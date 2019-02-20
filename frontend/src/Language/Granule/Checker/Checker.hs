{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Granule.Checker.Checker where

import Control.Monad (unless)
import Control.Monad.State.Strict
import Control.Monad.Except (throwError)
import Data.List (genericLength, intercalate)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty (toList)
import Data.Maybe
import qualified Data.Text as T

import Language.Granule.Checker.Constraints.Compile
import Language.Granule.Checker.Coeffects
import Language.Granule.Checker.Constraints
import Language.Granule.Checker.Kinds
import Language.Granule.Checker.Exhaustivity
import Language.Granule.Checker.Monad
import Language.Granule.Checker.NameClash
import Language.Granule.Checker.Patterns
import Language.Granule.Checker.Predicates
import qualified Language.Granule.Checker.Primitives as Primitives
import Language.Granule.Checker.Simplifier
import Language.Granule.Checker.Substitutions
import Language.Granule.Checker.Types
import Language.Granule.Checker.Variables
import Language.Granule.Context

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Helpers (freeVars)
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type

import Language.Granule.Utils

--import Debug.Trace

-- Checking (top-level)
check :: (?globals :: Globals)
  => AST () ()
  -> IO (Either (NonEmpty CheckerError) (AST () Type))
check ast@(AST dataDecls defs) = evalChecker initState $ do
    _         <- checkNameClashes ast
    _         <- runAll checkTyCon dataDecls
    dataDecls <- runAll checkDataCons dataDecls
    _         <- runAll kindCheckDef defs
    defs      <- runAll (checkDef defCtxt) defs
    pure $ AST dataDecls defs
  where
    defCtxt = map (\(Def _ name _ tys) -> (name, tys)) defs


checkTyCon :: DataDecl -> Checker ()
checkTyCon (DataDecl sp name tyVars kindAnn ds)
  = lookup name <$> gets typeConstructors >>= \case
    Just _ -> throw TypeConstructorNameClash{ errLoc = sp, errId = name }
    Nothing -> modify' $ \st ->
      st{ typeConstructors = (name, (tyConKind, cardin)) : typeConstructors st }
  where
    cardin = (Just . genericLength) ds -- the number of data constructors
    tyConKind = mkKind (map snd tyVars)
    mkKind [] = case kindAnn of Just k -> k; Nothing -> KType -- default to `Type`
    mkKind (v:vs) = KFun v (mkKind vs)

checkDataCons :: (?globals :: Globals) => DataDecl -> Checker DataDecl
checkDataCons (DataDecl sp name tyVars k dataConstrs) = do
    st <- get
    let kind = case lookup name (typeConstructors st) of
                Just (kind,_) -> kind
                Nothing -> error $ "Internal error. Trying to lookup data constructor " <> pretty name
    modify' $ \st -> st { tyVarContext = [(v, (k, ForallQ)) | (v, k) <- tyVars] }
    dataConstrs <- mapM (checkDataCon name kind tyVars) dataConstrs
    pure (DataDecl sp name tyVars k dataConstrs)

checkDataCon :: (?globals :: Globals)
  => Id -- ^ The type constructor and associated type to check against
  -> Kind -- ^ The kind of the type constructor
  -> Ctxt Kind -- ^ The type variables
  -> DataConstr -- ^ The data constructor to check
  -> Checker DataConstr -- ^ Return @Just ()@ on success, @Nothing@ on failure
checkDataCon
  tName
  kind
  tyVarsT
  d@(DataConstrIndexed sp dName tySch@(Forall _ tyVarsD constraints ty)) = do
    case map fst $ intersectCtxts tyVarsT tyVarsD of
      [] -> do -- no clashes

        -- Only relevant type variables get included
        let tyVars = relevantSubCtxt (freeVars ty) (tyVarsT <> tyVarsD)
        let tyVars_justD = relevantSubCtxt (freeVars ty) tyVarsD

        -- Add the type variables from the data constructor into the environment
        modify $ \st -> st { tyVarContext = [(v, (k, ForallQ)) | (v, k) <- tyVars_justD] ++ tyVarContext st }
        tySchKind <- inferKindOfType' sp tyVars ty

        case tySchKind of
          KType -> do
            check ty
            st <- get
            case extend (dataConstructors st) dName (Forall sp tyVars constraints ty) of
              Just ds -> do
                put st { dataConstructors = ds }
              Nothing -> throw DataConstructorNameClashError{ errLoc = sp, errId = dName }
          KPromote (TyCon k) | internalId k == "Protocol" -> do
            check ty
            st <- get
            case extend (dataConstructors st) dName (Forall sp tyVars constraints ty) of
              Just ds -> put st { dataConstructors = ds }
              Nothing -> throw DataConstructorNameClashError{ errLoc = sp, errId = dName }

          _ -> throw KindMismatch{ errLoc = sp, kExpected = KType, kActual = kind }
      (v:vs) -> throwError $ fmap (DataConstructorTypeVariableNameClash sp dName tName) (v:|vs)
    pure d
  where
    check (TyCon tC)
      | tC == tName = return ()
      | otherwise = throw DataConstructorReturnTypeError
          { errLoc = sp, idExpected = tName, idActual = tC }
    check (FunTy arg res) = check res
    check (TyApp fun arg) = check fun
    check t = throw MalformedDataConstructorType{ errLoc = sp, errTy = t }

checkDataCon tName kind tyVars d@DataConstrNonIndexed{}
  = checkDataCon tName kind tyVars
    $ nonIndexedToIndexedDataConstr tName tyVars d

checkDef :: (?globals :: Globals)
         => Ctxt TypeScheme  -- context of top-level definitions
         -> Def () ()        -- definition
         -> Checker (Def () Type)
checkDef defCtxt (Def s defName equations tys@(Forall _ foralls constraints ty)) = do

    -- Clean up knowledge shared between equations of a definition
    modify (\st -> st { guardPredicates = [[]]
                      , patternConsumption = initialisePatternConsumptions equations } )

    elaboratedEquations :: [Equation () Type] <- forM equations $ \equation -> do -- Checker [Maybe (Equation () Type)]
        -- Erase the solver predicate between equations
        modify' $ \st -> st
            { predicateStack = []
            , tyVarContext = []
            , kVarContext = []
            , guardContexts = []
            }
        elaboratedEq <- checkEquation defCtxt defName equation tys

        -- Solve the generated constraints
        checkerState <- get
        debugM "tyVarContext" (pretty $ tyVarContext checkerState)
        let predStack = Conj $ predicateStack checkerState
        debugM "Solver predicate" $ pretty predStack
        solveConstraints predStack (getSpan equation) defName
        pure elaboratedEq

    checkGuardsForImpossibility s defName
    checkGuardsForExhaustivity s defName ty equations
    pure $ Def s defName elaboratedEquations tys

checkEquation :: (?globals :: Globals) =>
     Ctxt TypeScheme -- context of top-level definitions
  -> Id              -- Name of the definition
  -> Equation () ()  -- Equation
  -> TypeScheme      -- Type scheme
  -> Checker (Equation () Type)

checkEquation defCtxt _ (Equation s () pats expr) tys@(Forall _ foralls constraints ty) = do
  -- Check that the lhs doesn't introduce any duplicate binders
  duplicateBinderCheck s pats

  -- Freshen the type context
  modify (\st -> st { tyVarContext = map (\(n, c) -> (n, (c, ForallQ))) foralls})

  -- Create conjunct to capture the pattern constraints
  newConjunct

  mapM_ (\ty -> do
    pred <- compileTypeConstraintToConstraint s ty
    addPredicate pred) constraints

  -- Build the binding context for the branch pattern
  st <- get
  (patternGam, tau, localVars, subst, elaborated_pats, consumptions) <-
     ctxtFromTypedPatterns s ty pats (patternConsumption st)

  -- Update the consumption information
  modify (\st -> st { patternConsumption =
                         zipWith joinConsumption consumptions (patternConsumption st) } )

  -- Create conjunct to capture the body expression constraints
  newConjunct

  -- Specialise the return type by the pattern generated substitution
  tau' <- substitute subst tau

  -- Check the body
  (localGam, subst', elaboratedExpr) <-
       checkExpr defCtxt patternGam Positive True tau' expr

  case checkLinearity patternGam localGam of
    [] -> do
      -- Check that our consumption context approximations the binding
      ctxtApprox s localGam patternGam

      -- Conclude the implication
      concludeImplication s localVars

      -- Create elaborated equation
      subst'' <- combineSubstitutions s subst subst'
      let elab = Equation s ty elaborated_pats elaboratedExpr

      elab' <- substitute subst'' elab
      return elab'

    -- Anything that was bound in the pattern but not used up
    (p:ps) -> illLinearityMismatch s (p:|ps)


data Polarity = Positive | Negative deriving Show


flipPol :: Polarity -> Polarity
flipPol Positive = Negative
flipPol Negative = Positive

-- Type check an expression

--  `checkExpr defs gam t expr` computes `Just delta`
--  if the expression type checks to `t` in context `gam`:
--  where `delta` gives the post-computation context for expr
--  (which explains the exact coeffect demands)
--  or `Nothing` if the typing does not match.

checkExpr :: (?globals :: Globals)
          => Ctxt TypeScheme   -- context of top-level definitions
          -> Ctxt Assumption   -- local typing context
          -> Polarity         -- polarity of <= constraints
          -> Bool             -- whether we are top-level or not
          -> Type             -- type
          -> Expr () ()       -- expression
          -> Checker (Ctxt Assumption, Substitution, Expr () Type)

-- Checking of constants

checkExpr _ [] _ _ ty@(TyCon c) (Val s _ (NumInt n))   | internalId c == "Int" = do
    let elaborated = Val s ty (NumInt n)
    return ([], [], elaborated)

checkExpr _ [] _ _ ty@(TyCon c) (Val s _ (NumFloat n)) | internalId c == "Float" = do
    let elaborated = Val s ty (NumFloat n)
    return ([], [], elaborated)

checkExpr defs gam pol _ ty@(FunTy sig tau) (Val s _ (Abs _ p t e)) = do
  -- If an explicit signature on the lambda was given, then check
  -- it confirms with the type being checked here

  (tau', subst1) <- case t of
    Nothing -> return (tau, [])
    Just t' -> do
      (eqT, unifiedType, subst) <- equalTypes s sig t'
      unless eqT $ throw TypeError{ errLoc = s, tyExpected = sig, tyActual = t' }
      return (tau, subst)

  (bindings, _, subst, elaboratedP, _) <- ctxtFromTypedPattern s sig p NotFull
  debugM "binding from lam" $ pretty bindings

  pIrrefutable <- isIrrefutable s sig p
  if pIrrefutable then do
    -- Check the body in the extended context
    (gam', subst2, elaboratedE) <- checkExpr defs (bindings <> gam) pol False tau' e
    -- Check linearity of locally bound variables
    case checkLinearity bindings gam' of
       [] -> do
          subst <- combineSubstitutions s subst1 subst2

          -- Locally we should have this property (as we are under a binder)
          ctxtEquals s (gam' `intersectCtxts` bindings) bindings

          let elaborated = Val s ty (Abs ty elaboratedP t elaboratedE)
          return (gam' `subtractCtxt` bindings, subst, elaborated)

       (p:ps) -> illLinearityMismatch s (p:|ps)
  else throw RefutablePatternError{ errLoc = s, errPat = p }




-- Application special case for built-in 'scale'
-- TODO: needs more thought
{- checkExpr defs gam pol topLevel tau
          (App s _ (App _ _ (Val _ _ (Var _ v)) (Val _ _ (NumFloat _ x))) e) | internalId v == "scale" = do
    equalTypes s (TyCon $ mkId "Float") tau
    checkExpr defs gam pol topLevel (Box (CFloat (toRational x)) (TyCon $ mkId "Float")) e
-}

-- Application checking
checkExpr defs gam pol topLevel tau (App s _ e1 e2) = do

    (argTy, gam2, elaboratedR) <- synthExpr defs gam pol e2
    (gam1, subst, elaboratedL) <- checkExpr defs gam (flipPol pol) topLevel (FunTy argTy tau) e1
    gam <- ctxtPlus s gam1 gam2

    let elaborated = App s tau elaboratedL elaboratedR
    return (gam, subst, elaborated)

{-

[G] |- e : t
 ---------------------
[G]*r |- [e] : []_r t

-}

-- Promotion
checkExpr defs gam pol _ ty@(Box demand tau) (Val s _ (Promote _ e)) = do
    let vars = freeVars e -- map fst gam
    gamF    <- discToFreshVarsIn s vars gam demand
    (gam', subst, elaboratedE) <- checkExpr defs gamF pol False tau e

    -- Causes a promotion of any typing assumptions that came from variable
    -- inside a guard from an enclosing case that have kind Level
    -- This prevents control-flow attacks and is a special case for Level
    -- (the guard contexts come from a special context in the solver)
    guardGam <- allGuardContexts
    guardGam' <- filterM isLevelKinded guardGam
    let gam'' = multAll (vars <> map fst guardGam') demand (gam' <> guardGam')

    let elaborated = Val s ty (Promote tau elaboratedE)
    return (gam'', subst, elaborated)
  where
    -- Calculate whether a type assumption is level kinded
    isLevelKinded (_, as) = do
        ty <- inferCoeffectTypeAssumption s as
        return $ case ty of
          Just (TyCon (internalId -> "Level"))
            -> True
          Just (TyApp (TyCon (internalId -> "Interval"))
                      (TyCon (internalId -> "Level")))
            -> True
          _ -> False


-- Dependent pattern-matching case (only at the top level)
checkExpr defs gam pol True tau (Case s _ guardExpr cases) = do
  -- Synthesise the type of the guardExpr
  (guardTy, guardGam, elaboratedGuard) <- synthExpr defs gam pol guardExpr
  pushGuardContext guardGam

  newCaseFrame

  -- Check each of the branches
  branchCtxtsAndSubst <-
    forM cases $ \(pat_i, e_i) -> do
      -- Build the binding context for the branch pattern
      newConjunct
      (patternGam, eVars, subst, elaborated_pat_i, _) <- ctxtFromTypedPattern s guardTy pat_i NotFull

      -- Checking the case body
      newConjunct
      -- Specialise the return type and the incoming environment using the
      -- pattern-match-generated type substitution
      tau' <- substitute subst tau
      (specialisedGam, unspecialisedGam) <- substCtxt subst gam

      let checkGam = patternGam <> specialisedGam <> unspecialisedGam
      (localGam, subst', elaborated_i) <- checkExpr defs checkGam pol False tau' e_i

      -- We could do this, but it seems redundant.
      -- localGam' <- ctxtPlus s guardGam localGam
      -- ctxtApprox s localGam' checkGam

      -- Check linear use in anything Linear
      gamSoFar <- ctxtPlus s guardGam localGam
      case checkLinearity patternGam gamSoFar of
        -- Return the resulting computed context, without any of
        -- the variable bound in the pattern of this branch
        [] -> do


           debugM "Specialised gam" (pretty specialisedGam)
           debugM "Unspecialised gam" (pretty unspecialisedGam)

           debugM "pattern gam" (pretty patternGam)
           debugM "local gam" (pretty localGam)

           st <- get
           debugM "pred so far" (pretty (predicateStack st))

           -- The resulting context has the shared part removed
           -- 28/02/2018 - We used to have this
           --let branchCtxt = (localGam `subtractCtxt` guardGam) `subtractCtxt` specialisedGam
           -- But we want promotion to invovlve the guard to avoid leaks
           let branchCtxt = (localGam `subtractCtxt` specialisedGam) `subtractCtxt` patternGam

           branchCtxt' <- ctxtPlus s branchCtxt  (justLinear $ (gam `intersectCtxts` specialisedGam) `intersectCtxts` localGam)

           -- Probably don't want to remove specialised things in this way- we want to
           -- invert the substitution and put these things into the context

           -- Check local binding use
           ctxtApprox s (localGam `intersectCtxts` patternGam) patternGam


           -- Check "global" (to the definition) binding use
           consumedGam <- ctxtPlus s guardGam localGam
           debugM "** gam = " (pretty gam)
           debugM "** c sub p = " (pretty (consumedGam `subtractCtxt` patternGam))

           ctxtApprox s (consumedGam `subtractCtxt` patternGam) gam

           -- Conclude the implication
           concludeImplication (getSpan pat_i) eVars

           return (branchCtxt', subst', (elaborated_pat_i, elaborated_i))

        -- Anything that was bound in the pattern but not used correctly
        p:ps -> illLinearityMismatch s (p:|ps)

  st <- get
  debugM "pred so after branches" (pretty (predicateStack st))

  -- Pop from stacks related to case
  _ <- popGuardContext
  _ <- popCaseFrame

  -- Find the upper-bound contexts
  let (branchCtxts, substs, elaboratedCases) = unzip3 branchCtxtsAndSubst
  branchesGam <- fold1M (joinCtxts s) branchCtxts

  debugM "*** Branches from the case " (pretty branchCtxts)

  -- Contract the outgoing context of the guard and the branches (joined)
  g <- ctxtPlus s branchesGam guardGam
  debugM "--- Output context for case " (pretty g)

  st <- get
  debugM "pred at end of case" (pretty (predicateStack st))

  let elaborated = Case s tau elaboratedGuard elaboratedCases
  return (g, concat substs, elaborated)

-- All other expressions must be checked using synthesis
checkExpr defs gam pol topLevel tau e = do

  (tau', gam', elaboratedE) <- synthExpr defs gam pol e

  (tyEq, _, subst) <-
    case pol of
      Positive -> do
        debugM "+ Compare for equality " $ pretty tau' <> " = " <> pretty tau
        if topLevel
          -- If we are checking a top-level, then don't allow overapproximation
          then equalTypesWithPolarity (getSpan e) SndIsSpec tau' tau
          else lEqualTypesWithPolarity (getSpan e) SndIsSpec tau' tau

      -- i.e., this check is from a synth
      Negative -> do
        debugM "- Compare for equality " $ pretty tau <> " = " <> pretty tau'
        if topLevel
          -- If we are checking a top-level, then don't allow overapproximation
          then equalTypesWithPolarity (getSpan e) FstIsSpec tau' tau
          else lEqualTypesWithPolarity (getSpan e) FstIsSpec tau' tau

  if tyEq
    then return (gam', subst, elaboratedE)
    else do
      case pol of
        Positive -> throw TypeError{ errLoc = getSpan e, tyExpected = tau , tyActual = tau' }
        Negative -> throw TypeError{ errLoc = getSpan e, tyExpected = tau', tyActual =  tau }

-- | Synthesise the 'Type' of expressions.
-- See <https://en.wikipedia.org/w/index.php?title=Bidirectional_type_checking&redirect=no>
synthExpr :: (?globals :: Globals)
          => Ctxt TypeScheme   -- ^ Context of top-level definitions
          -> Ctxt Assumption   -- ^ Local typing context
          -> Polarity          -- ^ Polarity of subgrading
          -> Expr () ()        -- ^ Expression
          -> Checker (Type, Ctxt Assumption, Expr () Type)

-- Literals can have their type easily synthesised
synthExpr _ _ _ (Val s _ (NumInt n))  = do
  let t = TyCon $ mkId "Int"
  return (t, [], Val s t (NumInt n))

synthExpr _ _ _ (Val s _ (NumFloat n)) = do
  let t = TyCon $ mkId "Float"
  return (t, [], Val s t (NumFloat n))

synthExpr _ _ _ (Val s _ (CharLiteral c)) = do
  let t = TyCon $ mkId "Char"
  return (t, [], Val s t (CharLiteral c))

synthExpr _ _ _ (Val s _ (StringLiteral c)) = do
  let t = TyCon $ mkId "String"
  return (t, [], Val s t (StringLiteral c))

-- Secret syntactic weakening
synthExpr defs gam pol
  (App s _ (Val _ _ (Var _ (sourceId -> "weak__"))) v@(Val _ _ (Var _ x))) = do

  (t, _, elabE) <- synthExpr defs gam pol v

  return (t, [(x, Discharged t (CZero (TyCon $ mkId "Level")))], elabE)

-- Constructors
synthExpr _ gam _ (Val s _ (Constr _ c [])) = do
  -- Should be provided in the type checkers environment
  st <- get
  case lookup c (dataConstructors st) of
    Just tySch -> do
      -- Freshen the constructor
      -- (discarding any fresh type variables, info not needed here)
      (ty, _, []) <- freshPolymorphicInstance InstanceQ False tySch
      -- TODO: allow data type constructors to have constraints

      let elaborated = Val s ty (Constr ty c [])
      return (ty, [], elaborated)

    Nothing -> throw UnboundDataConstructor{ errLoc = s, errId = c }

-- Case synthesis
synthExpr defs gam pol (Case s _ guardExpr cases) = do
  -- Synthesise the type of the guardExpr
  (ty, guardGam, elaboratedGuard) <- synthExpr defs gam pol guardExpr
  -- then synthesise the types of the branches

  newCaseFrame

  branchTysAndCtxts <-
    forM cases $ \(pati, ei) -> do
      -- Build the binding context for the branch pattern
      newConjunct
      (patternGam, eVars, _, elaborated_pat_i, _) <- ctxtFromTypedPattern s ty pati NotFull
      newConjunct
      ---
      (tyCase, localGam, elaborated_i) <- synthExpr defs (patternGam <> gam) pol ei
      concludeImplication (getSpan pati) eVars

      ctxtEquals s (localGam `intersectCtxts` patternGam) patternGam

      -- Check linear use in this branch
      gamSoFar <- ctxtPlus s guardGam localGam
      case checkLinearity patternGam gamSoFar of
         -- Return the resulting computed context, without any of
         -- the variable bound in the pattern of this branch
         [] -> return (tyCase, localGam `subtractCtxt` patternGam,
                        (elaborated_pat_i, elaborated_i))
         p:ps -> illLinearityMismatch s (p:|ps)

  popCaseFrame

  let (branchTys, branchCtxts, elaboratedCases) = unzip3 branchTysAndCtxts
  let branchTysAndSpans = zip branchTys (map (getSpan . snd) cases)
  -- Finds the upper-bound return type between all branches
  branchType <- foldM (\ty2 (ty1, sp) -> joinTypes sp ty1 ty2)
                   (head branchTys)
                   (tail branchTysAndSpans)

  -- Find the upper-bound type on the return contexts
  branchesGam <- fold1M (joinCtxts s) branchCtxts

  -- Contract the outgoing context of the guard and the branches (joined)
  gamNew <- ctxtPlus s branchesGam guardGam

  debugM "*** synth branchesGam" (pretty branchesGam)

  let elaborated = Case s branchType elaboratedGuard elaboratedCases
  return (branchType, gamNew, elaborated)

-- Diamond cut
synthExpr defs gam pol (LetDiamond s _ p optionalTySig e1 e2) = do
  -- TODO: refactor this once we get a proper mechanism for
  -- specifying effect over-approximations and type aliases

  (sig, gam1, elaborated1) <- synthExpr defs gam pol e1

  (ef1, ty1) <-
          case sig of
            Diamond ["IO"] ty1 -> return ([], ty1)
            Diamond ["Session"] ty1 -> return ([], ty1)
            Diamond ef1 ty1 -> return (ef1, ty1)
            t -> throw ExpectedEffectType{ errLoc = s, errTy = t }

  -- Type body of the let...
  -- ...in the context of the binders from the pattern
  (binders, _, _, elaboratedP, _)  <- ctxtFromTypedPattern s ty1 p NotFull
  pIrrefutable <- isIrrefutable s ty1 p
  if not pIrrefutable
  then throw RefutablePatternError{ errLoc = s, errPat = p }
  else do
     (tau, gam2, elaborated2) <- synthExpr defs (binders <> gam) pol e2
     (ef2, ty2) <-
           case tau of
             Diamond ["IO"] ty2 -> return ([], ty2)
             Diamond ["Session"] ty2 -> return ([], ty2)
             Diamond ef2 ty2 -> return (ef2, ty2)
             t -> throw ExpectedEffectType{ errLoc = s, errTy = t }

     optionalSigEquality s optionalTySig ty1

     -- Check that usage matches the binding grades/linearity
     -- (performs the linearity check)
     ctxtEquals s (gam2 `intersectCtxts` binders) binders

     gamNew <- ctxtPlus s (gam2 `subtractCtxt` binders) gam1

     let t = Diamond (ef1 <> ef2) ty2
     let elaborated = LetDiamond s t elaboratedP optionalTySig elaborated1 elaborated2
     return (t, gamNew, elaborated)

-- Variables
synthExpr defs gam _ (Val s _ (Var _ x)) =
   -- Try the local context
   case lookup x gam of
     Nothing ->
       -- Try definitions in scope
       case lookup x (defs <> Primitives.builtins) of
         Just tyScheme  -> do
           (ty', _, constraints) <- freshPolymorphicInstance InstanceQ False tyScheme -- discard list of fresh type variables

           mapM_ (\ty -> do
             pred <- compileTypeConstraintToConstraint s ty
             addPredicate pred) constraints

           let elaborated = Val s ty' (Var ty' x)
           return (ty', [], elaborated)

         -- Couldn't find it
         Nothing -> throw UnboundVariableError{ errLoc = s, errId = x }

     -- In the local context
     Just (Linear ty)       -> do
       let elaborated = Val s ty (Var ty x)
       return (ty, [(x, Linear ty)], elaborated)

     Just (Discharged ty c) -> do
       k <- inferCoeffectType s c
       let elaborated = Val s ty (Var ty x)
       return (ty, [(x, Discharged ty (COne k))], elaborated)

-- Specialised application for scale
{-
TODO: needs thought
synthExpr defs gam pol
      (App _ _ (Val _ _ (Var _ v)) (Val _ _ (NumFloat _ r))) | internalId v == "scale" = do
  let float = TyCon $ mkId "Float"
  return (FunTy (Box (CFloat (toRational r)) float) float, [])
-}

-- Application
synthExpr defs gam pol (App s _ e e') = do
    (fTy, gam1, elaboratedL) <- synthExpr defs gam pol e
    case fTy of
      -- Got a function type for the left-hand side of application
      (FunTy sig tau) -> do
         (gam2, subst, elaboratedR) <- checkExpr defs gam (flipPol pol) False sig e'
         gamNew <- ctxtPlus s gam1 gam2
         tau    <- substitute subst tau

         let elaborated = App s tau elaboratedL elaboratedR
         return (tau, gamNew, elaborated)

      -- Not a function type
      t -> throw LhsOfApplicationNotAFunction{ errLoc = s, errTy = t }

{- Promotion

[G] |- e : t
 ---------------------
[G]*r |- [e] : []_r t

-}

synthExpr defs gam pol (Val s _ (Promote _ e)) = do
   debugM "Synthing a promotion of " $ pretty e

   -- Create a fresh kind variable for this coeffect
   vark <- freshIdentifierBase $ "kprom_" <> [head (pretty e)]
   -- remember this new kind variable in the kind environment
   modify (\st -> st { kVarContext = (mkId vark, KCoeffect) : kVarContext st })

   -- Create a fresh coeffect variable for the coeffect of the promoted expression
   var <- freshTyVarInContext (mkId $ "prom_[" <> pretty e <> "]") (KPromote $ TyVar $ mkId vark)

   gamF <- discToFreshVarsIn s (freeVars e) gam (CVar var)

   (t, gam', elaboratedE) <- synthExpr defs gamF pol e

   let finalTy = Box (CVar var) t
   let elaborated = Val s finalTy (Promote t elaboratedE)
   return (finalTy, multAll (freeVars e) (CVar var) gam', elaborated)


-- BinOp
synthExpr defs gam pol (Binop s _ op e1 e2) = do
    (t1, gam1, elaboratedL) <- synthExpr defs gam pol e1
    (t2, gam2, elaboratedR) <- synthExpr defs gam pol e2
    -- Look through the list of operators (of which there might be
    -- multiple matching operators)
    returnType <-
      selectFirstByType t1 t2
      . NonEmpty.toList
      . Primitives.binaryOperators
      $ op
    gamOut <- ctxtPlus s gam1 gam2
    let elaborated = Binop s returnType op elaboratedL elaboratedR
    return (returnType, gamOut, elaborated)

  where
    -- No matching type were found (meaning there is a type error)
    selectFirstByType t1 t2 [] = throw FailedOperatorResolution
        { errLoc = s, errOp = op, errTy = t1 .-> t2 .-> var "..." }

    selectFirstByType t1 t2 ((FunTy opt1 (FunTy opt2 resultTy)):ops) = do
      -- Attempt to use this typing
      (result, local) <- peekChecker $ do
         (eq1, _, _) <- equalTypes s t1 opt1
         (eq2, _, _) <- equalTypes s t2 opt2
         return (eq1 && eq2)
      -- If successful then return this local computation
      case result of
        Right True -> local >> return resultTy
        _         -> selectFirstByType t1 t2 ops

    selectFirstByType t1 t2 (_:ops) = selectFirstByType t1 t2 ops


-- Abstraction, can only synthesise the types of
-- lambda in Church style (explicit type)
synthExpr defs gam pol (Val s _ (Abs _ p (Just sig) e)) = do
  (bindings, _, subst, elaboratedP, _) <- ctxtFromTypedPattern s sig p NotFull

  pIrrefutable <- isIrrefutable s sig p
  if pIrrefutable then do
     (tau, gam'', elaboratedE) <- synthExpr defs (bindings <> gam) pol e

     -- Locally we should have this property (as we are under a binder)
     ctxtEquals s (gam'' `intersectCtxts` bindings) bindings

     let finalTy = FunTy sig tau
     let elaborated = Val s finalTy (Abs finalTy elaboratedP (Just sig) elaboratedE)

     return (finalTy, gam'' `subtractCtxt` bindings, elaborated)
  else throw RefutablePatternError{ errLoc = s, errPat = p }

-- Abstraction, can only synthesise the types of
-- lambda in Church style (explicit type)
synthExpr defs gam pol (Val s _ (Abs _ p Nothing e)) = do

  tyVar <- freshTyVarInContext (mkId "t") KType
  let sig = (TyVar tyVar)

  (bindings, _, subst, elaboratedP, _) <- ctxtFromTypedPattern s sig p NotFull

  pIrrefutable <- isIrrefutable s sig p
  if pIrrefutable then do
     (tau, gam'', elaboratedE) <- synthExpr defs (bindings <> gam) pol e

     -- Locally we should have this property (as we are under a binder)
     ctxtEquals s (gam'' `intersectCtxts` bindings) bindings

     let finalTy = FunTy sig tau
     let elaborated = Val s finalTy (Abs finalTy elaboratedP (Just sig) elaboratedE)

     return (finalTy, gam'' `subtractCtxt` bindings, elaborated)
  else throw RefutablePatternError{ errLoc = s, errPat = p }

synthExpr _ _ _ e =
  throw NeedTypeSignature{ errLoc = getSpan e, errExpr = e }

-- Check an optional type signature for equality against a type
optionalSigEquality :: (?globals :: Globals) => Span -> Maybe Type -> Type -> Checker ()
optionalSigEquality _ Nothing _ = pure ()
optionalSigEquality s (Just t) t' = do
  _ <- equalTypes s t' t
  pure ()

solveConstraints :: (?globals :: Globals) => Pred -> Span -> Id -> Checker ()
solveConstraints predicate s name = do

  -- Get the coeffect kind context and constraints
  checkerState <- get
  let ctxtCk  = tyVarContext checkerState
  let ctxtCkVar = kVarContext checkerState
  coeffectVars <- justCoeffectTypesConverted s ctxtCk
  coeffectKVars <- justCoeffectTypesConvertedVars s ctxtCkVar

  result <- liftIO $ provePredicate predicate coeffectVars coeffectKVars

  case result of
    QED -> return ()
    NotValid msg -> do
      msg' <- rewriteMessage msg
      simpPred <- simplifyPred predicate
      if msg' == "is Falsifiable\n"
        then throw SolverErrorFalsifiableTheorem
          { errLoc = s, errDefId = name, errPred = simpPred }
        else throw SolverErrorCounterExample
          { errLoc = s, errDefId = name, errPred = simpPred }
    NotValidTrivial unsats ->
       mapM_ (\c -> throw GradingError{ errLoc = getSpan c, errConstraint = Neg c }) unsats
    Timeout ->
       throw SolverTimeout{ errLoc = s, errSolverTimeoutMillis = solverTimeoutMillis }
    OtherSolverError msg -> throw SolverError{ errLoc = s, errMsg = msg }
    SolverProofError msg -> error msg

-- Rewrite an error message coming from the solver
rewriteMessage :: String -> Checker String
rewriteMessage msg = do
    st <- get
    let tyVars = tyVarContext st
    let msgLines = T.lines $ T.pack msg
    -- Rewrite internal names to source names
    let msgLines' = map (\line -> foldl convertLine line tyVars) msgLines

    return $ T.unpack (T.unlines msgLines')
  where
    convertLine line (v, (k, _)) =
        -- Try to replace line variables in the line
       let line' = T.replace (T.pack (internalId v)) (T.pack (sourceId v)) line
       -- If this succeeds we might want to do some other replacements
           line'' =
             if line /= line' then
               case k of
                 KPromote (TyCon (internalId -> "Level")) ->
                    T.replace (T.pack $ show privateRepresentation) (T.pack "Private")
                      (T.replace (T.pack $ show publicRepresentation) (T.pack "Public")
                       (T.replace (T.pack "Integer") (T.pack "Level") line'))
                 _ -> line'
             else line'
       in line''

justCoeffectTypesConverted :: (?globals::Globals)
  => Span -> [(a, (Kind, b))] -> Checker [(a, (Type, b))]
justCoeffectTypesConverted s xs = mapM convert xs >>= (return . catMaybes)
  where
    convert (var, (KPromote t, q)) = do
      k <- inferKindOfType s t
      case k of
        KCoeffect -> return $ Just (var, (t, q))
        _         -> return Nothing
    convert (var, (KVar v, q)) = do
      k <- inferKindOfType s (TyVar v)
      case k of
        KCoeffect -> return $ Just (var, (TyVar v, q))
        _         -> return Nothing
    convert _ = return Nothing
justCoeffectTypesConvertedVars :: (?globals::Globals)
  => Span -> [(Id, Kind)] -> Checker (Ctxt Type)
justCoeffectTypesConvertedVars s env = do
  let implicitUniversalMadeExplicit = map (\(var, k) -> (var, (k, ForallQ))) env
  env' <- justCoeffectTypesConverted s implicitUniversalMadeExplicit
  return $ stripQuantifiers env'

-- | `ctxtEquals ctxt1 ctxt2` checks if two contexts are equal
--   and the typical pattern is that `ctxt2` represents a specification
--   (i.e. input to checking) and `ctxt1` represents actually usage
ctxtApprox :: (?globals :: Globals) =>
    Span -> Ctxt Assumption -> Ctxt Assumption -> Checker ()
ctxtApprox s ctxt1 ctxt2 = do
  -- intersection contains those ids from ctxt1 which appears in ctxt2
  intersection <-
    -- For everything in the right context
    -- (which should come as an input to checking)
    forM ctxt2 $ \(id, ass2) ->
      -- See if it appears in the left context...
      case lookup id ctxt1 of
        -- ... if so equate
        Just ass1 -> do
          relateByAssumption s ApproximatedBy (id, ass1) (id, ass2)
          return id
        -- ... if not check to see if the missing variable is linear
        Nothing   ->
           case ass2 of
             -- Linear gets instantly reported
             Linear t -> illLinearityMismatch s . pure $ LinearNotUsed id
             -- Else, this could be due to weakening so see if this is allowed
             Discharged t c -> do
               kind <- inferCoeffectType s c
               relateByAssumption s ApproximatedBy (id, Discharged t (CZero kind)) (id, ass2)
               return id
  -- Last we sanity check, if there is anything in ctxt1 that is not in ctxt2
  -- then we have an issue!
  forM_ ctxt1 $ \(id, ass1) ->
    if (id `elem` intersection)
      then return ()
      else throw UnboundVariableError{ errLoc = s, errId = id }


-- | `ctxtEquals ctxt1 ctxt2` checks if two contexts are equal
--   and the typical pattern is that `ctxt2` represents a specification
--   (i.e. input to checking) and `ctxt1` represents actually usage
ctxtEquals :: (?globals :: Globals) =>
    Span -> Ctxt Assumption -> Ctxt Assumption -> Checker ()
ctxtEquals s ctxt1 ctxt2 = do
  -- intersection contains those ids from ctxt1 which appears in ctxt2
  intersection <-
    -- For everything in the right context
    -- (which should come as an input to checking)
    forM ctxt2 $ \(id, ass2) ->
      -- See if it appears in the left context...
      case lookup id ctxt1 of
        -- ... if so equate
        Just ass1 -> do
          relateByAssumption s Eq (id, ass1) (id, ass2)
          return id
        -- ... if not check to see if the missing variable is linear
        Nothing   ->
           case ass2 of
             -- Linear gets instantly reported
             Linear t -> illLinearityMismatch s . pure $ LinearNotUsed id
             -- Else, this could be due to weakening so see if this is allowed
             Discharged t c -> do
               kind <- inferCoeffectType s c
               relateByAssumption s Eq (id, Discharged t (CZero kind)) (id, ass2)
               return id
  -- Last we sanity check, if there is anything in ctxt1 that is not in ctxt2
  -- then we have an issue!
  forM_ ctxt1 $ \(id, ass1) ->
    if (id `elem` intersection)
      then return ()
      else throw UnboundVariableError{ errLoc = s, errId = id }

{- | Take the least-upper bound of two contexts.
     If one context contains a linear variable that is not present in
    the other, then the resulting context will not have this linear variable -}
joinCtxts :: (?globals :: Globals) => Span -> Ctxt Assumption -> Ctxt Assumption
  -> Checker (Ctxt Assumption)
joinCtxts s ctxt1 ctxt2 = do
    -- All the type assumptions from ctxt1 whose variables appear in ctxt2
    -- and weaken all others
    ctxt  <- intersectCtxtsWithWeaken s ctxt1 ctxt2
    -- All the type assumptions from ctxt2 whose variables appear in ctxt1
    -- and weaken all others
    ctxt' <- intersectCtxtsWithWeaken s ctxt2 ctxt1

    -- Make an context with fresh coeffect variables for all
    -- the variables which are in both ctxt1 and ctxt2...
    varCtxt <- freshVarsIn s (map fst ctxt) ctxt

    -- ... and make these fresh coeffects the upper-bound of the coeffects
    -- in ctxt and ctxt'
    zipWithM_ (relateByAssumption s ApproximatedBy) ctxt varCtxt
    zipWithM_ (relateByAssumption s ApproximatedBy) ctxt' varCtxt
    -- Return the common upper-bound context of ctxt1 and ctxt2
    return varCtxt

{- |  intersect contexts and weaken anything not appear in both
        relative to the left context (this is not commutative) -}
intersectCtxtsWithWeaken
  :: (?globals :: Globals)
  => Span
  -> Ctxt Assumption
  -> Ctxt Assumption
  -> Checker (Ctxt Assumption)
intersectCtxtsWithWeaken s a b = do
   let intersected = intersectCtxts a b
   -- All the things that were not shared
   let remaining   = b `subtractCtxt` intersected
   let leftRemaining = a `subtractCtxt` intersected
   weakenedRemaining <- mapM weaken remaining
   let newCtxt = intersected <> filter isNonLinearAssumption (weakenedRemaining <> leftRemaining)
   return . normaliseCtxt $ newCtxt
  where
   isNonLinearAssumption :: (Id, Assumption) -> Bool
   isNonLinearAssumption (_, Discharged _ _) = True
   isNonLinearAssumption _                   = False

   weaken :: (Id, Assumption) -> Checker (Id, Assumption)
   weaken (var, Linear t) =
       return (var, Linear t)
   weaken (var, Discharged t c) = do
       kind <- inferCoeffectType s c
       return (var, Discharged t (CZero kind))

{- | Given an input context and output context, check the usage of
     variables in the output, returning a list of usage mismatch
     information if, e.g., a variable is bound linearly in the input but is not
     used in the output, or is discharged in the output -}
checkLinearity :: Ctxt Assumption -> Ctxt Assumption -> [LinearityMismatch]
checkLinearity [] _ = []
checkLinearity ((v, Linear _):inCtxt) outCtxt =
  case lookup v outCtxt of
    -- Good: linear variable was used
    Just Linear{} -> checkLinearity inCtxt outCtxt
    -- Bad: linear variable was discharged (boxed var but binder not unboxed)
    Just Discharged{} -> LinearUsedNonLinearly v : checkLinearity inCtxt outCtxt
    Nothing -> LinearNotUsed v : checkLinearity inCtxt outCtxt

checkLinearity ((_, Discharged{}):inCtxt) outCtxt =
  -- Discharged things can be discarded, so it doesn't matter what
  -- happens with them
  checkLinearity inCtxt outCtxt

relateByAssumption :: (?globals :: Globals)
  => Span
  -> (Span -> Coeffect -> Coeffect -> Type -> Constraint)
  -> (Id, Assumption)
  -> (Id, Assumption)
  -> Checker ()

-- Linear assumptions ignored
relateByAssumption _ _ (_, Linear _) (_, Linear _) = return ()

-- Discharged coeffect assumptions
relateByAssumption s rel (_, Discharged _ c1) (_, Discharged _ c2) = do
  kind <- mguCoeffectTypes s c1 c2
  addConstraint (rel s c1 c2 kind)

relateByAssumption s _ x y =
  throw UnifyGradedLinear{ errLoc = s, errGraded = fst x, errLinear = fst y }


-- Replace all top-level discharged coeffects with a variable
-- and derelict anything else
-- but add a var
discToFreshVarsIn :: (?globals :: Globals) => Span -> [Id] -> Ctxt Assumption -> Coeffect
  -> Checker (Ctxt Assumption)
discToFreshVarsIn s vars ctxt coeffect = mapM toFreshVar (relevantSubCtxt vars ctxt)
  where
    toFreshVar (var, Discharged t c) = do
      coeffTy <- mguCoeffectTypes s c coeffect

      -- Create a fresh variable
      cvar  <- freshTyVarInContext var (promoteTypeToKind coeffTy)
      -- Return the freshened var-type mapping
      return (var, Discharged t (CVar cvar))

    toFreshVar (var, Linear t) = do
      coeffTy <- inferCoeffectType s coeffect
      return (var, Discharged t (COne coeffTy))


-- `freshVarsIn names ctxt` creates a new context with
-- all the variables names in `ctxt` that appear in the list
-- `vars` and are discharged are
-- turned into discharged coeffect assumptions annotated
-- with a fresh coeffect variable (and all variables not in
-- `vars` get deleted).
-- e.g.
--  `freshVarsIn ["x", "y"] [("x", Discharged (2, Int),
--                           ("y", Linear Int),
--                           ("z", Discharged (3, Int)]
--  -> [("x", Discharged (c5 :: Nat, Int),
--      ("y", Linear Int)]
--
freshVarsIn :: (?globals :: Globals) => Span -> [Id] -> Ctxt Assumption
  -> Checker (Ctxt Assumption)
freshVarsIn s vars ctxt = mapM toFreshVar (relevantSubCtxt vars ctxt)
  where
    toFreshVar (var, Discharged t c) = do
      ctype <- inferCoeffectType s c
      -- Create a fresh variable
      freshName <- freshIdentifierBase (internalId var)
      let cvar = mkId freshName
      -- Update the coeffect kind context
      modify (\s -> s { tyVarContext = (cvar, (promoteTypeToKind ctype, InstanceQ)) : tyVarContext s })

      -- Return the freshened var-type mapping
      return (var, Discharged t (CVar cvar))

    toFreshVar (var, Linear t) = return (var, Linear t)


-- Combine two contexts
ctxtPlus :: (?globals :: Globals) => Span -> Ctxt Assumption -> Ctxt Assumption
  -> Checker (Ctxt Assumption)
ctxtPlus _ [] ctxt2 = return ctxt2
ctxtPlus s ((i, v) : ctxt1) ctxt2 = do
  ctxt' <- extCtxt s ctxt2 i v
  ctxtPlus s ctxt1 ctxt'

-- ExtCtxt the context
extCtxt :: (?globals :: Globals) => Span -> Ctxt Assumption -> Id -> Assumption
  -> Checker (Ctxt Assumption)
extCtxt s ctxt var (Linear t) = do

  case lookup var ctxt of
    Just (Linear t') ->
       if t == t'
        then throw LinearityError{ errLoc = s, linearityMismatch = LinearUsedMoreThanOnce var }
        else throw TypeVariableMismatch{ errLoc = s, errVar = var, errTy1 = t, errTy2 = t' }
    Just (Discharged t' c) ->
       if t == t'
         then do
           k <- inferCoeffectType s c
           return $ replace ctxt var (Discharged t (c `CPlus` COne k))
         else throw TypeVariableMismatch{ errLoc = s, errVar = var, errTy1 = t, errTy2 = t' }
    Nothing -> return $ (var, Linear t) : ctxt

extCtxt s ctxt var (Discharged t c) = do

  case lookup var ctxt of
    Just (Discharged t' c') ->
        if t == t'
        then return $ replace ctxt var (Discharged t' (c `CPlus` c'))
        else throw TypeVariableMismatch{ errLoc = s, errVar = var, errTy1 = t, errTy2 = t' }
    Just (Linear t') ->
        if t == t'
        then do
           k <- inferCoeffectType s c
           return $ replace ctxt var (Discharged t (c `CPlus` COne k))
        else throw TypeVariableMismatch{ errLoc = s, errVar = var, errTy1 = t, errTy2 = t' }
    Nothing -> return $ (var, Discharged t c) : ctxt

-- Helper, foldM on a list with at least one element
fold1M :: Monad m => (a -> a -> m a) -> [a] -> m a
fold1M _ []     = error "Must have at least one case"
fold1M f (x:xs) = foldM f x xs

justLinear :: [(a, Assumption)] -> [(a, Assumption)]
justLinear [] = []
justLinear ((x, Linear t) : xs) = (x, Linear t) : justLinear xs
justLinear ((x, _) : xs) = justLinear xs

checkGuardsForExhaustivity :: (?globals :: Globals)
  => Span -> Id -> Type -> [Equation () ()] -> Checker ()
checkGuardsForExhaustivity s name ty eqs = do
  debugM "Guard exhaustivity" "todo"
  return ()

checkGuardsForImpossibility :: (?globals :: Globals) => Span -> Id -> Checker ()
checkGuardsForImpossibility s name = do
  -- Get top of guard predicate stack
  st <- get
  let ps = head $ guardPredicates st

  -- Convert all universal variables to existential
  let tyVarContextExistential =
         mapMaybe (\(v, (k, q)) ->
                       case q of
                         BoundQ -> Nothing
                         _      -> Just (v, (k, InstanceQ))) (tyVarContext st)
  tyVars <- justCoeffectTypesConverted s tyVarContextExistential
  kVars <- justCoeffectTypesConvertedVars s (kVarContext st)

  -- For each guard predicate
  forM_ ps $ \((ctxt, p), s) -> do

    p <- simplifyPred p

    -- Existentially quantify those variables occuring in the pattern in scope
    let thm = foldr (uncurry Exists) p ctxt

    -- Try to prove the theorem
    result <- liftIO $ provePredicate thm tyVars kVars

    let msgHead = "Pattern guard for equation of `" <> pretty name <> "`"

    case result of
      QED -> return ()

      -- Various kinds of error
      -- TODO make errors better
      NotValid msg -> throw PatternUnreachable
        { errLoc = s
        , errMsg = msgHead <> " is impossible. Its condition " <> msg
        }
      NotValidTrivial unsats -> throw PatternUnreachable
        { errLoc = s
        , errMsg
            = msgHead <> " is impossible.\n\t"
            <> intercalate "\n\t" (map (pretty . Neg) unsats)
        }
      Timeout -> throw PatternUnreachable
        { errLoc = s
        , errMsg
            = "While checking plausibility of pattern guard for equation "
            <> pretty name <> "the solver timed out with limit of " <>
            show solverTimeoutMillis <>
            " ms. You may want to increase the timeout (see --help)."
        }

      OtherSolverError msg -> throw PatternUnreachable
        { errLoc = s
        , errMsg = msg
        }

      SolverProofError msg -> error msg
