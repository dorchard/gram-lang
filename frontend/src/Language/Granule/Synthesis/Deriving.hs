module Language.Granule.Synthesis.Deriving
  (derivePush, derivePull) where

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Type
import Language.Granule.Syntax.Expr
import Language.Granule.Syntax.Def
import Language.Granule.Syntax.Span
import Language.Granule.Context

import Language.Granule.Checker.Kinds
import Language.Granule.Checker.Monad
import Language.Granule.Checker.Predicates (Quantifier(..))
import Language.Granule.Checker.Variables
import Language.Granule.Checker.SubstitutionContexts
import Language.Granule.Synthesis.Builders

import Language.Granule.Utils

  {-
  Module for automatically deriving graded linear logical
  operations based on types.
  -}

pbox :: Coeffect -> Type -> Pattern Type -> Pattern Type
pbox c t = PBox nullSpanNoFile (Box c t) True

derivePush :: (?globals :: Globals) => Type -> Checker (TypeScheme, Def () Type)
derivePush ty = do
  -- Create fresh variables for the grades
  kVar <- freshIdentifierBase "k" >>= (return . mkId)
  cVar <- freshIdentifierBase "r" >>= (return . mkId)

  -- Get kind of type constructor
  kind <- inferKindOfType nullSpanNoFile ty
  -- Generate fresh type variables and apply them to the kind constructor
  (tyVarsContext, baseTy, argTy) <- fullyApplyTypePush kind (CVar cVar) ty
  -- Give a name to the input
  z <- freshIdentifierBase "z" >>= (return . mkId)
  (returnTy, bodyExpr) <-
    derivePush' (CVar cVar) [] baseTy (makeVar z (trivialScheme argTy))

  -- Build derived type scheme
  let tyVars = map (\(id, (t, _)) -> (id, t)) tyVarsContext
  let tyS = Forall nullSpanNoFile
              ([(kVar, KCoeffect), (cVar, KPromote (TyVar kVar))] ++ tyVars)
              []
              (FunTy Nothing argTy returnTy)
  -- Build the expression
  let expr = Val nullSpanNoFile (FunTy Nothing argTy returnTy) True
              $ Abs returnTy (PVar nullSpanNoFile argTy True z) Nothing bodyExpr
  let name = mkId $ "push" ++ pretty ty
  return $
    (tyS, Def nullSpanNoFile name True
            (EquationList nullSpanNoFile name True
               [Equation nullSpanNoFile name (unforall tyS) True [] expr]) tyS)

derivePush' :: (?globals :: Globals)
            => Coeffect -> Ctxt Id -> Type -> Expr () Type -> Checker (Type, Expr () Type)

-- Unit case:  push_() arg = (case arg of () -> ()) : ())
derivePush' c _sigma argTy@(TyCon (internalName -> "()")) arg = do
  let ty  = FunTy Nothing (Box c argTy) argTy
  return (ty, makeUnitElimP (pbox c argTy) arg makeUnitIntro (trivialScheme argTy))

-- Pair case: push_(t1,t2) arg = (case arg of (x, y) -> (push_t1 [x], push_t2 [y])
derivePush' c _sigma argTy@(ProdTy t1 t2) arg = do
  x <- freshIdentifierBase "x" >>= (return . mkId)
  y <- freshIdentifierBase "y" >>= (return . mkId)
  -- Induction
  (leftTy, leftExpr)   <- derivePush' c _sigma t1 (makeBox (trivialScheme $ Box c t1) (makeVar x (trivialScheme t1)))
  (rightTy, rightExpr) <- derivePush' c _sigma t2 (makeBox (trivialScheme $ Box c t2) (makeVar y (trivialScheme t2)))
  -- Build eliminator
  let returnTy = ProdTy leftTy rightTy
  return (returnTy, makePairElimP (pbox c argTy) arg x y (trivialScheme returnTy) t1 t2
               (makePair leftTy rightTy leftExpr rightExpr))

derivePush' _ _ ty _ = do
  error $ "Cannot push derive for type " ++ show ty

derivePull :: Ctxt (Ctxt (TypeScheme, Substitution)) -> Type -> (TypeScheme, Def () ())
derivePull = error "stub"

-- Given a kind for a type constructor, fully apply the type constructor
-- generator with fresh type variables for each parameter and return a type-variable
-- context containing these variables as well as the applied type along with
-- a pair of the applied type (e.g., F a b) [called the base type]
-- and the type for argument of the push (e.g., F ([] r a) ([] r b))
fullyApplyTypePush :: (?globals :: Globals)
                   => Kind -> Coeffect -> Type -> Checker (Ctxt (Kind, Quantifier), Type, Type)
fullyApplyTypePush k r t = fullyApplyTypePush' k r t t

fullyApplyTypePush' :: (?globals :: Globals)
                    => Kind -> Coeffect -> Type -> Type -> Checker (Ctxt (Kind, Quantifier), Type, Type)
fullyApplyTypePush' KType r baseTy argTy =
  return ([], baseTy, argTy)

fullyApplyTypePush' (KFun t1 t2) r baseTy argTy = do
  -- Fresh ty variable
  tyVar <- freshIdentifierBase "a" >>= (return . mkId)
  -- Apply to the base type
  let baseTy' = TyApp baseTy (TyVar tyVar)
  -- Apply to the "argument of push" type
  let argTy'  =
       case t1 of
         KType -> TyApp argTy (Box r (TyVar tyVar))
         _     -> TyApp argTy (TyVar tyVar)
  -- Induction
  (ids, baseTy'', argTy'') <- fullyApplyTypePush' t2 r baseTy' argTy'
  return ((tyVar, (t1, ForallQ)) : ids, baseTy'', argTy'')

fullyApplyTypePush' k _ _ _ =
  error $ "Cannot fully apply for kind " ++ pretty k