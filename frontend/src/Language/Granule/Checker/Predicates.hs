{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric #-}

module Language.Granule.Checker.Predicates where

{-

This module provides the representation of theorems (predicates)
inside the type checker.

-}

import Control.Monad.Trans.State.Strict
import Data.List (intercalate, (\\))
import GHC.Generics (Generic)

import Language.Granule.Context

import Language.Granule.Syntax.Helpers
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.FirstParameter
import Language.Granule.Syntax.Pretty
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type

data Quantifier =
    -- | Universally quantification, e.g. polymorphic
    ForallQ

    -- | Instantiations of universally quantified variables
    | InstanceQ

    -- | Univeral, but bound in a dependent pattern match
    | BoundQ
  deriving (Show, Eq)

instance Pretty Quantifier where
  pretty ForallQ   = "∀"
  pretty InstanceQ = "∃"
  pretty BoundQ    = "pi"

stripQuantifiers :: Ctxt (a, Quantifier) -> Ctxt a
stripQuantifiers = map (\(var, (k, _)) -> (var, k))


-- Represent constraints generated by the type checking algorithm
data Constraint =
  -- Coeffect resource algebra constraints
    Eq  Span Coeffect Coeffect Type
  | Neq Span Coeffect Coeffect Type
  | ApproximatedBy Span Coeffect Coeffect Type

  --
  | Lub Span Coeffect Coeffect Coeffect Type

  -- NonZeroPromotableTo s x c means that:
  --   exists x . (x != 0) and x * 1 = c
  -- This is used to check constraints related to definite unification
  -- which incurrs a consumption effect
  | NonZeroPromotableTo Span Id Coeffect Type

  -- Used for user-predicates, and also effect types
  | Lt Span Coeffect Coeffect -- Must be Nat kinded
  | Gt Span Coeffect Coeffect -- Must be Nat kinded
  | LtEq Span Coeffect Coeffect -- Must be Nat kinded
  | GtEq Span Coeffect Coeffect -- Must be Nat kinded

  deriving (Show, Eq, Generic)

instance FirstParameter Constraint Span

normaliseConstraint :: Constraint -> Constraint
normaliseConstraint (Eq s c1 c2 t)   = Eq s (normalise c1) (normalise c2) t
normaliseConstraint (Neq s c1 c2 t)  = Neq s (normalise c1) (normalise c2) t
normaliseConstraint (Lub s c1 c2 c3 t) = Lub s (normalise c1) (normalise c2) (normalise c3) t
normaliseConstraint (ApproximatedBy s c1 c2 t) = ApproximatedBy s (normalise c1) (normalise c2) t
normaliseConstraint (NonZeroPromotableTo s x c t) = NonZeroPromotableTo s x (normalise c) t
normaliseConstraint (Lt s c1 c2) = Lt s (normalise c1) (normalise c2)
normaliseConstraint (Gt s c1 c2) = Gt s (normalise c1) (normalise c2)
normaliseConstraint (LtEq s c1 c2) = LtEq s (normalise c1) (normalise c2)
normaliseConstraint (GtEq s c1 c2) = GtEq s (normalise c1) (normalise c2)

instance Monad m => Freshenable m Constraint where
  freshen (Eq s' c1 c2 k) = do
    c1 <- freshen c1
    c2 <- freshen c2
    return $ Eq s' c1 c2 k

  freshen (Neq s' c1 c2 k) = do
    c1 <- freshen c1
    c2 <- freshen c2
    return $ Neq s' c1 c2 k

  freshen (ApproximatedBy s' c1 c2 t) = do
    c1 <- freshen c1
    c2 <- freshen c2
    return $ ApproximatedBy s' c1 c2 t

  freshen (Lub s' c1 c2 c3 t) = do
    c1 <- freshen c1
    c2 <- freshen c2
    c3 <- freshen c3
    return $ Lub s' c1 c2 c3 t

  freshen (NonZeroPromotableTo s i c t) = do
    c <- freshen c
    t <- freshen t
    return $ NonZeroPromotableTo s i c t

  freshen (Lt s c1 c2) = do
    c1 <- freshen c1
    c2 <- freshen c2
    return $ Lt s c1 c2

  freshen (Gt s c1 c2) = do
    c1 <- freshen c1
    c2 <- freshen c2
    return $ Gt s c1 c2

  freshen (LtEq s c1 c2) = LtEq s <$> freshen c1 <*> freshen c2
  freshen (GtEq s c1 c2) = GtEq s <$> freshen c1 <*> freshen c2

-- Used to negate constraints
newtype Neg a = Neg a
  deriving (Eq, Show)

instance Pretty (Neg Constraint) where
    pretty (Neg (Neq _ c1 c2 _)) =
      "Trying to prove that " <> pretty c1 <> " == " <> pretty c2

    pretty (Neg (Eq _ c1 c2 _)) =
      "Actual grade or index `" <> pretty c1 <>
      "` is not equal to specified grade or index `" <> pretty c2 <> "`"

    pretty (Neg (ApproximatedBy _ c1 c2 (TyCon k))) | internalName k == "Level" =
      pretty c2 <> " value cannot be moved to level " <> pretty c1

    pretty (Neg (ApproximatedBy _ c1 c2 k)) =
      case k of
        TyCon (internalName -> "Nat") ->
          "Expected " <> pretty c2 <> " uses, but instead there are " <> pretty c1 <> " actual uses."
        _ -> pretty c1 <> " is not approximatable by " <> pretty c2 <> " for type " <> pretty k

    pretty (Neg p@Lub{}) = 
      "Trying to prove negation of statement: " ++ pretty p

    pretty (Neg (NonZeroPromotableTo _ _ c _)) = "TODO"

    pretty (Neg (Lt _ c1 c2)) =
      "Trying to prove false statement: (" <> pretty c1 <> " < " <> pretty c2 <> ")"

    pretty (Neg (Gt _ c1 c2)) =
      "Trying to prove false statement: (" <> pretty c1 <> " > " <> pretty c2 <> ")"

    pretty (Neg (LtEq _ c1 c2)) =
      "Trying to prove false statement: (" <> pretty c1 <> " ≤ " <> pretty c2 <> ")"

    pretty (Neg (GtEq _ c1 c2)) =
      "Trying to prove false statement: (" <> pretty c1 <> " ≥ " <> pretty c2 <> ")"

instance Pretty [Constraint] where
    pretty constr =
      "---\n" <> (intercalate "\n" . map pretty $ constr)

instance Pretty Constraint where
    pretty (Eq _ c1 c2 _) =
      "(" <> pretty c1 <> " = " <> pretty c2 <> ")" -- @" <> show s

    pretty (Neq _ c1 c2 _) =
        "(" <> pretty c1 <> " ≠ " <> pretty c2 <> ")" -- @" <> show s

    pretty (ApproximatedBy _ c1 c2 k) =
      case k of
        -- Nat is discrete
        TyCon (internalName -> "Nat") -> "(" <> pretty c1 <> " = " <> pretty c2 <> ")"
        _ -> "(" <> pretty c1 <> " ≤ " <> pretty c2 <> ")" -- <> " @ " <> pretty k

    pretty (Lub _ c1 c2 c3 _) =
      "(" <> pretty c1 <> " ⊔ " <> pretty c2 <> " = " <> pretty c3 <> ")"

    pretty (Lt _ c1 c2) =
      "(" <> pretty c1 <> " < " <> pretty c2 <> ")"

    pretty (Gt _ c1 c2) =
      "(" <> pretty c1 <> " > " <> pretty c2 <> ")"

    pretty (LtEq _ c1 c2) =
      "(" <> pretty c1 <> " ≤ " <> pretty c2 <> ")"

    pretty (GtEq _ c1 c2) =
      "(" <> pretty c1 <> " ≥ " <> pretty c2 <> ")"

    pretty (NonZeroPromotableTo _ _ c _) = "TODO"


varsConstraint :: Constraint -> [Id]
varsConstraint (Eq _ c1 c2 _) = freeVars c1 <> freeVars c2
varsConstraint (Neq _ c1 c2 _) = freeVars c1 <> freeVars c2
varsConstraint (Lub _ c1 c2 c3 _) = freeVars c1 <> freeVars c2 <> freeVars c3
varsConstraint (ApproximatedBy _ c1 c2 _) = freeVars c1 <> freeVars c2
varsConstraint (NonZeroPromotableTo _ _ c _) = freeVars c
varsConstraint (Lt _ c1 c2) = freeVars c1 <> freeVars c2
varsConstraint (Gt _ c1 c2) = freeVars c1 <> freeVars c2
varsConstraint (LtEq _ c1 c2) = freeVars c1 <> freeVars c2
varsConstraint (GtEq _ c1 c2) = freeVars c1 <> freeVars c2


-- Represents a predicate generated by the type checking algorithm
data Pred where
    Conj :: [Pred] -> Pred
    Disj :: [Pred] -> Pred
    Impl :: Pred -> Pred -> Pred
    Con  :: Constraint -> Pred
    NegPred  :: Pred -> Pred
    Exists :: Id -> Kind -> Pred -> Pred
    Forall :: Id -> Kind -> Pred -> Pred

mkUniversals :: Ctxt Kind -> Pred -> Pred
mkUniversals [] p = p
mkUniversals ((v, k) : ctxt) p =
  Forall v k (mkUniversals ctxt p)

instance Term Pred where
  freeVars (Conj ps) = concatMap freeVars ps
  freeVars (Disj ps) = concatMap freeVars ps
  freeVars (Impl p1 p2) = freeVars p1 <> freeVars p2
  freeVars (Con c) = varsConstraint c
  freeVars (NegPred p) = freeVars p
  freeVars (Exists x _ p) = freeVars p \\ [x]
  freeVars (Forall x _ p) = freeVars p \\ [x]

boundVars :: Pred -> [Id]
boundVars (Conj ps)    = concatMap boundVars ps
boundVars (Disj ps)    = concatMap boundVars ps
boundVars (Impl p1 p2) = boundVars p1 ++ boundVars p2
boundVars (NegPred p)  = boundVars p
boundVars (Exists x _ p) = x : boundVars p
boundVars (Forall x _ p) = x : boundVars p
boundVars (Con _) = []

instance (Monad m, MonadFail m) => Freshenable m Pred where
  freshen (Conj ps) = do
    ps' <- mapM freshen ps
    return $ Conj ps'

  freshen (Disj ps) = do
    ps' <- mapM freshen ps
    return $ Disj ps'

  freshen (NegPred p) = do
    p' <- freshen p
    return $ NegPred p'

  freshen (Exists v k p) = do
    st <- get

    -- Create a new binding name for v
    let v' = internalName v <> "-e" <> show (counter st)

    -- Updated freshener state
    put (st { tyMap = (internalName v, v') : tyMap st
          , counter = counter st + 1 })

    -- Freshen the rest of the predicate
    p' <- freshen p
    -- Freshening now out of scope
    removeFreshenings [Id (internalName v) v']

    return $ Exists (Id (internalName v) v') k p'

  freshen (Forall v k p) = do
    st <- get

    -- Create a new binding name for v
    let v' = internalName v <> "-e" <> show (counter st)

    -- Updated freshener state
    put (st { tyMap = (internalName v, v') : tyMap st
          , counter = counter st + 1 })

    -- Freshen the rest of the predicate
    p' <- freshen p
    -- Freshening now out of scope
    removeFreshenings [Id (internalName v) v']

    return $ Forall (Id (internalName v) v') k p'

  freshen (Impl p1 p2) = do
    p1' <- freshen p1
    p2' <- freshen p2
    return $ Impl p1' p2'

  freshen (Con cons) = do
    cons' <- freshen cons
    return $ Con cons'

deriving instance Show Pred
deriving instance Eq Pred

-- Fold operation on a predicate
predFold ::
     ([a] -> a)
  -> ([a] -> a)
  -> (a -> a -> a)
  -> (Constraint -> a)
  -> (a -> a)
  -> (Id -> Kind -> a -> a)
  -> (Id -> Kind -> a -> a)
  -> Pred
  -> a
predFold c d i a n e f (Conj ps)   = c (map (predFold c d i a n e f) ps)
predFold c d i a n e f (Disj ps)   = d (map (predFold c d i a n e f) ps)
predFold c d i a n e f (Impl p p') = i (predFold c d i a n e f p) (predFold c d i a n e f p')
predFold _ _ _ a _  _ _ (Con cons)  = a cons
predFold c d i a n e f (NegPred p) = n (predFold c d i a n e f p)
predFold c d i a n e f (Exists x t p) = e x t (predFold c d i a n e f p)
predFold c d i a n e f (Forall x t p) = f x t (predFold c d i a n e f p)

-- Fold operation on a predicate (monadic)
predFoldM :: Monad m =>
     ([a] -> m a)
  -> ([a] -> m a)
  -> (a -> a -> m a)
  -> (Constraint -> m a)
  -> (a -> m a)
  -> (Id -> Kind -> a -> m a)
  -> (Id -> Kind -> a -> m a)
  -> Pred
  -> m a
predFoldM c d i a n e f (Conj ps)   = do
  ps <- mapM (predFoldM c d i a n e f) ps
  c ps

predFoldM c d i a n e f (Disj ps)   = do
  ps <- mapM (predFoldM c d i a n e f) ps
  d ps

predFoldM c d i a n e f (Impl p p') = do
  p  <- predFoldM c d i a n e f p
  p' <- predFoldM c d i a n e f p'
  i p p'

predFoldM _ _ _ a _ _ _ (Con cons)  =
  a cons

predFoldM c d i a n e f (NegPred p) =
  predFoldM c d i a n e f p >>= n

predFoldM c d i a n e f (Exists x t p) =
  predFoldM c d i a n e f p >>= e x t

predFoldM c d i a n e f (Forall x t p) =
  predFoldM c d i a n e f p >>= f x t

instance Pretty [Pred] where
  pretty ps =
    "Size = " <> show (length ps) <> "\n" <>
    (intercalate "\n" (map (\p -> " - " <> pretty p) ps))

instance Pretty Pred where
  pretty =
    predFold
     (intercalate " ∧ ")
     (intercalate " ∨ ")
     (\p q -> "(" <> p <> " -> " <> q <> ")")
     pretty
     (\p -> "¬(" <> p <> ")")
     (\x t p -> "∃ " <> pretty x <> " : " <> pretty t <> " . " <> p)
     (\x t p -> "∀ " <> pretty x <> " : " <> pretty t <> " . " <> p)

-- | Whether the predicate is empty, i.e. contains no constraints
isTrivial :: Pred -> Bool
isTrivial = predFold and or (\lhs rhs -> rhs) (const False) id (\_ _ p -> p) (\_ _ p -> p)

-- Transform universal quantifiers to existentials for the given list of
-- identifiers. This is used for looking at whether a universal theorem
-- can ever be satisfied (e.g., for checking whether dependent-pattern match
-- cases are possible)
universalsAsExistentials :: [Id] -> Pred -> Pred
universalsAsExistentials vars =
    predFold Conj Disj Impl Con NegPred Exists forallCase
  where
    forallCase var kind p =
      if var `elem` vars then Exists var kind p else Forall var kind p


-- TODO: replace with use of `substitute`

-- given an context mapping coeffect type variables to coeffect typ,
-- then rewrite a set of constraints so that any occruences of the kind variable
-- are replaced with the coeffect type
rewriteBindersInPredicate :: Ctxt (Kind, Quantifier) -> Pred -> Pred
rewriteBindersInPredicate ctxt =
    predFold
      Conj
      Disj
      Impl
      (\c -> Con $ foldr (uncurry updateConstraint') c ctxt)
      NegPred
      existsCase
      forallCase
  where
    existsCase :: Id -> Kind -> Pred -> Pred
    existsCase var (KVar kvar) p =
      Exists var k' p
        where
          k' = case lookup kvar ctxt of
                  Just (k, _) -> k
                  Nothing -> KVar kvar
    existsCase var k p = Exists var k p

    forallCase :: Id -> Kind -> Pred -> Pred
    forallCase var (KVar kvar) p =
      Forall var k' p
        where
          k' = case lookup kvar ctxt of
                  Just (k, _) -> k
                  Nothing -> KVar kvar
    forallCase var k p = Forall var k p

    updateConstraint' :: Id -> (Kind, Quantifier) -> Constraint -> Constraint
    updateConstraint' id (k, q) c =
      case demoteKindToType k of
        Just t -> updateConstraint id (t, q) c
        Nothing -> c

    -- `updateConstraint v k c` rewrites any occurence of the kind variable
    -- `v` in the constraint `c` with the kind `k`
    updateConstraint :: Id -> (Type, Quantifier) -> Constraint -> Constraint
    updateConstraint ckindVar (ckind, _) (Eq s c1 c2 k) =
      Eq s (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
        (case k of
          TyVar ckindVar' | ckindVar == ckindVar' -> ckind
          _ -> k)
    updateConstraint ckindVar (ckind, _) (Neq s c1 c2 k) =
            Neq s (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
              (case k of
                TyVar ckindVar' | ckindVar == ckindVar' -> ckind
                _ -> k)

    updateConstraint ckindVar (ckind, _) (ApproximatedBy s c1 c2 k) =
      ApproximatedBy s (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
        (case k of
          TyVar ckindVar' | ckindVar == ckindVar' -> ckind
          _  -> k)

    updateConstraint ckindVar (ckind, _) (Lub s c1 c2 c3 k) =
      Lub s (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2) (updateCoeffect ckindVar ckind c3)
        (case k of
          TyVar ckindVar' | ckindVar == ckindVar' -> ckind
          _  -> k)

    updateConstraint ckindVar (ckind, _) (NonZeroPromotableTo s x c t) =
       NonZeroPromotableTo s x (updateCoeffect ckindVar ckind c)
          (case t of
             TyVar ckindVar' | ckindVar == ckindVar' -> ckind
             _  -> t)

    updateConstraint ckindVar (ckind, _) (Lt s c1 c2) =
        Lt s (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)

    updateConstraint ckindVar (ckind, _) (Gt s c1 c2) =
        Gt s (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)

    updateConstraint ckindVar (ckind, _) (GtEq s c1 c2) =
        GtEq s (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)

    updateConstraint ckindVar (ckind, _) (LtEq s c1 c2) =
        LtEq s (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)

    -- `updateCoeffect v k c` rewrites any occurence of the kind variable
    -- `v` in the coeffect `c` with the kind `k`
    updateCoeffect :: Id -> Type -> Coeffect -> Coeffect
    updateCoeffect ckindVar ckind (CZero (TyVar ckindVar'))
      | ckindVar == ckindVar' = CZero ckind
    updateCoeffect ckindVar ckind (COne (TyVar ckindVar'))
      | ckindVar == ckindVar' = COne ckind
    updateCoeffect ckindVar ckind (CMeet c1 c2) =
      CMeet (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
    updateCoeffect ckindVar ckind (CJoin c1 c2) =
      CJoin (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
    updateCoeffect ckindVar ckind (CPlus c1 c2) =
      CPlus (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
    updateCoeffect ckindVar ckind (CTimes c1 c2) =
      CTimes (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
    updateCoeffect ckindVar ckind (CMinus c1 c2) =
      CMinus (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
    updateCoeffect ckindVar ckind (CExpon c1 c2) =
      CExpon (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
    updateCoeffect ckindVar ckind (CInterval c1 c2) =
      CInterval (updateCoeffect ckindVar ckind c1) (updateCoeffect ckindVar ckind c2)
    updateCoeffect _ _ c = c
