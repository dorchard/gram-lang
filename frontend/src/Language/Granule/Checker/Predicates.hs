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

import Control.Monad.Fail
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
  prettyL l ForallQ   = "∀"
  prettyL l InstanceQ = "∃"
  prettyL l BoundQ    = "pi"

stripQuantifiers :: Ctxt (a, Quantifier) -> Ctxt a
stripQuantifiers = map (\(var, (k, _)) -> (var, k))


-- Represent constraints generated by the type checking algorithm
data Constraint =
    Eq  Span Coeffect Coeffect Type
  | Neq Span Coeffect Coeffect Type
  | ApproximatedBy Span Coeffect Coeffect Type

  -- NonZeroPromotableTo s x c means that:
  --   exists x . (x != 0) and x * 1 = c
  -- This is used to check constraints related to definite unification
  -- which incurrs a consumption effect
  | NonZeroPromotableTo Span Id Coeffect Type

  -- Used for arbitrary predicates (not from the rest of type checking)
  | Lt Span Coeffect Coeffect -- Must be Nat kinded
  | Gt Span Coeffect Coeffect -- Must be Nat kinded

  deriving (Show, Eq, Generic)

instance FirstParameter Constraint Span

normaliseConstraint :: Constraint -> Constraint
normaliseConstraint (Eq s c1 c2 t)   = Eq s (normalise c1) (normalise c2) t
normaliseConstraint (Neq s c1 c2 t)  = Neq s (normalise c1) (normalise c2) t
normaliseConstraint (ApproximatedBy s c1 c2 t) = ApproximatedBy s (normalise c1) (normalise c2) t
normaliseConstraint (NonZeroPromotableTo s x c t) = NonZeroPromotableTo s x (normalise c) t
normaliseConstraint (Lt s c1 c2) = Lt s (normalise c1) (normalise c2)
normaliseConstraint (Gt s c1 c2) = Gt s (normalise c1) (normalise c2)

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

-- Used to negate constraints
newtype Neg a = Neg a
  deriving (Eq, Show)

instance Pretty (Neg Constraint) where
    prettyL l (Neg (Neq _ c1 c2 _)) =
      "Trying to prove that " <> prettyL l c1 <> " == " <> prettyL l c2

    prettyL l (Neg (Eq _ c1 c2 _)) =
      "Actual grade `" <> prettyL l c1 <>
      "` is not equal to specified grade `" <> prettyL l c2 <> "`"

    prettyL l (Neg (ApproximatedBy _ c1 c2 (TyCon k))) | internalId k == "Level" =
      prettyL l c2 <> " value cannot be moved to level " <> prettyL l c1

    prettyL l (Neg (ApproximatedBy _ c1 c2 k)) =
      prettyL l c1 <> " is not approximatable by " <> prettyL l c2 <> " for type " <> pretty k
      <> if k == (TyCon $ mkId "Nat") then " because Nat denotes precise usage." else ""

    prettyL l (Neg (NonZeroPromotableTo _ _ c _)) = "TODO"

    prettyL l (Neg (Lt _ c1 c2)) =
      "Trying to prove false statement: (" <> prettyL l c1 <> " < " <> prettyL l c2 <> ")"

    prettyL l (Neg (Gt _ c1 c2)) =
      "Trying to prove false statement: (" <> prettyL l c1 <> " > " <> prettyL l c2 <> ")"

instance Pretty [Constraint] where
    prettyL l constr =
      "---\n" <> (intercalate "\n" . map (prettyL l) $ constr)

instance Pretty Constraint where
    prettyL l (Eq _ c1 c2 _) =
      "(" <> prettyL l c1 <> " = " <> prettyL l c2 <> ")" -- @" <> show s

    prettyL l (Neq _ c1 c2 _) =
        "(" <> prettyL l c1 <> " ≠ " <> prettyL l c2 <> ")" -- @" <> show s

    prettyL l (ApproximatedBy _ c1 c2 _) =
      "(" <> prettyL l c1 <> " ≤ " <> prettyL l c2 <> ")" -- @" <> show s

    prettyL l (Lt _ c1 c2) =
      "(" <> prettyL l c1 <> " < " <> prettyL l c2 <> ")"

    prettyL l (Gt _ c1 c2) =
      "(" <> prettyL l c1 <> " > " <> prettyL l c2 <> ")"

    prettyL l (NonZeroPromotableTo _ _ c _) = "TODO"


varsConstraint :: Constraint -> [Id]
varsConstraint (Eq _ c1 c2 _) = freeVars c1 <> freeVars c2
varsConstraint (Neq _ c1 c2 _) = freeVars c1 <> freeVars c2
varsConstraint (ApproximatedBy _ c1 c2 _) = freeVars c1 <> freeVars c2
varsConstraint (NonZeroPromotableTo _ _ c _) = freeVars c
varsConstraint (Lt _ c1 c2) = freeVars c1 <> freeVars c2
varsConstraint (Gt _ c1 c2) = freeVars c1 <> freeVars c2


-- Represents a predicate generated by the type checking algorithm
data Pred where
    Conj :: [Pred] -> Pred
    Disj :: [Pred] -> Pred
    Impl :: [Id] -> Pred -> Pred -> Pred
    Con  :: Constraint -> Pred
    NegPred  :: Pred -> Pred
    Exists :: Id -> Kind -> Pred -> Pred

vars :: Pred -> [Id]
vars (Conj ps) = concatMap vars ps
vars (Disj ps) = concatMap vars ps
vars (Impl bounds p1 p2) = (vars p1 <> vars p2) \\ bounds
vars (Con c) = varsConstraint c
vars (NegPred p) = vars p
vars (Exists x _ p) = vars p \\ [x]

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
    let v' = internalId v <> "-e" <> show (counter st)

    -- Updated freshener state
    put (st { tyMap = (internalId v, v') : tyMap st
          , counter = counter st + 1 })

    -- Freshen the rest of the predicate
    p' <- freshen p
    -- Freshening now out of scope
    removeFreshenings [Id (internalId v) v']

    return $ Exists (Id (internalId v) v') k p'

  freshen (Impl [] p1 p2) = do
    p1' <- freshen p1
    p2' <- freshen p2
    return $ Impl [] p1' p2'

  freshen (Impl (v:vs) p p') = do
    st <- get

    -- Freshen the variable bound here
    let v' = internalId v <> "-" <> show (counter st)
    put (st { tyMap = (internalId v, v') : tyMap st
            , counter = counter st + 1 })

    -- Freshen the rest
    (Impl vs' pf pf') <- freshen (Impl vs p p')
    -- Freshening now out of scope
    removeFreshenings [Id (internalId v) v']

    return $ Impl ((Id (internalId v) v'):vs') pf pf'

  freshen (Con cons) = do
    cons' <- freshen cons
    return $ Con cons'

deriving instance Show Pred
deriving instance Eq Pred

-- Fold operation on a predicate
predFold ::
     ([a] -> a)
  -> ([a] -> a)
  -> ([Id] -> a -> a -> a)
  -> (Constraint -> a)
  -> (a -> a)
  -> (Id -> Kind -> a -> a)
  -> Pred
  -> a
predFold c d i a n e (Conj ps)   = c (map (predFold c d i a n e) ps)
predFold c d i a n e (Disj ps)   = d (map (predFold c d i a n e) ps)
predFold c d i a n e (Impl eVar p p') = i eVar (predFold c d i a n e p) (predFold c d i a n e p')
predFold _ _ _ a _  _ (Con cons)  = a cons
predFold c d i a n e (NegPred p) = n (predFold c d i a n e p)
predFold c d i a n e (Exists x t p) = e x t (predFold c d i a n e p)

-- Fold operation on a predicate (monadic)
predFoldM :: Monad m =>
     ([a] -> m a)
  -> ([a] -> m a)
  -> ([Id] -> a -> a -> m a)
  -> (Constraint -> m a)
  -> (a -> m a)
  -> (Id -> Kind -> a -> m a)
  -> Pred
  -> m a
predFoldM c d i a n e (Conj ps)   = do
  ps <- mapM (predFoldM c d i a n e) ps
  c ps

predFoldM c d i a n e (Disj ps)   = do
  ps <- mapM (predFoldM c d i a n e) ps
  d ps

predFoldM c d i a n e (Impl localVars p p') = do
  p <- predFoldM c d i a n e p
  p' <- predFoldM c d i a n e p'
  i localVars p p'

predFoldM _ _ _ a _ _ (Con cons)  =
  a cons

predFoldM c d i a n e (NegPred p) =
  predFoldM c d i a n e p >>= n

predFoldM c d i a n e (Exists x t p) =
  predFoldM c d i a n e p >>= e x t

instance Pretty [Pred] where
  prettyL l ps =
    "Size = " <> show (length ps) <> "\n" <>
    (intercalate "\n" (map (\p -> " - " <> prettyL l p) ps))

instance Pretty Pred where
  prettyL l =
    predFold
     (intercalate " ∧ ")
     (intercalate " ∨ ")
     (\s p q ->
         (if null s then "" else "∀ " <> intercalate "," (map sourceId s) <> " . ")
      <> "(" <> p <> " -> " <> q <> ")")
      (prettyL l)
      (\p -> "¬(" <> p <> ")")
      (\x t p -> "∃ " <> pretty x <> " : " <> pretty t <> " . " <> p)

-- | Whether the predicate is empty, i.e. contains no constraints
isTrivial :: Pred -> Bool
isTrivial = predFold and or (\_ lhs rhs -> lhs && rhs) (const False) id (\_ _ p -> p)
