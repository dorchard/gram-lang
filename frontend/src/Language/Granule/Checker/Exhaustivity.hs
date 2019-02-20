{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Granule.Checker.Exhaustivity (isIrrefutable) where

import Control.Monad.State.Strict

import Language.Granule.Checker.Monad
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Pattern
import Language.Granule.Syntax.Span
import Language.Granule.Syntax.Type
import Language.Granule.Utils

-- | Check whether a given pattern match will always succeed
-- NB: This is work in progress.
isIrrefutable :: (?globals :: Globals) => Span -> Type -> Pattern t -> Checker Bool
isIrrefutable s t (PVar _ _ _) = return True
isIrrefutable s t (PWild _ _)  = return True
isIrrefutable s (Box _ t) (PBox _ _ p) = isIrrefutable s t p
isIrrefutable s t@(TyVar _) (PBox _ _ p) = isIrrefutable s t p
isIrrefutable s (TyCon c) _ = checkCardinality c
isIrrefutable s t@(TyApp t1 t2) (PConstr _ _ name ps) = unpeel s t (reverse ps)
isIrrefutable s t@(TyVar _) (PConstr _ _ (internalName -> "(,)") [p1, p2]) = do
  i1 <- isIrrefutable s t p1 -- somewhat of a cheat but type information is not important here
  i2 <- isIrrefutable s t p2 -- somewhat of a cheat but type info is not important here
  return (i1 && i2)

isIrrefutable s _ _ = return False

-- | Check if every sub-pattern of a type application is also irrefutable
-- (reverse the patterns coming out of a PConstr before calling this)
unpeel :: (?globals :: Globals) => Span -> Type -> [Pattern t] -> Checker Bool
unpeel s (TyApp t1 t2) (p:ps) = do
    irrefutable <- isIrrefutable s t2 p
    if irrefutable then unpeel s t1 ps else return False
unpeel _ (TyCon c) _ = checkCardinality c
unpeel _ _ _ = return False

-- | Get the number of data constructors, only irrefutable if = `Just 1`
checkCardinality :: Id -> Checker Bool
checkCardinality tyCon = do
    st <- get
    case lookup tyCon (typeConstructors st) of
      Just (_,Just 1) -> return True
      _               -> return False
