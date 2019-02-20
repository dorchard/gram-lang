{- Deals with compilation of coeffects into symbolic representations of SBV -}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Granule.Checker.Coeffects where

import Language.Granule.Checker.Monad
import Language.Granule.Context
import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type

-- | Find out whether a coeffect if flattenable, and if so get the operation
-- | used to representing flattening on the grades
flattenable :: Type -> Type -> Maybe ((Coeffect -> Coeffect -> Coeffect), Type)
flattenable t1 t2
 | t1 == t2 = case t1 of
     TyCon (internalName -> "Nat")   -> Just (CTimes, t1)
     TyCon (internalName -> "Level") -> Just (CJoin, t1)

     TyApp (TyCon (internalName -> "Interval")) t ->  flattenable t t
     TyApp (TyCon (internalName -> "Ext")) t ->  flattenable t t
     -- TODO

     _ -> Nothing
 | otherwise = Just (CProduct, TyCon (mkId "×") .@ t1 .@ t2)

-- | Multiply an context by a coeffect
--   (Derelict and promote all variables which are not discharged and are in th
--    set of used variables, (first param))
multAll :: [Id] -> Coeffect -> Ctxt Assumption -> Ctxt Assumption

multAll _ _ [] = []

multAll vars c ((name, Linear t) : ctxt) | name `elem` vars
    = (name, Discharged t c) : multAll vars c ctxt

multAll vars c ((name, Discharged t c') : ctxt) | name `elem` vars
    = (name, Discharged t (c `CTimes` c')) : multAll vars c ctxt

multAll vars c ((_, Linear _) : ctxt) = multAll vars c ctxt
multAll vars c ((_, Discharged _ _) : ctxt) = multAll vars c ctxt
