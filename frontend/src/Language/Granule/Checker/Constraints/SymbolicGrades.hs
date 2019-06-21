{-# LANGUAGE DeriveGeneric  #-}

module Language.Granule.Checker.Constraints.SymbolicGrades where

{- Provides a symbolic representation of grades (coeffects, effects, indices)
   in order for a solver to use.
-}

import Language.Granule.Syntax.Identifiers
import Language.Granule.Syntax.Type
import Language.Granule.Checker.Constraints.SNatX (SNatX(..))

import qualified Data.Text as T
import GHC.Generics (Generic)
import Data.SBV hiding (kindOf, name, symbolic)
import qualified Data.Set as S

-- Symbolic grades, for coeffects and indices
data SGrade =
       SNat      SInteger
     | SFloat    SFloat
     | SLevel    SInteger
     | SSet      (S.Set (Id, Type))
     | SExtNat   SNatX
     | SInterval { sLowerBound :: SGrade, sUpperBound :: SGrade }
     -- Single point coeffect (not exposed at the moment)
     | SPoint
     | SProduct { sfst :: SGrade, ssnd :: SGrade }

     -- A kind of embedded uninterpreted sort which can accept some equations
     -- Used for doing some limited solving over poly coeffect grades
     | SUnknown SynTree
                                 -- but if Nothing then these values are incomparable
    deriving (Show, Generic)

data SynTree =
    SynPlus SynTree SynTree
  | SynTimes SynTree SynTree
  | SynMeet SynTree SynTree
  | SynJoin SynTree SynTree
  | SynLeaf (Maybe SInteger)  -- Just 0 and Just 1 can be identified

instance Show SynTree where
  show (SynPlus s t) = "(" ++ show s ++ " + " ++ show t ++ ")"
  show (SynTimes s t) = show s ++ " * " ++ show t
  show (SynJoin s t) = "(" ++ show s ++ " \\/ " ++ show t ++ ")"
  show (SynMeet s t) = "(" ++ show s ++ " /\\ " ++ show t ++ ")"
  show (SynLeaf Nothing) = "?"
  show (SynLeaf (Just n)) = T.unpack $
    T.replace (T.pack $ " :: SInteger") (T.pack "") (T.pack $ show n)


sEqTree :: SynTree -> SynTree -> SBool
sEqTree (SynPlus s s') (SynPlus t t') = (sEqTree s t) .&& (sEqTree s' t')
sEqTree (SynTimes s s') (SynTimes t t') = (sEqTree s t) .&& (sEqTree s' t')
sEqTree (SynMeet s s') (SynMeet t t') = (sEqTree s t) .&& (sEqTree s' t')
sEqTree (SynJoin s s') (SynJoin t t') = (sEqTree s t) .&& (sEqTree s' t')
sEqTree (SynLeaf Nothing) (SynLeaf Nothing) = sFalse
sEqTree (SynLeaf (Just n)) (SynLeaf (Just n')) = n .=== n'
sEqTree _ _ = sFalse

-- Work out if two symbolic grades are of the same type
match :: SGrade -> SGrade -> Bool
match (SNat _) (SNat _) = True
match (SFloat _) (SFloat _) = True
match (SLevel _) (SLevel _) = True
match (SSet _) (SSet _) = True
match (SExtNat _) (SExtNat _) = True
match (SInterval s1 s2) (SInterval t1 t2) = match s1 t1 && match t1 t2
match SPoint SPoint = True
match (SProduct s1 s2) (SProduct t1 t2) = match s1 t1 && match s2 t2
match (SUnknown _) (SUnknown _) = True
match _ _ = False

isSProduct :: SGrade -> Bool
isSProduct (SProduct _ _) = True
isSProduct _ = False

applyToProducts :: (SGrade -> SGrade -> a)
            -> (a -> a -> b)
            -> (SGrade -> a)
            -> SGrade -> SGrade -> b

applyToProducts f g _ a@(SProduct a1 b1) b@(SProduct a2 b2) =
  if (match a1 a2) && (match b1 b2)
    then g (f a1 a2) (f b1 b2)
    else if (match a1 b2) && (match b1 a2)
      then g (f a1 b2) (f b1 a2)
      else error $"Solver grades " <> show a <> " and " <> show b <> " are incompatible "

applyToProducts f g h a@(SProduct a1 b1) c =
  if match a1 c
    then g (f a1 c) (h b1)
    else if match b1 c
         then g (h a1) (f b1 c)
         else error $ "Solver grades " <> show a <> " and " <> show c <> " are incompatible "

applyToProducts f g h c a@(SProduct a1 b1) =
  if match c a1
    then g (f c a1) (h b1)
    else if match c b1
         then g (h a1) (f c b1)
         else error $ "Solver grades " <> show a <> " and " <> show c <> " are incompatible "

applyToProducts _ _ _ a b =
  error $ "Solver grades " <> show a <> " and " <> show b <> " are not products"

natLike :: SGrade -> Bool
natLike (SNat _) = True
natLike (SExtNat _) = True
natLike _ = False

instance Mergeable SGrade where
  symbolicMerge s sb (SNat n) (SNat n') = SNat (symbolicMerge s sb n n')
  symbolicMerge s sb (SFloat n) (SFloat n') = SFloat (symbolicMerge s sb n n')
  symbolicMerge s sb (SLevel n) (SLevel n') = SLevel (symbolicMerge s sb n n')
  symbolicMerge s sb (SSet n) (SSet n') = error "Can't symbolic merge sets yet"
  symbolicMerge s sb (SExtNat n) (SExtNat n') = SExtNat (symbolicMerge s sb n n')
  symbolicMerge s sb (SInterval lb1 ub1) (SInterval lb2 ub2) =
    SInterval (symbolicMerge s sb lb1 lb2) (symbolicMerge s sb ub1 ub2)
  symbolicMerge s sb SPoint SPoint = SPoint

  symbolicMerge s sb a b | isSProduct a || isSProduct b =
    applyToProducts (symbolicMerge s sb) SProduct id a b

  symbolicMerge s sb (SUnknown (SynLeaf (Just u))) (SUnknown (SynLeaf (Just u'))) =
    SUnknown (SynLeaf (Just (symbolicMerge s sb u u')))
  symbolicMerge _ _ s t = cannotDo "symbolicMerge" s t

instance OrdSymbolic SGrade where
  (SInterval lb1 ub1) .< (SInterval lb2 ub2) =
    lb2 .< lb1 .&& ub1 .< ub2
  (SNat n)    .< (SNat n') = n .< n'
  (SFloat n)  .< (SFloat n') = n .< n'
  (SLevel n)  .< (SLevel n') = n .< n'
  (SSet n)    .< (SSet n') = error "Can't compare symbolic sets yet"
  (SExtNat n) .< (SExtNat n') = n .< n'
  SPoint .< SPoint = sTrue
  s .< t | isSProduct s || isSProduct t = applyToProducts (.<) (.&&) (const sTrue) s t
  (SUnknown (SynLeaf (Just n))) .< (SUnknown (SynLeaf (Just n'))) = n .< n'
  s .< t = cannotDo ".<" s t

instance EqSymbolic SGrade where
  (SInterval lb1 ub1) .== (SInterval lb2 ub2) =
    lb2 .== lb1 .&& ub1 .== ub2
  (SNat n)    .== (SNat n') = n .== n'
  (SFloat n)  .== (SFloat n') = n .== n'
  (SLevel n)  .== (SLevel n') = n .== n'
  (SSet n)    .== (SSet n') = error "Can't compare symbolic sets yet"
  (SExtNat n) .== (SExtNat n') = n .== n'
  SPoint .== SPoint = sTrue
  s .== t | isSProduct s || isSProduct t = applyToProducts (.==) (.&&) (const sTrue) s t
  (SUnknown t) .== (SUnknown t') = sEqTree t t'
  s .== t = cannotDo ".==" s t

-- | Meet operation on symbolic grades
symGradeMeet :: SGrade -> SGrade -> SGrade
symGradeMeet (SNat n1) (SNat n2)     = SNat $ n1 `smin` n2
symGradeMeet (SSet s) (SSet t)       = SSet $ S.intersection s t
symGradeMeet (SLevel s) (SLevel t)   = SLevel $ s `smin` t
symGradeMeet (SFloat n1) (SFloat n2) = SFloat $ n1 `smin` n2
symGradeMeet (SExtNat x) (SExtNat y) = SExtNat (x `smin` y)
symGradeMeet (SInterval lb1 ub1) (SInterval lb2 ub2) =
  SInterval (lb1 `symGradeMeet` lb2) (ub1 `symGradeMeet` ub2)
symGradeMeet SPoint SPoint = SPoint
symGradeMeet s t | isSProduct s || isSProduct t =
  applyToProducts symGradeMeet SProduct id s t
symGradeMeet (SUnknown (SynLeaf (Just n))) (SUnknown (SynLeaf (Just n'))) =
  SUnknown (SynLeaf (Just (n `smin` n')))
symGradeMeet (SUnknown t) (SUnknown t') = SUnknown (SynMeet t t')
symGradeMeet s t = cannotDo "meet" s t

-- | Join operation on symbolic grades
symGradeJoin :: SGrade -> SGrade -> SGrade
symGradeJoin (SNat n1) (SNat n2) = SNat (n1 `smax` n2)
symGradeJoin (SSet s) (SSet t)   = SSet $ S.intersection s t
symGradeJoin (SLevel s) (SLevel t) = SLevel $ s `smax` t
symGradeJoin (SFloat n1) (SFloat n2) = SFloat (n1 `smax` n2)
symGradeJoin (SExtNat x) (SExtNat y) = SExtNat (x `smax` y)
symGradeJoin (SInterval lb1 ub1) (SInterval lb2 ub2) =
   SInterval (lb1 `symGradeJoin` lb2) (ub1 `symGradeJoin` ub2)
symGradeJoin SPoint SPoint = SPoint
symGradeJoin s t | isSProduct s || isSProduct t =
  applyToProducts symGradeJoin SProduct id s t
symGradeJoin (SUnknown (SynLeaf (Just n))) (SUnknown (SynLeaf (Just n'))) =
  SUnknown (SynLeaf (Just (n `smax` n')))
symGradeJoin (SUnknown t) (SUnknown t') = SUnknown (SynJoin t t')
symGradeJoin s t = cannotDo "join" s t

-- | Plus operation on symbolic grades
symGradePlus :: SGrade -> SGrade -> SGrade
symGradePlus (SNat n1) (SNat n2) = SNat (n1 + n2)
symGradePlus (SSet s) (SSet t) = SSet $ S.union s t
symGradePlus (SLevel lev1) (SLevel lev2) = SLevel $ lev1 `smax` lev2
symGradePlus (SFloat n1) (SFloat n2) = SFloat $ n1 + n2
symGradePlus (SExtNat x) (SExtNat y) = SExtNat (x + y)
symGradePlus (SInterval lb1 ub1) (SInterval lb2 ub2) =
    SInterval (lb1 `symGradePlus` lb2) (ub1 `symGradePlus` ub2)
symGradePlus SPoint SPoint = SPoint
symGradePlus s t | isSProduct s || isSProduct t =
   applyToProducts symGradePlus SProduct id s t

-- Direct encoding of addition unit
symGradePlus (SUnknown t@(SynLeaf (Just u))) (SUnknown t'@(SynLeaf (Just u'))) =
  ite (u .== 0) (SUnknown (SynLeaf (Just u')))
    (ite (u' .== 0) (SUnknown (SynLeaf (Just u))) (SUnknown (SynPlus t t')))

symGradePlus (SUnknown t@(SynLeaf (Just u))) (SUnknown t') =
  ite (u .== 0) (SUnknown t') (SUnknown (SynPlus t t'))

symGradePlus (SUnknown um) (SUnknown (SynLeaf u)) =
  symGradePlus (SUnknown (SynLeaf u)) (SUnknown um)

symGradePlus s t = cannotDo "plus" s t

-- | Times operation on symbolic grades
symGradeTimes :: SGrade -> SGrade -> SGrade
symGradeTimes (SNat n1) (SNat n2) = SNat (n1 * n2)
symGradeTimes (SSet s) (SSet t) = SSet $ S.union s t
symGradeTimes (SLevel lev1) (SLevel lev2) =
    ite (lev1 .== literal unusedRepresentation)
        (SLevel $ literal unusedRepresentation)
      $ ite (lev2 .== literal unusedRepresentation)
            (SLevel $ literal unusedRepresentation)
            (SLevel $ lev1 `smax` lev2)
symGradeTimes (SFloat n1) (SFloat n2) = SFloat $ n1 * n2
symGradeTimes (SExtNat x) (SExtNat y) = SExtNat (x * y)
symGradeTimes (SInterval lb1 ub1) (SInterval lb2 ub2) =
    --SInterval (lb1 `symGradeTimes` lb2) (ub1 `symGradeTimes` ub2)
    SInterval (comb symGradeMeet) (comb symGradeJoin)
     where
      comb f = ((lb1lb2 `f` lb1ub2) `f` ub1lb2) `f` ub1ub2
      lb1lb2 = lb1 `symGradeTimes` lb2
      lb1ub2 = lb1 `symGradeTimes` ub2
      ub1lb2 = ub1 `symGradeTimes` lb2
      ub1ub2 = ub1 `symGradeTimes` ub2
symGradeTimes SPoint SPoint = SPoint
symGradeTimes s t | isSProduct s || isSProduct t =
  applyToProducts symGradeTimes SProduct id s t

-- units and absorption directly encoded
symGradeTimes (SUnknown t@(SynLeaf (Just u))) (SUnknown t'@(SynLeaf (Just u'))) =
    ite (u .== 1) (SUnknown (SynLeaf (Just u')))
      (ite (u' .== 1) (SUnknown (SynLeaf (Just u)))
        (ite (u .== 0) (SUnknown (SynLeaf (Just 0)))
          (ite (u' .== 0) (SUnknown (SynLeaf (Just 0)))
             (SUnknown (SynPlus t t')))))

symGradeTimes (SUnknown t@(SynLeaf (Just u))) (SUnknown t') =
  ite (u .== 1) (SUnknown t')
    (ite (u .== 0) (SUnknown (SynLeaf (Just 0))) (SUnknown (SynTimes t t')))

symGradeTimes (SUnknown um) (SUnknown (SynLeaf u)) =
  symGradeTimes (SUnknown (SynLeaf u)) (SUnknown um)

symGradeTimes s t = cannotDo "times" s t

-- | Minus operation on symbolic grades
symGradeMinus :: SGrade -> SGrade -> SGrade
symGradeMinus (SNat n1) (SNat n2) = SNat $ ite (n1 .< n2) 0 (n1 - n2)
symGradeMinus (SSet s) (SSet t) = SSet $ s S.\\ t
symGradeMinus (SExtNat x) (SExtNat y) = SExtNat (x - y)
symGradeMinus (SInterval lb1 ub1) (SInterval lb2 ub2) =
    SInterval (lb1 `symGradeMinus` lb2) (ub1 `symGradeMinus` ub2)
symGradeMinus SPoint SPoint = SPoint
symGradeMinus s t | isSProduct s || isSProduct t =
  applyToProducts symGradeMinus SProduct id s t
symGradeMinus s t = cannotDo "minus" s t

cannotDo :: String -> SGrade -> SGrade -> a
cannotDo op (SUnknown s) (SUnknown t) =
  error $ "It is unknown whether "
      <> show s <> " "
      <> op <> " "
      <> show t
      <> " holds for all resource algebras."

cannotDo op s t =
  error $ "Cannot perform symbolic operation `"
      <> op <> "` on "
      <> show s <> " and "
      <> show t
