{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Array.Repa.Runtime where

import Control.Monad (zipWithM)
import Data.Maybe (catMaybes)

import GHC.Base (quotInt, remInt)

import Data.Array.Repa (Z(..), (:.)(..))
import qualified Data.Array.Repa as R
import qualified Data.Array.Repa.Repr.Vector as R
import qualified Data.Array.Repa.Repr.Unboxed as R
import qualified Data.Array.Repa.Eval as R

newtype RuntimeShape = RuntimeShape { unRuntimeShape :: [Int] }
  deriving (Eq, Ord, Show, Read)

instance R.Shape RuntimeShape where
  rank (RuntimeShape xs) = length xs
  zeroDim = RuntimeShape []
  unitDim = RuntimeShape [1]
  intersectDim (RuntimeShape xs) (RuntimeShape ys) = RuntimeShape (zipWith min xs ys)
  addDim (RuntimeShape xs) (RuntimeShape ys) = RuntimeShape (zipWith (+) xs ys)
  size (RuntimeShape xs) = product xs
  sizeIsValid (RuntimeShape ss) = True -- TODO fix this later

  toIndex (RuntimeShape ss) (RuntimeShape is) =
    let
      go [] _ = 0
      go _ [] = 0
      go (s : ss) (i : is) = go ss is * s + i
    in
      go ss is

  fromIndex (RuntimeShape ss) i =
    let
      go [] j = []
      go (x : xs) j = remInt j x  : go xs (quotInt j x)
    in
      RuntimeShape $ go ss i

  inShapeRange (RuntimeShape xs) (RuntimeShape ys) (RuntimeShape zs) =
    let
      f x y z = x <= z && z < y
    in
      and $ zipWith3 f xs ys zs

  listOfShape (RuntimeShape xs) = xs
  shapeOfList = RuntimeShape
  deepSeq (RuntimeShape xs) a = xs `seq` a

newtype RuntimeSlice = RuntimeSlice { unRuntimeSlice :: [Maybe Int] }
  deriving (Eq, Ord, Show, Read)

type instance R.FullShape RuntimeSlice = RuntimeShape
type instance R.SliceShape RuntimeSlice = RuntimeShape

instance R.Slice RuntimeSlice where
  sliceOfFull (RuntimeSlice ss) (RuntimeShape sh) =
    let
      ls = length ss
      lh = length sh
      n = max ls lh - ls
      ss' = ss ++ replicate n Nothing
      f Nothing x = Just x
      f (Just _) _ = Nothing
    in
      RuntimeShape . catMaybes $ zipWith f ss' sh

  fullOfSlice (RuntimeSlice ss) (RuntimeShape sh) =
    let
      ls = length ss
      lh = length sh
      n = max ls lh - ls
      ss' = ss ++ replicate n Nothing
      go [] ys = ys
      go (Nothing : xs) (y : ys) = y : go xs ys
      go (Just x : xs) ys = x : go xs ys
    in
      RuntimeShape $ go ss' sh

wrapUpdate :: (R.Unbox a, Show a) => [RuntimeSlice]
           -> RuntimeArray R.U a
           -> RuntimeArray R.U a
           -> RuntimeArray R.U a
wrapUpdate ss (RuntimeArray new) (RuntimeArray old) =
  RuntimeArray (arrayUpdate ss new old)
wrapUpdate _ (DimensionError i j) _ =
  DimensionError i j
wrapUpdate _ _ (DimensionError i j) =
  DimensionError i j

arrayUpdate :: (R.Unbox a, Show a) => [RuntimeSlice]
            -> R.Array R.U RuntimeShape a
            -> R.Array R.U RuntimeShape a
            -> R.Array R.U RuntimeShape a
arrayUpdate ss new old =
  R.computeUnboxedS .
  R.traverse old id $ \getOld ix ->
    case lookupSlices ss ix of
      Just ix' -> R.index new ix'
      Nothing -> getOld ix

lookupSlices :: [RuntimeSlice] -> RuntimeShape -> Maybe RuntimeShape
lookupSlices [] sh = Just sh
lookupSlices (s : ss) sh =
  lookupSlices ss sh >>= \sh' ->
    if sliceFilter s sh'
    then Just $ R.sliceOfFull s sh'
    else Nothing

sliceFilter :: RuntimeSlice -> RuntimeShape -> Bool
sliceFilter (RuntimeSlice []) (RuntimeShape _) =
  True
sliceFilter (RuntimeSlice _) (RuntimeShape []) =
  True
sliceFilter (RuntimeSlice (Just x : xs)) (RuntimeShape (s : ss)) =
  x == s && sliceFilter (RuntimeSlice xs) (RuntimeShape ss)
sliceFilter (RuntimeSlice (Nothing : xs)) (RuntimeShape (_ : ss)) =
  sliceFilter (RuntimeSlice xs) (RuntimeShape ss)

-- TODO do index checking here, fold problems into the errors in RuntimeArray
runtimeSlice :: R.Source rep a => RuntimeArray rep a -> RuntimeSlice -> RuntimeArray rep a
runtimeSlice (RuntimeArray a) sl =
  RuntimeArrayD $ R.slice a sl
runtimeSlice (RuntimeArrayD d) sl =
  RuntimeArrayD $ R.slice d sl
runtimeSlice (DimensionError i j) _ =
  DimensionError i j

-- TODO do index checking here, fold problems into the errors in RuntimeArray
runtimeExtend :: R.Source rep a => RuntimeSlice -> RuntimeArray rep a -> RuntimeArray rep a
runtimeExtend sl (RuntimeArray a) =
  RuntimeArrayD $ R.extend sl a
runtimeExtend sl (RuntimeArrayD d) =
  RuntimeArrayD $ R.extend sl d
runtimeExtend _ (DimensionError i j) =
  DimensionError i j

-- We can probably sidestep having to write things like the above if we write
-- our own R.Source instance:

-- data R rep

-- instance R.Source rep a => R.Source (R rep) a where
--   data Array (R rep) sh a =
--       RA (R.Array rep RuntimeShape a)
--     | RAD (R.Array R.D RuntimeShape a)
--     | DE RuntimeShape RuntimeShape

--   extent (RA a) = R.shapeOfList . R.listOfShape . R.extent $ a
--   extent (RAD a) = R.shapeOfList . R.listOfShape . R.extent $ a
--   extent e@(DE _ _) = error "boom"

class R.Source rep a => RuntimeArrayHelper rep a where
  fromList :: RuntimeShape -> [a] -> RuntimeArray rep a
  run :: RuntimeArray rep a -> Either ([Int], [Int]) (R.Array rep RuntimeShape a)
  runP :: Monad m => RuntimeArray rep a -> m (Either ([Int], [Int]) (R.Array rep RuntimeShape a))

instance R.Unbox a => RuntimeArrayHelper R.U a where
  fromList sh = RuntimeArray . R.fromListUnboxed sh
  run (RuntimeArray a) = Right a
  run (RuntimeArrayD d) = Right . R.computeUnboxedS $ d
  run (DimensionError i j) = Left (i, j)
  runP (RuntimeArray a) = pure . Right $ a
  runP (RuntimeArrayD d) = Right <$> R.computeUnboxedP d
  runP (DimensionError i j) = pure . Left $ (i, j)

instance RuntimeArrayHelper R.V a where
  fromList sh = RuntimeArray . R.fromListVector sh
  run (RuntimeArray a) = Right a
  run (RuntimeArrayD d) = Right . R.computeVectorS $ d
  run (DimensionError i j) = Left (i, j)
  runP (RuntimeArray a) = pure . Right $ a
  runP (RuntimeArrayD d) = Right <$> R.computeVectorP d
  runP (DimensionError i j) = pure . Left $ (i, j)

data RuntimeArray rep a =
    RuntimeArray (R.Array rep RuntimeShape a)
  | RuntimeArrayD (R.Array R.D RuntimeShape a)
  -- TODO add a CallStack here, freeze the callstack so we don't get bogged down in the details
  | DimensionError [Int] [Int]

instance (Eq a, RuntimeArrayHelper rep a) => Eq (RuntimeArray rep a) where
  w1 == w2 = case (run w1, run w2) of
    (Right a1, Right a2) -> R.toList a1 == R.toList a2 && R.extent a1 == R.extent a2
    (Left (i1, j1), Left (i2, j2)) -> i1 == i2 && j1 == j2
    _ -> False

instance (Ord a, RuntimeArrayHelper rep a) => Ord (RuntimeArray rep a) where
  compare w1 w2 = case (run w1, run w2) of
    (Right x, Right y) ->
      case compare (R.extent x) (R.extent y) of
        LT -> LT
        EQ -> compare (R.toList x) (R.toList y)
        GT -> GT
    (Right _, _) ->
      LT
    (_, Right _) ->
      GT
    (Left (i1, j1), Left (i2, j2)) ->
      compare (i1,j1) (i2,j2)

instance (Show a, RuntimeArrayHelper rep a) => Show (RuntimeArray rep a) where
  showsPrec n w = case run w of
    Left (i, j) -> showString "DimensionError " . showsPrec n i . showString " " . showsPrec n j
    Right a -> showString "RuntimeArray (" . showsPrec n (R.extent a) . showString ") " . showsPrec n (R.toList a)

-- instance (Read a, RuntimeArrayHelper rep a) => Read (RuntimeArray rep a) where

arrayFromList :: (R.Shape sh, RuntimeArrayHelper rep a) => sh -> [a] -> RuntimeArray rep a
arrayFromList sh = fromList (R.shapeOfList . R.listOfShape $ sh)

liftScalar :: RuntimeArrayHelper rep a => a -> RuntimeArray rep a
liftScalar = fromList (RuntimeShape []) . pure

instance (Num a, R.Source rep a, RuntimeArrayHelper rep a) => Num (RuntimeArray rep a) where
  (+) = liftBinary (+)
  (-) = liftBinary (-)
  (*) = liftBinary (*)
  fromInteger = liftScalar . fromInteger
  abs = liftUnary abs
  signum = liftUnary signum

instance (Fractional a, R.Source rep a, RuntimeArrayHelper rep a) => Fractional (RuntimeArray rep a) where
  (/) = liftBinary (/)
  fromRational =  liftScalar . fromRational

instance (Floating a, R.Source rep a, RuntimeArrayHelper rep a) => Floating (RuntimeArray rep a) where
  pi = liftScalar pi
  exp = liftUnary exp
  log = liftUnary exp
  sqrt = liftUnary exp
  (**) = liftBinary (**)
  logBase = liftBinary logBase
  sin = liftUnary sin
  cos = liftUnary cos
  tan = liftUnary tan
  asin = liftUnary asin
  acos = liftUnary acos
  atan = liftUnary atan
  sinh = liftUnary sinh
  cosh = liftUnary cosh
  tanh = liftUnary tanh
  asinh = liftUnary asinh
  acosh = liftUnary acosh
  atanh = liftUnary atanh

liftUnary :: (R.Source rep a)
            => (a -> b)
            -> RuntimeArray rep a
            -> RuntimeArray rep b
liftUnary fn (RuntimeArray a) =
  RuntimeArrayD . R.map fn $ a
liftUnary fn (RuntimeArrayD a) =
  RuntimeArrayD . R.map fn $ a
liftUnary _ e@(DimensionError i1 i2) =
  DimensionError i1 i2

liftBinary :: (R.Source rep a, R.Source rep b)
            => (a -> b -> c)
            -> RuntimeArray rep a
            -> RuntimeArray rep b
            -> RuntimeArray rep c
liftBinary fn (RuntimeArray a1) (RuntimeArray a2) =
  broadcastBinary fn a1 a2
liftBinary fn (RuntimeArray a1) (RuntimeArrayD a2) =
  broadcastBinary fn a1 a2
liftBinary fn (RuntimeArrayD a1) (RuntimeArray a2) =
  broadcastBinary fn a1 a2
liftBinary fn (RuntimeArrayD a1) (RuntimeArrayD a2) =
  broadcastBinary fn a1 a2
liftBinary _ e@(DimensionError i1 i2) _ =
  DimensionError i1 i2
liftBinary _ _ e@(DimensionError i1 i2) =
  DimensionError i1 i2

broadcastBinary :: (R.Shape sh1, R.Shape sh2, R.Source rep1 a, R.Source rep2 b)
                => (a -> b -> c)
                -> R.Array rep1 sh1 a
                -> R.Array rep2 sh2 b
                -> RuntimeArray rep c
broadcastBinary fn a1 a2 =
  let
    sh1 = R.extent a1
    sh2 = R.extent a2
  in
    case broadcastSh sh1 sh2 of
      Nothing -> DimensionError (R.listOfShape sh1) (R.listOfShape sh2)
      Just sh3 ->
          let
            a1' = R.backpermute sh3 (lim sh1) a1
            a2' = R.backpermute sh3 (lim sh2) a2
          in
            RuntimeArrayD $ R.zipWith fn a1' a2'

broadcastSh :: (R.Shape sh1, R.Shape sh2)
             => sh1
             -> sh2
             -> Maybe RuntimeShape
broadcastSh sh1 sh2 =
  let
    l1 = R.listOfShape sh1
    r1 = length l1
    l2 = R.listOfShape sh2
    r2 = length l2
    r = max r1 r2
    f a b
      | a == b = Just a
      | a == 1 = Just b
      | b == 1 = Just a
      | otherwise = Nothing
    l3 = zipWithM f (l1 ++ replicate (r - r1) 1) (l2 ++ replicate (r - r2) 1)
  in
    R.shapeOfList <$> l3

lim :: (R.Shape sh1, R.Shape sh2) => sh1 -> sh2 -> sh1
lim sh1 sh2 =
  let
    l1 = R.listOfShape sh1
    l2 = R.listOfShape sh2
    f a b
      | a <= b    = 0
      | otherwise = b
    l3 = zipWith f l1 l2
  in
    R.shapeOfList l3

checkMatch :: [Int] -> [Maybe Int] -> Bool
checkMatch xs ys =
  let
    l1 = length xs
    l2 = length ys
    r = max l1 l2
    f x = fmap (== x)
  in
    and . catMaybes $ zipWith f (xs ++ replicate (r - l1) 1) (ys ++ replicate (r - l2) (Just 1))

dimsMatch :: R.Source rep a => [Maybe Int] -> RuntimeArray rep a -> Bool
dimsMatch ds (RuntimeArray a) =
  checkMatch (R.listOfShape . R.extent $ a) ds
dimsMatch ds (RuntimeArrayD a) =
  checkMatch (R.listOfShape . R.extent $ a) ds
dimsMatch _ _ =
  False
