module Merge

import Data.List.Views
import Data.So

import Order
import OrderedList
import Perm
import Sorted

%hide merge
%default total

-- Merge sort

merge : (f : Order a) -> (xs, ys : List a) -> List a
merge f xs [] = xs
merge f [] ys = ys
merge f (x :: xs) (y :: ys) = case choose $ x `f` y of
                                   Left _   => x :: merge f xs (y :: ys)
                                   Right _  => y :: merge f (x :: xs) ys

mergeSort' : (f : Order a) -> (xs : List a) -> SplitRec xs -> List a
mergeSort' f [] SplitRecNil = []
mergeSort' f [x] SplitRecOne = [x]
mergeSort' f (lefts ++ rights) (SplitRecPair lrec rrec) = merge f (mergeSort' f lefts lrec ) (mergeSort' f rights rrec)

mergeSort : (f : Order a) -> (xs : List a) -> List a
mergeSort f xs = mergeSort' f xs (splitRec xs)

-- Proofs

mergeLeftEmptyId : (f : Order a) -> (ys : List a) -> merge f [] ys = ys
mergeLeftEmptyId f [] = Refl
mergeLeftEmptyId f (x :: xs) = Refl

-- Merge is a permutation

mergeIsPerm : (f : Order a) -> (xs, ys : List a) -> Perm (merge f xs ys) (xs ++ ys)
mergeIsPerm f [] ys = rewrite mergeLeftEmptyId f ys in permRefl ys
mergeIsPerm f xs [] = rewrite appendNilRightNeutral xs in permRefl xs
mergeIsPerm f (x :: xs) (y :: ys) with (choose $ x `f` y)
  | Left _ = PRest $ mergeIsPerm f xs (y :: ys)
  | Right _ = let restPerm = PRest {x = y} $ mergeIsPerm f (x :: xs) ys
                  permMid' = permSwapMid y (x :: xs) ys
              in PTrans restPerm permMid'

mergeSort'IsPerm : (f : Order a) -> (xs : List a) -> (s : SplitRec xs) -> Perm (mergeSort' f xs s) xs
mergeSort'IsPerm f [] SplitRecNil = PNil
mergeSort'IsPerm f [x] SplitRecOne = PRest PNil
mergeSort'IsPerm f (lefts ++ rights) (SplitRecPair lrec rrec) =
  let
    leftSubperm = mergeSort'IsPerm f lefts lrec
    rightSubperm = mergeSort'IsPerm f rights rrec
    mergePerm = mergeIsPerm f (mergeSort' f lefts lrec) (mergeSort' f rights rrec)
    concatPerm = permConcat leftSubperm rightSubperm
  in PTrans mergePerm concatPerm

mergeSortIsPerm : (f : Order a) -> (xs : List a) -> Perm (mergeSort f xs) xs
mergeSortIsPerm f xs = mergeSort'IsPerm f xs (splitRec xs)

-- Merge produces an ordered list

mutual
  mergeIsOrdered_single_x : (ftotal : Totality f) ->
                            (x : a) -> (f_y_x : So (f y x)) ->
                            (ysinc : OrderedList f (y :: ys)) ->
                            OrderedList f (y :: (merge f [x] ys))
  mergeIsOrdered_single_x {f} _ x f_y_x (SingleList y) = ConsOrderedList f y (SingleList x)
  mergeIsOrdered_single_x {f} {ys = y1 :: ys} ftotal x f_y_x (ConsOrderedList f y0 yrest) with (mergeIsOrdered ftotal (SingleList x) yrest)
    | rest with (choose $ x `f` y1)
      | Left _  = ConsOrderedList f y0 rest
      | Right _ = ConsOrderedList f y0 rest

  mergeIsOrdered_x0_leq_y : (ftotal : Totality f) ->
                            (x0_f_y : So (x0 `f` y)) -> (x0_f_x1 : So (x0 `f` x1)) ->
                            (xrest : OrderedList f (x1 :: xs)) -> (ysinc : OrderedList f (y :: ys)) ->
                            OrderedList f (x0 :: merge f (x1 :: xs) (y :: ys))
  mergeIsOrdered_x0_leq_y {f} {x1} {y} {x0} ftotal x0_f_y x0_f_x1 xrest ysinc with (mergeIsOrdered ftotal xrest ysinc)
    | rest with (choose $ x1 `f` y)
      | Left _  = ConsOrderedList f x0 rest
      | Right _ = ConsOrderedList f x0 rest

  mergeIsOrdered_x0_geq_y : (ftotal : Totality f) ->
                            (y_f_x0 : So (y0 `f` x0)) ->
                            (xsinc : OrderedList f (x0 :: xs)) -> (ysinc : OrderedList f (y0 :: ys)) ->
                            OrderedList f (y0 :: merge f (x0 :: xs) ys)
  mergeIsOrdered_x0_geq_y {f} ftotal y_f_x0 xsinc (SingleList y0) = ConsOrderedList f y0 xsinc
  mergeIsOrdered_x0_geq_y {x0} ftotal y_f_x0 xsinc (ConsOrderedList {prf} {x1} f y0 yrest) with (mergeIsOrdered ftotal xsinc yrest)
    | rest with (choose $ x0 `f` x1)
      | Left _  = ConsOrderedList f y0 rest
      | Right _ = ConsOrderedList f y0 rest

  mergeIsOrdered : (ftotal : Totality f) ->
                   (xsinc : OrderedList f xs) ->
                   (ysinc : OrderedList f ys) ->
                   OrderedList f (merge f xs ys)
  mergeIsOrdered {f} {xs = []} {ys} _ _ ysinc = rewrite mergeLeftEmptyId f ys in ysinc
  mergeIsOrdered {f} {xs} {ys = []} _ xsinc _ = xsinc
  mergeIsOrdered {f} {xs = [x]} {ys = y :: ys} ftotal (SingleList x) ysinc with (choose $ x `f` y)
    | Left _          = ConsOrderedList f x ysinc
    | Right not_f_x_y = mergeIsOrdered_single_x ftotal x (ftotal not_f_x_y) ysinc
  mergeIsOrdered {f} {xs = x0 :: x1 :: xs} {ys = y :: ys} ftotal (ConsOrderedList {prf} f x0 xrest) ysinc with (choose $ x0 `f` y)
    | Left x0_f_y       = mergeIsOrdered_x0_leq_y ftotal x0_f_y prf xrest ysinc
    | Right not_x0_f_y  = mergeIsOrdered_x0_geq_y ftotal (ftotal not_x0_f_y) (ConsOrderedList f x0 xrest) ysinc

mergeSort'IsOrdered : (f : Order a) -> (ftotal : Totality f) -> (xs : List a) -> (s : SplitRec xs) -> OrderedList f (mergeSort' f xs s)
mergeSort'IsOrdered f ftotal [] SplitRecNil = EmptyList
mergeSort'IsOrdered f ftotal [x] SplitRecOne = SingleList x
mergeSort'IsOrdered f ftotal (lefts ++ rights) (SplitRecPair lrec rrec) =
    let lInc = mergeSort'IsOrdered f ftotal lefts lrec
        rInc = mergeSort'IsOrdered f ftotal rights rrec
    in mergeIsOrdered ftotal lInc rInc

mergeSortIsOrdered : (f : Order a) -> (ftotal : Totality f) -> (xs : List a) -> OrderedList f (mergeSort f xs)
mergeSortIsOrdered f ftotal xs = mergeSort'IsOrdered f ftotal xs (splitRec xs)

mergeSortIsASort : (f : Order a) -> (ftotal : Totality f) -> (xs : List a) -> Sorted f xs (mergeSort f xs)
mergeSortIsASort f ftotal xs = MkSorted (mergeSortIsPerm f xs) (mergeSortIsOrdered f ftotal xs)
