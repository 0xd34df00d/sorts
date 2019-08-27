module Perm

import Data.List

%default total
%access public export

infixr 6 ~~
data (~~) : (xs : List a) -> (pxs : List a) -> Type where
  PNil    : [] ~~ []
  PSwap   : x0 :: x1 :: xs ~~ x1 :: x0 :: xs
  PRest   : (rest : xs ~~ pxs) -> x :: xs ~~ x :: pxs
  PTrans  : (p1 : xs ~~ pxs) -> (p2 : pxs ~~ ppxs) -> xs ~~ ppxs

%name (~~) p, p1, p2

permRefl : (xs : List a) -> xs ~~ xs
permRefl [] = PNil
permRefl (x :: xs) = PRest $ permRefl xs

permSym : xs ~~ ys -> ys ~~ xs
permSym PNil = PNil
permSym PSwap = PSwap
permSym (PRest rest) = PRest (permSym rest)
permSym (PTrans p1 p2) = let p1' = permSym p1
                             p2' = permSym p2
                         in PTrans p2' p1'

permTrans : xs ~~ ys -> ys ~~ zs -> xs ~~ zs
permTrans x y = PTrans x y

nilPerm : xs ~~ [] -> xs = []
nilPerm PNil = Refl
nilPerm (PTrans p1 p2) = case nilPerm p2 of Refl => nilPerm p1

permSingleton : xs ~~ [x] -> xs = [x]
permSingleton (PRest rest) = rewrite nilPerm rest in Refl
permSingleton (PTrans p1 p2) = case permSingleton p2 of Refl => permSingleton p1

permPreservesElem : xs ~~ ys -> (elPrf : Elem elt xs) -> Elem elt ys
permPreservesElem PNil x = x
permPreservesElem PSwap Here = There Here
permPreservesElem PSwap (There Here) = Here
permPreservesElem PSwap (There (There later)) = There (There later)
permPreservesElem (PRest rest) Here = Here
permPreservesElem (PRest rest) (There later) = There (permPreservesElem rest later)
permPreservesElem (PTrans p1 p2) elPrf = permPreservesElem p2 $ permPreservesElem p1 elPrf

permHeadElem : DecEq a => (x : a) -> (xs, ys : List a) -> x :: xs ~~ ys -> Elem x ys
permHeadElem x xs ys p = permPreservesElem p Here

permTail : (tail : List a) -> xs ~~ ys -> xs ++ tail ~~ ys ++ tail
permTail tail PNil = permRefl tail
permTail tail PSwap = PSwap
permTail tail (PRest rest) = PRest $ permTail tail rest
permTail tail (PTrans p1 p2) = let rec1 = permTail tail p1
                                   rec2 = permTail tail p2
                               in PTrans rec1 rec2

permHeadLast : (y : a) -> (xs : List a) -> y :: xs ~~ xs ++ [y]
permHeadLast y [] = PRest PNil
permHeadLast y (x :: xs) = let rec = permHeadLast y xs
                               x_y_xs = PRest {x} rec
                               swapped = PSwap {x0 = y} {x1 = x} {xs}
                           in PTrans swapped x_y_xs

permSwapMid : (y : a) -> (xs, ys : List a) -> y :: xs ++ ys ~~ xs ++ y :: ys
permSwapMid y xs ys = let headLast = permHeadLast y xs
                      in rewrite appendAssociative xs [y] ys
                      in permTail ys headLast

permHead : (x : a) -> xs ~~ pxs -> x :: xs ~~ x :: pxs
permHead x PNil = PRest PNil
permHead x PSwap = PRest PSwap
permHead x (PRest rest) = PRest (PRest rest)
permHead x (PTrans p1 p2) = PRest (PTrans p1 p2)

permPrepend : (xs : List a) -> ys ~~ pys -> xs ++ ys ~~ xs ++ pys
permPrepend [] p = p
permPrepend (x :: xs) p = permHead x $ permPrepend xs p

permConcat : xs ~~ pxs -> ys ~~ pys -> xs ++ ys ~~ pxs ++ pys
permConcat {xs} {pys} p1 p2 = permPrepend xs p2 `PTrans` permTail pys p1
