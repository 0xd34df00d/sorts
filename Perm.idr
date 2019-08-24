module Perm

import Data.List

%default total
%access public export

data Perm : (xs : List a) -> (pxs : List a) -> Type where
  PNil    : Perm [] []
  PSwap   : Perm (x0 :: x1 :: xs) (x1 :: x0 :: xs)
  PRest   : (rest : Perm xs pxs) -> Perm (x :: xs) (x :: pxs)
  PTrans  : (p1 : Perm xs pxs) -> (p2 : Perm pxs ppxs) -> Perm xs ppxs

%name Perm p, p1, p2

permRefl : (xs : List a) -> Perm xs xs
permRefl [] = PNil
permRefl (x :: xs) = PRest $ permRefl xs

permSym : Perm xs ys -> Perm ys xs
permSym PNil = PNil
permSym PSwap = PSwap
permSym (PRest rest) = PRest (permSym rest)
permSym (PTrans p1 p2) = let p1' = permSym p1
                             p2' = permSym p2
                         in PTrans p2' p1'

permTrans : Perm xs ys -> Perm ys zs -> Perm xs zs
permTrans x y = PTrans x y

nilPerm : Perm xs [] -> xs = []
nilPerm PNil = Refl
nilPerm (PTrans p1 p2) = case nilPerm p2 of Refl => nilPerm p1

permSingleton : Perm xs [x] -> xs = [x]
permSingleton (PRest rest) = rewrite nilPerm rest in Refl
permSingleton (PTrans p1 p2) = case permSingleton p2 of Refl => permSingleton p1

permPreservesElem : Perm xs ys -> (elPrf : Elem elt xs) -> Elem elt ys
permPreservesElem PNil x = x
permPreservesElem PSwap Here = There Here
permPreservesElem PSwap (There Here) = Here
permPreservesElem PSwap (There (There later)) = There (There later)
permPreservesElem (PRest rest) Here = Here
permPreservesElem (PRest rest) (There later) = There (permPreservesElem rest later)
permPreservesElem (PTrans p1 p2) elPrf = permPreservesElem p2 $ permPreservesElem p1 elPrf
