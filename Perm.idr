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
