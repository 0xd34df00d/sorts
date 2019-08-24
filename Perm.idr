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
