module OrderedList

import Data.So

import Order

%default total
%access public export

data OrderedList : (f : Order a) -> (xs : List a) -> Type where
  EmptyList       : OrderedList f []
  SingleList      : (x : a) -> OrderedList f [x]
  ConsOrderedList : (f : Order a) -> (x0 : a) -> {auto prf : So (x0 `f` x1)} -> (rest : OrderedList f (x1 :: xs)) -> OrderedList f (x0 :: x1 :: xs)

%name OrderedList xsinc, ysinc, zsinc
