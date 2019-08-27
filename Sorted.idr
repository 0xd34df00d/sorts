module Sorted

import Order
import OrderedList
import Perm

%default total
%access public export

data Sorted : (f : Order a) -> (orig : List a) -> (sorted : List a) -> Type where
  MkSorted : (permPrf : sorted ~~ orig) -> (ordPrf : OrderedList f sorted) -> Sorted f orig sorted
