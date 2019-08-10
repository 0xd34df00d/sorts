module Merge

import Data.List.Views
import Data.So

import Order

%hide merge
%default total

merge : (f : Order a) -> (xs, ys : List a) -> List a
merge f xs [] = xs
merge f [] ys = ys
merge f (x :: xs) (y :: ys) = case choose $ x `f` y of
                                   Left _   => x :: merge f xs (y :: ys)
                                   Right _  => y :: merge f (x :: xs) ys
