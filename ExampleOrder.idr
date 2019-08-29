module ExampleOrder

import Data.So

import Order

%default total

natCmp : Nat -> Nat -> Bool
natCmp m n = decAsBool $ isLTE m n

notLte : (m, n : Nat) -> (contra : LTE m n -> Void) -> LTE n m
notLte Z n contra = absurd $ contra LTEZero
notLte (S k) Z contra = LTEZero
notLte (S k) (S j) contra = let rec = notLte k j (\lteArg => contra (LTESucc lteArg)) in LTESucc rec

natCmpTotal : Totality ExampleOrder.natCmp
natCmpTotal = impl
  where
    impl : {x_t, y_t : Nat} -> So (not (x_t `natCmp` y_t)) -> So (y_t `natCmp` x_t)
    impl {x_t} {y_t} notLeq with (isLTE x_t y_t)
      | Yes _ = absurd notLeq
      | No contra with (isLTE y_t x_t)
        | Yes _ = notLeq
        | No contra' = let prf = notLte _ _ contra' in void $ contra prf
