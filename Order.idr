module Order

import Data.So

%access public export
%default total

Order : Type -> Type
Order a = a -> a -> Bool

Totality : Order a -> Type
Totality {a} f = {x_t, y_t : a} -> So (not (x_t `f` y_t)) -> So (y_t `f` x_t)
