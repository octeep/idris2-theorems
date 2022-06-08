module Theorem.Nat

import Data.Nat
import Control.Function

public export
lteAddLeft : {a,b,c : _} -> LTE (a + b) c -> LTE a c
lteAddLeft {b=Z} eq =
  replace {p=(\x => LTE x c)} (plusZeroRightNeutral a) eq
lteAddLeft {b=(S n)} eq =
  lteAddLeft
  $ replace {p=(\x => LTE x c)} (plusCommutative n a)
  $ lteSuccLeft
  $ replace {p=(\x => LTE x c)} (plusCommutative a (S n)) eq

public export
plusEqToLTE : {a,b,c : _} -> a + b = c -> LTE a c
plusEqToLTE eq = rewrite sym eq in lteAddRight {m=b} a

public export
lteAddLeft' : {a,b,c : _} -> LTE (b + a) c -> LTE a c
lteAddLeft' eq = lteAddLeft $ replace {p=(\x => LTE x c)} (plusCommutative b a) eq
