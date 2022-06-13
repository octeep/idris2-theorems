module Theorem.Finite

import Theorem.ZZ
import Data.Fin
import Data.Nat

%default total

complement_is_neg : (a : Fin (S n)) -> a + complement a = FZ

mod : ZZ -> (n : Nat) -> {auto modNotZero : NonZero n} -> Fin n
mod n (S m) = ?a
