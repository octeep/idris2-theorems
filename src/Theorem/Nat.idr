module Theorem.Nat

import Data.Nat
import Control.Function

%default total

public export
data Even : Nat -> Type where
  ZeroIsEven : Even Z
  SuccIsEven : Even n -> Even (S (S n))

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

public export
lteAddRight' : {a,b,c : _} -> LTE a b -> LTE a (b + c)
lteAddRight' {c=Z} prf = rewrite plusZeroRightNeutral b in prf
lteAddRight' {c=(S n)} prf = rewrite sym $ plusSuccRightSucc b n in lteSuccRight $ lteAddRight' {c=n} prf

public export
multNotZero : (i,j : Nat) -> (i * 0 = S j) -> Void
multNotZero i j prf = uninhabited $ the (0 = S j) $ rewrite sym $ multZeroRightZero i in prf

public export
productZeroInfersZero : (a, b : Nat) -> a * (S b) = 0 -> a = 0
productZeroInfersZero Z _ prf = prf

public export
ltePlusConcatLemma : (a,b,c,d : Nat) -> LTE a b -> LTE c d -> LTE (a + c) (b + d)
ltePlusConcatLemma Z b c d prfAB prfCD = replace {p=LTE c} (plusCommutative d b) $ lteAddRight' prfCD
ltePlusConcatLemma (S a) (S b) c d (LTESucc prfAB) prfCD = LTESucc $ ltePlusConcatLemma a b c d prfAB prfCD

public export
lteMultConcatLemma : (a,b,c,d : Nat) -> LTE a b -> LTE c d -> LTE (a * c) (b * d)
lteMultConcatLemma Z b c d prfAB prfCD = LTEZero
lteMultConcatLemma (S a) (S b) c d (LTESucc prfAB) prfCD =
  ltePlusConcatLemma c d _ _ prfCD (lteMultConcatLemma a b c d prfAB prfCD)

public export
lteSquareLemma : (a, b : Nat) -> LTE a b -> LTE (a * a) (b * b)
lteSquareLemma a b prf = lteMultConcatLemma a b a b prf prf
