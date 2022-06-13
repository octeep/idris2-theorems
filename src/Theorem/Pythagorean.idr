module Theorem.Pythagorean

import Theorem.Division
import Theorem.ZZ
import Theorem.Basic
import Theorem.Nat
import Data.Nat
import Data.Nat.Factor

%default total

public export
data PrimPythTripleN : Nat -> Nat -> Nat -> Type where
  MkPythTripleN : {a, b, c : Nat} ->
                  (a * a) + (b * b) = (c * c) ->
                  NonZero a -> NonZero b ->
                  PrimPythTripleN a b c

public export
data GCD3 : Nat -> Nat -> Nat -> Nat -> Type where
  MkGCD3 : GCD p a b -> GCD q p c -> GCD3 q a b c

minus_add_inv : (a, b : Nat) -> a `LTE` b -> (minus b a) + a = b
minus_add_inv Z b prf =
  rewrite minusZeroRight b in plusZeroRightNeutral b
minus_add_inv (S a) (S b) (LTESucc prf) =
  rewrite sym $ plusSuccRightSucc (minus b a) a in cong S $ minus_add_inv a b prf

data PrimPythTripeNGen : PrimPythTripleN a b c -> Nat -> Nat -> Type where
  MkPPTG : (t : PrimPythTripleN a b c) ->
           NonZero n ->
           m `GT` n ->
           a = m * m `minus` n * n ->
           b = 2 * m * n ->
           c = m * m + n * n ->
           PrimPythTripeNGen t m n


public export
reduceTripleToGen : (t : PrimPythTripleN a b c) -> GCD3 1 a b c -> PrimPythTripeNGen t m n
reduceTripleToGen (MkPythTripleN {a,b,c} eqn aNZ bNZ) _ =
  let
    eqn0 = trans (sym $ minusPlus (a * a)) $ cong (\x => minus x (a * a)) eqn
  in
    ?awee
