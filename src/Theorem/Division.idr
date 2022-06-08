module Theorem.Division

import Data.Nat
import Theorem.Nat
import Theorem.ZZ
import Control.Relation
import Decidable.Equality

public export
data Factor : ZZ -> ZZ -> Type where
  CofactorExists : {a, k, n : ZZ} -> (a * k = n) -> Factor a n

public export
oneIsFactor : {n : ZZ} -> Factor 1 n
oneIsFactor {n} = CofactorExists $ multOneLeftNeutralZ n

public export
negOneIsFactor : {n : ZZ} -> Factor (-1) n
negOneIsFactor {n} =
  CofactorExists {k=(negate n), a=(-1)} $
  rewrite multNegateCancelZ 1 n in multOneLeftNeutralZ n

public export
selfIsFactor : {n : ZZ} -> Factor n n
selfIsFactor {n} = CofactorExists {a = n, k = 1} (multOneRightNeutralZ n)

public export
data CommonFactor : ZZ -> ZZ -> ZZ -> Type where
  CommonFactorExists : Factor p a -> Factor p b -> CommonFactor p a b

public export
commonFactorDivSum  : {d,a,b : _} -> CommonFactor d a b -> Factor d (a + b)
commonFactorDivSum (CommonFactorExists factorA factorB) =
  let
    CofactorExists {k=p} prfA = factorA
    CofactorExists {k=q} prfB = factorB
    prfAB = cong2 (+) prfA prfB
  in
    CofactorExists $ trans (multDistributesOverPlusRightZ d p q) prfAB

public export
data GCD : Nat -> ZZ -> ZZ -> Type where
  MkGCD : {auto notBothZero : NotBothZero a b} ->
          (CommonFactor (cast p) a b) ->
          ((q : ZZ) -> CommonFactor q a b -> Factor q (cast p)) ->
          GCD p a b

public export
Uninhabited (Factor 0 (Pos (S n))) where
  uninhabited (CofactorExists prf) impossible

{-
public export
Uninhabited (Factor 0 (NegS n)) where
  uninhabited (CofactorExists prf) = ?ww prf
  -}

reduceToLTE : {n,m,k : _} -> Pos (S (plus k (mult n (S k)))) = Pos (S m) -> LTE n m
reduceToLTE eq =
  lteAddLeft
  $ replace {p = (\x => LTE x m)} (multRightSuccPlus n k)
  $ plusEqToLTE
  $ the (plus (mult n (S k)) k = m)
  $ rewrite plusCommutative (mult n (S k)) k in
  injective $ injective eq

public export
selfGCDMustBeSelf : {n,m :_} -> GCD (S n) (Pos $ S m) (Pos $ S m) -> n = m
selfGCDMustBeSelf {n,m} gcd@(MkGCD cfPrf factorWit) =
  let
    CommonFactorExists (CofactorExists {k=Pos k1} nFactorOfM) _ = cfPrf
    CofactorExists {k=Pos k2} mFactorOfN = factorWit (Pos $ S m) (CommonFactorExists selfIsFactor selfIsFactor)
  in case k1 of
    S _ => case k2 of
      S _ => antisymmetric (reduceToLTE nFactorOfM) (reduceToLTE mFactorOfN)
      Z => absurd $ multNotZero m n (injective mFactorOfN)
    Z => absurd $ multNotZero n m (injective nFactorOfM)

public export
Coprime : ZZ -> ZZ -> Type
Coprime = GCD 1

euclidLemmaPositive : (n, a, b: Nat) ->
                      Coprime (Pos $ S n) (Pos $ S a) ->
                      Factor (Pos $ S n) ((Pos $ S a) * (Pos $ S b)) ->
                      Factor (Pos $ S n) (Pos $ S b)
euclidLemmaPositive n a b coprimePrf nDividesAB =
  case decEq n a of
       Yes prf =>
          let nIsOne = selfGCDMustBeSelf $ replace {p = GCD 1 (Pos $ S n) . Pos . S} (sym prf) coprimePrf
          in rewrite sym nIsOne in oneIsFactor
       No prf => ?what1 prf
