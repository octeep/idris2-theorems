module Theorem.Division

import Data.Nat
import Theorem.Integer
import Control.Function
import Control.Relation
import Decidable.Equality

public export
data NotZero : ZZ -> Type where
  PIsNotZero : NotZero (PS x)
  NIsNotZero : NotZero (NS x)

public export
NotBothZero : ZZ -> ZZ -> Type
NotBothZero a b = Either (NotZero a) (NotZero b)

public export
data Factor : ZZ -> ZZ -> Type where
  CofactorExists : {a, k, n : ZZ} -> (a * k = n) -> Factor a n

public export
oneIsFactor : {n : ZZ} -> Factor 1 n
oneIsFactor {n = PS m} = CofactorExists {k=PS m} Refl
oneIsFactor {n = NS m} = CofactorExists {k=NS m} Refl
oneIsFactor {n = Z} = CofactorExists {k=Z} Refl

public export
negOneIsFactor : {n : ZZ} -> Factor (-1) n
negOneIsFactor {n = PS m} = CofactorExists {k=NS m} Refl
negOneIsFactor {n = NS m} = CofactorExists {k=PS m} Refl
negOneIsFactor {n = Z} = CofactorExists {k=Z} Refl

public export
selfIsFactor : {n : ZZ} -> Factor n n
selfIsFactor {n} = CofactorExists {a = n, k = 1} (multOneRightNetural n)

public export
data CommonFactor : ZZ -> ZZ -> ZZ -> Type where
  CommonFactorExists : Factor p a -> Factor p b -> CommonFactor p a b

public export
subsetFactorDivides : ((q : ZZ) -> Factor q a -> Factor q b) -> Factor a b

public export
data GCD : Nat -> ZZ -> ZZ -> Type where
  MkGCD : {auto notBothZero : NotBothZero a b} ->
          (CommonFactor (cast p) a b) ->
          ((q : ZZ) -> CommonFactor q a b -> Factor q (cast p)) ->
          GCD p a b

public export
Uninhabited (Factor Z (PS n)) where
  uninhabited (CofactorExists prf) impossible

public export
Uninhabited (Factor Z (NS n)) where
  uninhabited (CofactorExists prf) impossible

lteAddLeft : {a,b,c : _} -> LTE (a + b) c -> LTE a c
lteAddLeft {b=Z} eq =
  replace {p=(\x => LTE x c)} (plusZeroRightNeutral a) eq
lteAddLeft {b=(S n)} eq =
  lteAddLeft
  $ replace {p=(\x => LTE x c)} (plusCommutative n a)
  $ lteSuccLeft
  $ replace {p=(\x => LTE x c)} (plusCommutative a (S n)) eq

plusLTE : {a,b,c : _} -> a + b = c -> LTE a c
plusLTE eq = rewrite sym eq in lteAddRight {m=b} a

multLTE : {n,m,k : _} -> LTE (mult n (S k)) m -> LTE n m
multLTE eq = lteAddLeft $
  replace {p=(\x => LTE x m)} (multRightSuccPlus n k) eq

plusMultCleanup : {a,k : _} -> plus (mult a k) a = mult a (S k)
plusMultCleanup =
  rewrite plusCommutative (mult a k) a in
    rewrite sym $ multRightSuccPlus a k in
      Refl

ltePlusMultCleanup : {a,b,k : _} -> LTE (plus (mult a k) a) b -> LTE (mult a (S k)) b
ltePlusMultCleanup eq = replace {p = (\x => LTE x b)} plusMultCleanup eq

reduceToLTE : {n,m,k : _} -> PS (plus (plus (mult n k) n) k) = PS m -> LTE n m
reduceToLTE = multLTE . ltePlusMultCleanup . plusLTE . injective

public export
selfGCDMustBeSelf : {n,m :_} -> GCD (S n) (PS m) (PS m) -> n = m
selfGCDMustBeSelf {n,m} (MkGCD cfPrf factorWit) =
  let
    CommonFactorExists (CofactorExists {k=PS k1} nFactorOfM) _ = cfPrf
    CofactorExists {k=PS k2} mFactorOfN = factorWit (PS m) (CommonFactorExists selfIsFactor selfIsFactor)
    prfA = reduceToLTE nFactorOfM
    prfB = reduceToLTE mFactorOfN
  in antisymmetric prfA prfB

public export
Coprime : ZZ -> ZZ -> Type
Coprime = GCD 1

{-
public export
euclidLemma : (n, a, b: ZZ) -> Coprime n a -> Factor n (a * b) -> Factor n b
euclidLemma n a b (MkGCD commonFactorPrf _) nDividesAB =
  case decEq n a of
       Yes prf => rewrite sym prf in selfIsFactor
       No prf => ?what1 prf
