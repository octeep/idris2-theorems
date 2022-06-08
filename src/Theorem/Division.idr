module Theorem.Division

import Data.Nat
import Theorem.Nat
import Theorem.Integer
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
commonFactorDivSum  : {d,a,b : _} -> CommonFactor d a b -> Factor d (a + b)
commonFactorDivSum (CommonFactorExists factorA factorB) =
  let
    CofactorExists {k=p} prfA = factorA
    CofactorExists {k=q} prfB = factorB
    prfAB = the (mult d (a + b) = mult d (a + b)) Refl
  in
    ?what prfA prfB prfAB

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

reduceToLTE : {n,m,k : _} -> PS (plus (plus (mult n k) n) k) = PS m -> LTE n m
reduceToLTE = lteAddLeft' . plusEqToLTE . injective

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

euclidLemmaPositive : (n, a, b: Nat) -> Coprime (PS n) (PS a) -> Factor (PS n) (PS a * PS b) -> Factor (PS n) (PS b)
euclidLemmaPositive n a b coprimePrf nDividesAB =
  case decEq n a of
       Yes prf =>
          let nIsOne = selfGCDMustBeSelf $ replace {p = GCD 1 (PS n) . PS} (sym prf) coprimePrf
          in rewrite sym nIsOne in oneIsFactor
       No prf => ?what1 prf
