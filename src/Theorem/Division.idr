module Theorem.Division

import Data.Nat
import Theorem.Nat
import Theorem.ZZ
import Control.Relation
import Decidable.Equality
import Data.Either

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
isFactorOfZero : {n : ZZ} -> Factor n 0
isFactorOfZero = CofactorExists {a=n,k=0} $ multZeroRightZeroZ n

public export
zeroFactorMustBeZero : {n : ZZ} -> Factor 0 n -> n = 0
zeroFactorMustBeZero (CofactorExists {k} prf) = trans (sym prf) (multZeroLeftZeroZ k)

public export
selfIsFactor : {n : ZZ} -> Factor n n
selfIsFactor {n} = CofactorExists {a = n, k = 1} (multOneRightNeutralZ n)

public export
data CommonFactor : ZZ -> ZZ -> ZZ -> Type where
  CommonFactorExists : Factor p a -> Factor p b -> CommonFactor p a b

public export
commonFactorFlip : CommonFactor p a b -> CommonFactor p b a
commonFactorFlip (CommonFactorExists prf1 prf2) = CommonFactorExists prf2 prf1

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
factorDividesNeg : Factor p n -> Factor p (-n)
factorDividesNeg (CofactorExists {a,k,n} prf) = CofactorExists {k=(-k),n=(-n)} $
  rewrite multNegateRightZ a k in cong negate prf

public export
factorNegIsFactor : {p : _} -> Factor p n -> Factor (-p) n
factorNegIsFactor (CofactorExists {k=q} prf) = CofactorExists $ trans (multNegateCancelZ p q) prf

public export
commonFactorDivDiff  : {d,a,b : _} -> CommonFactor d a b -> Factor d (a - b)
commonFactorDivDiff (CommonFactorExists prfA prfB) =
  commonFactorDivSum {b=(-b)}
  $ CommonFactorExists prfA
  $ factorDividesNeg prfB

public export
data GCD : Nat -> ZZ -> ZZ -> Type where
  MkGCD : {auto notBothZero : NotBothZero a b} ->
          (CommonFactor (cast p) a b) ->
          ((q : ZZ) -> CommonFactor q a b -> Factor q (cast p)) ->
          GCD p a b

public export
gcdFlip : GCD p a b -> GCD p b a
gcdFlip (MkGCD {notBothZero} crPrf wit) =
  MkGCD {notBothZero = mirror notBothZero} (commonFactorFlip crPrf) (\q,w => wit q $ commonFactorFlip w)

public export
gcdABIsGcdANegB : {b : _} -> GCD p a b -> GCD p a (-b)
gcdABIsGcdANegB (MkGCD {notBothZero} cfPrf wit) =
  MkGCD {notBothZero=map notZeroFlip notBothZero}
    (cfDividesNeg cfPrf)
    (\q,f => wit q $ replace {p = CommonFactor q a} (doubleNegElim b) $ cfDividesNeg f)
  where
    cfDividesNeg : CommonFactor f n m -> CommonFactor f n (-m)
    cfDividesNeg (CommonFactorExists a b) = CommonFactorExists a (factorDividesNeg b)
    notZeroFlip : {b : _} -> NotZero b -> NotZero (negate b)
    notZeroFlip NIsNotZero = PIsNotZero
    notZeroFlip PIsNotZero = NIsNotZero

public export
gcdABIsGcdNegAB : {a,b : _} -> GCD p a b -> GCD p (-a) b
gcdABIsGcdNegAB = gcdFlip . gcdABIsGcdANegB . gcdFlip

public export
gcdABIsGcdASubB : {p : _} -> {a,n : _} -> GCD p (Pos (S n)) (Pos (S a)) -> GCD p (Pos (S n)) (minusNatZ a n)
gcdABIsGcdASubB gcd =
  let
    MkGCD cfProof@(CommonFactorExists prfA prfB) wit = gcdABIsGcdANegB gcd
    eq = minusNatZAntiCommutative n a
  in
    replace {p = GCD p (Pos (S n))} eq
    $ gcdABIsGcdANegB
    $ MkGCD (CommonFactorExists prfA
    $ commonFactorDivSum cfProof) (\q,cf => wit q $ cfChange cf)
  where
    cfChange : {q:_} -> CommonFactor q (Pos (S n)) (minusNatZ n a) -> CommonFactor q (Pos (S n)) (NegS a)
    cfChange prfCD@(CommonFactorExists prfC prfD) =
      let
        tEq = the (plusZ (Pos (S n)) (negate (minusNatZ n a)) = Pos (S a)) $
          rewrite negateDistributesPlus (Pos $ S n) (NegS a) in
          rewrite plusAssociativeZ (Pos $ S n) (negate $ Pos $ S n) (Pos $ S a) in
          rewrite lemmaMinusSymmZero n in
          Refl
      in
        CommonFactorExists prfC (factorDividesNeg $ replace {p = Factor q} tEq $ commonFactorDivDiff prfCD)

public export
Uninhabited (Factor 0 (Pos (S n))) where
  uninhabited (CofactorExists prf) impossible

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
gcdZeroMustBeSelf : {n,m : _} -> GCD (S n) (Pos $ S m) 0 -> n = m
gcdZeroMustBeSelf {n,m} (MkGCD cfPrf@(CommonFactorExists prfA prfB) factorWit) =
  selfGCDMustBeSelf $
  MkGCD
  (CommonFactorExists prfA $ rewrite sym $ plusZeroRightNeutral m in commonFactorDivSum cfPrf)
  (\q,(CommonFactorExists prfC _) => factorWit q $ CommonFactorExists prfC isFactorOfZero)

public export
{a,b : _} -> Uninhabited (GCD 0 a b) where
  uninhabited (MkGCD {notBothZero} (CommonFactorExists prfA prfB) factorWit) =
    case notBothZero of
      Left  prf => uninhabited $ replace {p = NotZero} (zeroFactorMustBeZero prfA) prf
      Right prf => uninhabited $ replace {p = NotZero} (zeroFactorMustBeZero prfB) prf

public export
Coprime : ZZ -> ZZ -> Type
Coprime = GCD 1

mutual
  euclidLemmaPositive : (n, a, b: Nat) ->
                        Coprime (Pos $ S n) (Pos $ S a) ->
                        Factor (Pos $ S n) ((Pos $ S a) * (Pos $ S b)) ->
                        Factor (Pos $ S n) (Pos $ S b)
  euclidLemmaPositive n a b coprimePrf nDividesAB =
    case decEq n a of
         Yes prf =>
            let nIsOne = selfGCDMustBeSelf $ replace {p = GCD 1 (Pos $ S n) . Pos . S} (sym prf) coprimePrf
            in rewrite sym nIsOne in oneIsFactor
         No prf =>
            let
              CofactorExists {k=q} nqab = nDividesAB
              amog = multDistributesOverPlusRightZ (Pos $ S n) q (-(Pos $ S b))
              us = cong (\x => x - ((Pos $ S n) * (Pos $ S b))) nqab
              impo = multDistributesOverPlusLeftZ (Pos $ S a) (NegS n) (Pos $ S b)
              step = sym $ trans impo $ sym $ trans amog us
              factor = CofactorExists step
            in
              euclidLemma (Pos $ S n) (minusNatZ a n) (Pos $ S b) (gcdABIsGcdASubB coprimePrf) factor

  public export
  euclidLemma : (n, a, b : _) -> Coprime n a -> Factor n (a * b) -> Factor n b
  euclidLemma (Pos $ S n) (Pos $ S a) (Pos $ S b) coprime factor =
    euclidLemmaPositive n a b coprime factor
  euclidLemma n a (NegS b) coprime factor =
    factorDividesNeg
    $ euclidLemma n a (Pos $ S b) coprime
    $ replace {p = Factor n} (sym $ multNegateRightZ a $ NegS b)
    $ factorDividesNeg factor
  euclidLemma n (NegS a) b coprime factor =
    euclidLemma n (Pos $ S a) b (gcdABIsGcdANegB coprime)
    $ replace {p = Factor n} (sym $ multNegateLeftZ (NegS a) b)
    $ factorDividesNeg factor
  euclidLemma (NegS n) a b coprime factor =
    factorNegIsFactor
    $ euclidLemma (Pos $ S n) a b (gcdABIsGcdNegAB coprime) (factorNegIsFactor factor)
  euclidLemma n a (Pos 0) coprime factor =
    isFactorOfZero
  euclidLemma (Pos $ S n) (Pos 0) b coprime factor =
    rewrite sym $ cong S $ gcdZeroMustBeSelf coprime in oneIsFactor
  euclidLemma (Pos 0) (Pos a) (Pos b) coprime factor =
    case (coprime, factor) of
      (MkGCD {notBothZero = Right aNotZero} _ _, CofactorExists {k} prf) =>
        case a of
          Z => absurd aNotZero
          S a' =>
            let
              bIsZero =
                productZeroInfersZero b a'
                  $ trans (sym $ multCommutative a b)
                  $ injective
                  $ trans (sym prf) (multZeroLeftZeroZ k)
            in
              rewrite bIsZero in isFactorOfZero
