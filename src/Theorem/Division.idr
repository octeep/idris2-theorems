module Theorem.Division

import Data.Nat
import Theorem.Nat
import Theorem.ZZ
import Control.Relation
import Decidable.Equality
import Data.Either

%default total

public export
data FactorZZ : ZZ -> ZZ -> Type where
  CofactorExists : {a, k, n : ZZ} -> (a * k = n) -> FactorZZ a n

public export
oneIsFactorZZ : {n : ZZ} -> FactorZZ 1 n
oneIsFactorZZ {n} = CofactorExists $ multOneLeftNeutralZ n

public export
negOneIsFactorZZ : {n : ZZ} -> FactorZZ (-1) n
negOneIsFactorZZ {n} =
  CofactorExists {k=(negate n), a=(-1)} $
  rewrite multNegateCancelZ 1 n in multOneLeftNeutralZ n

public export
isFactorZZOfZero : {n : ZZ} -> FactorZZ n 0
isFactorZZOfZero = CofactorExists {a=n,k=0} $ multZeroRightZeroZ n

public export
zeroFactorZZMustBeZero : {n : ZZ} -> FactorZZ 0 n -> n = 0
zeroFactorZZMustBeZero (CofactorExists {k} prf) = trans (sym prf) (multZeroLeftZeroZ k)

public export
selfIsFactorZZ : {n : ZZ} -> FactorZZ n n
selfIsFactorZZ {n} = CofactorExists {a = n, k = 1} (multOneRightNeutralZ n)

public export
data CommonFactorZZ : ZZ -> ZZ -> ZZ -> Type where
  CommonFactorZZExists : FactorZZ p a -> FactorZZ p b -> CommonFactorZZ p a b

public export
commonFactorZZFlip : CommonFactorZZ p a b -> CommonFactorZZ p b a
commonFactorZZFlip (CommonFactorZZExists prf1 prf2) = CommonFactorZZExists prf2 prf1

public export
commonFactorZZDivSum  : {d,a,b : _} -> CommonFactorZZ d a b -> FactorZZ d (a + b)
commonFactorZZDivSum (CommonFactorZZExists factorA factorB) =
  let
    CofactorExists {k=p} prfA = factorA
    CofactorExists {k=q} prfB = factorB
    prfAB = cong2 (+) prfA prfB
  in
    CofactorExists $ trans (multDistributesOverPlusRightZ d p q) prfAB

public export
factorDividesNeg : FactorZZ p n -> FactorZZ p (-n)
factorDividesNeg (CofactorExists {a,k,n} prf) = CofactorExists {k=(-k),n=(-n)} $
  rewrite multNegateRightZ a k in cong negate prf

public export
factorNegIsFactorZZ : {p : _} -> FactorZZ p n -> FactorZZ (-p) n
factorNegIsFactorZZ (CofactorExists {k=q} prf) = CofactorExists $ trans (multNegateCancelZ p q) prf

public export
commonFactorZZDivDiff  : {d,a,b : _} -> CommonFactorZZ d a b -> FactorZZ d (a - b)
commonFactorZZDivDiff (CommonFactorZZExists prfA prfB) =
  commonFactorZZDivSum {b=(-b)}
  $ CommonFactorZZExists prfA
  $ factorDividesNeg prfB

public export
data GCDZZ : Nat -> ZZ -> ZZ -> Type where
  MkGCDZZ : {auto notBothZero : NotBothZero a b} ->
          (CommonFactorZZ (cast p) a b) ->
          ((q : ZZ) -> CommonFactorZZ q a b -> FactorZZ q (cast p)) ->
          GCDZZ p a b

public export
gcdFlip : GCDZZ p a b -> GCDZZ p b a
gcdFlip (MkGCDZZ {notBothZero} crPrf wit) =
  MkGCDZZ {notBothZero = mirror notBothZero} (commonFactorZZFlip crPrf) (\q,w => wit q $ commonFactorZZFlip w)

public export
gcdABIsGcdANegB : {b : _} -> GCDZZ p a b -> GCDZZ p a (-b)
gcdABIsGcdANegB (MkGCDZZ {notBothZero} cfPrf wit) =
  MkGCDZZ {notBothZero=map notZeroFlip notBothZero}
    (cfDividesNeg cfPrf)
    (\q,f => wit q $ replace {p = CommonFactorZZ q a} (doubleNegElim b) $ cfDividesNeg f)
  where
    cfDividesNeg : CommonFactorZZ f n m -> CommonFactorZZ f n (-m)
    cfDividesNeg (CommonFactorZZExists a b) = CommonFactorZZExists a (factorDividesNeg b)
    notZeroFlip : {b : _} -> NotZero b -> NotZero (negate b)
    notZeroFlip NIsNotZero = PIsNotZero
    notZeroFlip PIsNotZero = NIsNotZero

public export
gcdABIsGcdNegAB : {a,b : _} -> GCDZZ p a b -> GCDZZ p (-a) b
gcdABIsGcdNegAB = gcdFlip . gcdABIsGcdANegB . gcdFlip

public export
gcdABIsGcdASubB : {p : _} -> {a,n : _} -> GCDZZ p (Pos (S n)) (Pos (S a)) -> GCDZZ p (Pos (S n)) (minusNatZ a n)
gcdABIsGcdASubB gcd =
  let
    MkGCDZZ cfProof@(CommonFactorZZExists prfA prfB) wit = gcdABIsGcdANegB gcd
    eq = minusNatZAntiCommutative n a
  in
    replace {p = GCDZZ p (Pos (S n))} eq
    $ gcdABIsGcdANegB
    $ MkGCDZZ (CommonFactorZZExists prfA
    $ commonFactorZZDivSum cfProof) (\q,cf => wit q $ cfChange cf)
  where
    cfChange : {q:_} -> CommonFactorZZ q (Pos (S n)) (minusNatZ n a) -> CommonFactorZZ q (Pos (S n)) (NegS a)
    cfChange prfCD@(CommonFactorZZExists prfC prfD) =
      let
        tEq = the (plusZ (Pos (S n)) (negate (minusNatZ n a)) = Pos (S a)) $
          rewrite negateDistributesPlus (Pos $ S n) (NegS a) in
          rewrite plusAssociativeZ (Pos $ S n) (negate $ Pos $ S n) (Pos $ S a) in
          rewrite lemmaMinusSymmZero n in
          Refl
      in
        CommonFactorZZExists prfC (factorDividesNeg $ replace {p = FactorZZ q} tEq $ commonFactorZZDivDiff prfCD)

public export
Uninhabited (FactorZZ 0 (Pos (S n))) where
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
selfGCDZZMustBeSelf : {n,m :_} -> GCDZZ (S n) (Pos $ S m) (Pos $ S m) -> n = m
selfGCDZZMustBeSelf {n,m} gcd@(MkGCDZZ cfPrf factorWit) =
  let
    CommonFactorZZExists (CofactorExists {k=Pos k1} nFactorZZOfM) _ = cfPrf
    CofactorExists {k=Pos k2} mFactorZZOfN = factorWit (Pos $ S m) (CommonFactorZZExists selfIsFactorZZ selfIsFactorZZ)
  in case k1 of
    S _ => case k2 of
      S _ => antisymmetric (reduceToLTE nFactorZZOfM) (reduceToLTE mFactorZZOfN)
      Z => absurd $ multNotZero m n (injective mFactorZZOfN)
    Z => absurd $ multNotZero n m (injective nFactorZZOfM)

public export
gcdZeroMustBeSelf : {n,m : _} -> GCDZZ (S n) (Pos $ S m) 0 -> n = m
gcdZeroMustBeSelf {n,m} (MkGCDZZ cfPrf@(CommonFactorZZExists prfA prfB) factorWit) =
  selfGCDZZMustBeSelf $
  MkGCDZZ
  (CommonFactorZZExists prfA $ rewrite sym $ plusZeroRightNeutral m in commonFactorZZDivSum cfPrf)
  (\q,(CommonFactorZZExists prfC _) => factorWit q $ CommonFactorZZExists prfC isFactorZZOfZero)

public export
{a,b : _} -> Uninhabited (GCDZZ 0 a b) where
  uninhabited (MkGCDZZ {notBothZero} (CommonFactorZZExists prfA prfB) factorWit) =
    case notBothZero of
      Left  prf => uninhabited $ replace {p = NotZero} (zeroFactorZZMustBeZero prfA) prf
      Right prf => uninhabited $ replace {p = NotZero} (zeroFactorZZMustBeZero prfB) prf

public export
Coprime : ZZ -> ZZ -> Type
Coprime = GCDZZ 1

mutual
  euclidLemmaPositive : (n, a, b: Nat) ->
                        Coprime (Pos $ S n) (Pos $ S a) ->
                        FactorZZ (Pos $ S n) ((Pos $ S a) * (Pos $ S b)) ->
                        FactorZZ (Pos $ S n) (Pos $ S b)
  euclidLemmaPositive n a b coprimePrf nDividesAB =
    case decEq n a of
         Yes prf =>
            let nIsOne = selfGCDZZMustBeSelf $ replace {p = GCDZZ 1 (Pos $ S n) . Pos . S} (sym prf) coprimePrf
            in rewrite sym nIsOne in oneIsFactorZZ
         No prf =>
            let
              CofactorExists {k=q} nqab = nDividesAB
              amog = multDistributesOverPlusRightZ (Pos $ S n) q (-(Pos $ S b))
              us = cong (\x => x - ((Pos $ S n) * (Pos $ S b))) nqab
              impo = multDistributesOverPlusLeftZ (Pos $ S a) (NegS n) (Pos $ S b)
              step = sym $ trans impo $ sym $ trans amog us
              factor = CofactorExists step
            in
              euclidLemma (Pos $ S n) (assert_smaller a $ minusNatZ a n) (Pos $ S b) (gcdABIsGcdASubB coprimePrf) factor

  public export
  euclidLemma : (n, a, b : _) -> Coprime n a -> FactorZZ n (a * b) -> FactorZZ n b
  euclidLemma (Pos $ S n) (Pos $ S a) (Pos $ S b) coprime factor =
    euclidLemmaPositive n a b coprime factor
  euclidLemma n a (NegS b) coprime factor =
    factorDividesNeg
    $ euclidLemma n a (assert_smaller (NegS b) $ Pos $ S b) coprime
    $ replace {p = FactorZZ n} (sym $ multNegateRightZ a $ NegS b)
    $ factorDividesNeg factor
  euclidLemma n (NegS a) b coprime factor =
    euclidLemma n (assert_smaller (NegS a) $ Pos $ S a) b (gcdABIsGcdANegB coprime)
    $ replace {p = FactorZZ n} (sym $ multNegateLeftZ (NegS a) b)
    $ factorDividesNeg factor
  euclidLemma (NegS n) a b coprime factor =
    factorNegIsFactorZZ
    $ euclidLemma (Pos $ S n) a b (gcdABIsGcdNegAB coprime) (factorNegIsFactorZZ factor)
  euclidLemma n a (Pos 0) coprime factor =
    isFactorZZOfZero
  euclidLemma (Pos $ S n) (Pos 0) b coprime factor =
    rewrite sym $ cong S $ gcdZeroMustBeSelf coprime in oneIsFactorZZ
  euclidLemma (Pos 0) (Pos a) (Pos b) coprime factor =
    case (coprime, factor) of
      (MkGCDZZ {notBothZero = Right aNotZero} _ _, CofactorExists {k} prf) =>
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
              rewrite bIsZero in isFactorZZOfZero

public export
data GCDZZ3 : Nat -> ZZ -> ZZ -> ZZ -> Type where
  MkGCDZZ3 : GCDZZ p a b -> GCDZZ q (Pos p) c -> GCDZZ3 q a b c
