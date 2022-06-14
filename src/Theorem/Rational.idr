module Theorem.Rational

import Data.Nat
import Theorem.ZZ
import Theorem.Division

%default total

||| Canonical representation of Rational
public export
data QQ : Type where
  MkQQ : (num : ZZ) -> (den : Nat) -> {auto dnz : NonZero den} -> Coprime num (Pos den) -> QQ

public export
reduceCommonFactor : (num, den : ZZ) -> (dnz : NotZero den) -> QQ
reduceCommonFactor num den dnz =
  let
    (gcd ** gcdWit) = gcdz num den
    MkGCDZZ (CommonFactorExists prfA prfB) _ = gcdWit
    CofactorExists {k=k1} gcdNum = prfA
    CofactorExists {k=k2} gcdDen = prfB
    gcdWitAB =
      divByGcdGcdOneZ
      $ replace {p = \x => GCDZZ gcd x (Pos gcd * k2)} (sym gcdNum)
      $ replace {p = GCDZZ gcd num} (sym gcdDen) gcdWit
  in
    case k2 of
      Pos (S k2') => MkQQ k1 (S k2') gcdWitAB
      NegS k2' => MkQQ (-k1) (S k2') $ gcdABIsGcdANegB $ gcdABIsGcdNegAB gcdWitAB
      Pos Z => absurd $ replace {p=NotZero} (sym $ trans (sym $ cong Pos $ multZeroRightZero gcd) gcdDen) dnz

{-
plus : QQ -> QQ -> QQ
plus (MkQQ n1 d1 p1) (MkQQ n2 d2 p2) = ?f (n1 * Pos d2 + n2 * Pos d1) (d1 * d2) ?aa
