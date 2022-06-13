module Theorem.Rational

import Data.Nat
import Theorem.ZZ
import Theorem.Division

%default total

||| Canonical representation of Rational
public export
data QQ : Type where
  MkQQ : (num : ZZ) -> (den : Nat) -> {auto dnz : NonZero den} -> Coprime num (Pos den) -> QQ

plus : QQ -> QQ -> QQ
plus (MkQQ n1 d1 p1) (MkQQ n2 d2 p2) = ?f (n1 * Pos d2 + n2 * Pos d1) (d1 * d2) ?aa
