module Theorem.Basic

%default total

public export
data Xor : Type -> Type -> Type where
  ATBF : a -> Not b -> Xor a b
  BTAF : b -> Not a -> Xor a b
