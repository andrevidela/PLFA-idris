module Relations 

import Data.Nat

%default total
%hide (<)
%hide (>)

lte_antisym : a `LTE` b -> b `LTE` a -> a = b
lte_antisym LTEZero LTEZero = Refl
lte_antisym (LTESucc x) (LTESucc y) = cong S (lte_antisym x y)

public export
data Total : (m, n : Nat) -> Type where
  Fwd : m `LTE` n -> Total m n
  Bwd : n `LTE` m -> Total m n

lte_total : {m, n : Nat} -> Total m n
lte_total {m = 0} {n = n} = Fwd LTEZero
lte_total {m = (S k)} {n = 0} = Bwd LTEZero
lte_total {m = (S k)} {n = (S j)} = case (lte_total {m=k} {n=j}) of
  Fwd lte => Fwd (LTESucc lte)
  Bwd lte => Bwd (LTESucc lte)

public export
data (<) : (n, m : Nat) -> Type where
  LTZero : Z < S n
  LTSucc : a < b -> S a < S b

data Tri : (n, m : Nat) -> Type where
  TriLT : a < b -> Tri a b
  TriEQ : a = b -> Tri a b
  TriGT : b < a -> Tri a b

public export
lt_trans : a < b -> b < c -> a < c
lt_trans LTZero (LTSucc x) = LTZero
lt_trans (LTSucc x) (LTSucc y) = LTSucc (lt_trans x y)

trichotomy : {a, b : Nat} -> Tri a b
trichotomy {a = 0} {b = 0} = TriEQ Refl
trichotomy {a = 0} {b = (S k)} = TriLT LTZero
trichotomy {a = (S k)} {b = 0} = TriGT LTZero
trichotomy {a = (S k)} {b = (S j)} = case trichotomy {a=k} {b=j} of
                                          TriLT lt => TriLT (LTSucc lt)
                                          TriEQ eq => TriEQ (cong S eq)
                                          TriGT gt => TriGT (LTSucc gt)

lt_mono_left : a < b -> c + a < c + d

lt_mono_right : a < b -> a + c < b + c

lt_mono : a < b -> c < d -> a + c < b + d
lt_mono lt1 lt2 = lt_trans (lt_mono_right lt1) (lt_mono_left lt2)


