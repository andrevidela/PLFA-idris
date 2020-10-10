module Decidable

import Equality
import Connectives
import Negation
import Relations
import Data.Nat

%hide Dec
%hide Prelude.Not
%hide isLTE
%default total

data BB = TT | FF

lte : Nat -> Nat -> BB
lte 0 j = TT
lte (S k) 0 = FF
lte (S k) (S j) = lte k j 

twoLTfour : Decidable.lte 2 4 ~~ TT
twoLTfour = begin (~~) $ lte 2 4 
                      -< byDefinition >- End TT

Lift : BB -> Type
Lift TT = Top
Lift FF = Bot

lift_eq : (b : BB) -> Lift b -> b ~~ TT
lift_eq TT x = Refx
lift_eq FF x = elim_bot x

eq_lift : (b : BB) -> b ~~ TT -> Lift b
eq_lift TT Refx = TT

lteb_lte : (m, n : Nat) -> Lift (m `lte` n) -> m `LTE` n 
lteb_lte 0 n x = LTEZero
lteb_lte (S k) 0 x impossible
lteb_lte (S k) (S j) x = LTESucc $ lteb_lte k j x 

lte_lteb : m `LTE` n -> Lift (m `lte` n)
lte_lteb LTEZero = TT
lte_lteb (LTESucc x) = lte_lteb x

data Dec  : Type -> Type where
  Yep : a -> Dec a
  Nop : Not a -> Dec a

not_zero : {0 m : Nat} -> Not (S m `LTE` Z)
not_zero x impossible

not_succ : {0 m, n : Nat} -> Not (m `LTE` n) -> Not (S m `LTE` S n)
not_succ f (LTESucc x) = f x

isLTE : (m, n : Nat) -> Dec (m `LTE` n)
isLTE 0 n = Yep LTEZero
isLTE (S k) 0 = Nop not_zero
isLTE (S k) (S j) with (isLTE k j)
  isLTE (S k) (S j) | (Yep x) = Yep (LTESucc x)
  isLTE (S k) (S j) | (Nop f) = Nop (not_succ f)

not_left_succ_lt : (m : Nat) -> Not (m < 0)
not_left_succ_lt 0 LTZero impossible
not_left_succ_lt 0 (LTSucc x) impossible
not_left_succ_lt (S _) LTZero impossible
not_left_succ_lt (S _) (LTSucc x) impossible

not_succ_lt : Not (a < b) -> Not (S a < S b)
not_succ_lt f (LTSucc x) = f x

isLT : (m, n : Nat) -> Dec (m < n)
isLT 0 0 = Nop (lt_irreflexive)
isLT 0 (S k) = Yep LTZero
isLT (S k) 0 = Nop (not_left_succ_lt (S k))
isLT (S k) (S j) with (isLT k j)
  isLT (S k) (S j) | (Yep x) = Yep (LTSucc x)
  isLT (S k) (S j) | (Nop f) = Nop (not_succ_lt f)

not_eq_succ_right : Not (0 ~~ S k)

not_eq_succ_left : Not (S k ~~ 0)

natEq : (m, n : Nat) -> Dec (m ~~ n)
natEq 0 0 = Yep Refx
natEq 0 (S k) = Nop ?natEq_rhs_4
natEq (S k) 0 = Nop ?natEq_rhs_3
natEq (S k) (S j) with (natEq k j)
  natEq (S k) (S j) | (Yep x) = Yep (eq_cong S x)
  natEq (S k) (S j) | (Nop f) = Nop ?natEq_rhs_2
