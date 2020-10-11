module Decidable

import Equality
import Connectives
import Negation
import Relations
import Isomorphism
import Data.Nat

%hide Dec
%hide Data.Nat.lte
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
not_eq_succ_right Refx impossible

not_eq_succ_left : Not (S k ~~ 0)
not_eq_succ_left Refx impossible

succ_inj : (S a ~~ S b) -> a ~~ b
succ_inj Refx = Refx

natEq : (m, n : Nat) -> Dec (m ~~ n)
natEq 0 0 = Yep Refx
natEq 0 (S k) = Nop not_eq_succ_right
natEq (S k) 0 = Nop not_eq_succ_left
natEq (S k) (S j) with (natEq k j)
  natEq (S k) (S j) | (Yep x) = Yep (eq_cong S x)
  natEq (S k) (S j) | (Nop f) = Nop (f . succ_inj)

-- prefix 10 -|
--
-- postfix |-
--
-- interface Interpreter a b where
--   interpret : a -> b
--
-- data Value : (a, b : Type) -> Type where
--   (|-) : b -> Value a b
--
-- (-|) : Interpreter a b => Value a b -> b
-- (-|) (|- x) = interpret x

L : (1 _ : Dec a) -> BB
L (Yep x) = TT
L (Nop f) = FF

lteb : (n, m : Nat) -> BB
lteb n m = L $ isLTE n m

toWitness : (1 d : Dec a) -> (0 _ : Lift (L d)) -> a
toWitness (Yep y) x = y
toWitness (Nop f) x impossible

fromWitness : (1 d : Dec a) -> a -> Lift (L d)
fromWitness (Yep y) x = TT
fromWitness (Nop f) x = f x

and : BB -> BB -> BB
and TT TT = TT
and _  _  = FF

prod_dec : Dec a -> Dec b -> Dec (X a b)
prod_dec (Yep x) (Yep y) = Yep (x >< y)
prod_dec (Yep x) (Nop f) = Nop (\(a >< b) => f b)
prod_dec (Nop f) _ = Nop $ \(a >< b) => f a

or : BB -> BB -> BB
or FF FF = FF
or _ _ = TT

plus_dec : Dec a -> Dec b -> Dec (a |+| b)
plus_dec (Yep x) _ = Yep (Left x)
plus_dec (Nop f) (Yep x) = Yep (Right x)
plus_dec (Nop f) (Nop g) = Nop $ \case
                                   (Left x) => f x
                                   (Right x) => g x

not : BB -> BB
not TT = FF
not FF = TT

not_dec : Dec a -> Dec (Not a)
not_dec (Yep x) = Nop (\f => f x)
not_dec (Nop f) = Yep f

impl : BB -> BB -> BB
impl TT FF = FF
impl _ _ = TT

impl_dec : Dec a -> Dec b -> Dec (a -> b)
impl_dec (Yep x) (Nop f) = Nop $ \y => f (y x)
impl_dec (Yep x) (Yep f) = Yep (\y => f)
impl_dec (Nop f) y = Yep $ \a => elim_bot (f a)

and_prod : (x : Dec a) -> (y : Dec b) -> ((L x) `and` (L y)) ~~ L (x `prod_dec` y)
and_prod (Yep x) (Yep y) = Refx
and_prod (Yep x) (Nop f) = Refx
and_prod (Nop f) (Yep x) = Refx
and_prod (Nop f) (Nop g) = Refx

or_prod : (x : Dec a) -> (y : Dec b) -> ((L x) `or` (L y)) ~~ L (x `plus_dec` y)
or_prod (Yep x) (Yep y) = Refx
or_prod (Yep x) (Nop f) = Refx
or_prod (Nop f) (Yep x) = Refx
or_prod (Nop f) (Nop g) = Refx

not_not : (x : Dec a) -> (Decidable.not (L x)) ~~ L (Decidable.not_dec x)
not_not (Yep x) = Refx
not_not (Nop f) = Refx

iff : BB -> BB -> BB
iff TT TT = TT
iff TT FF = FF
iff FF TT = FF
iff FF FF = TT

iff_dec : Dec a -> Dec b -> Dec (a <=> b)
iff_dec x y = case (impl_dec x y, impl_dec y x) of
                   ((Yep z), (Yep w)) => Yep (MkEquiv z w)
                   ((Yep z), (Nop f)) => Nop $ \(MkEquiv ab ba) => f ba
                   ((Nop f), (Yep z)) => Nop $ \(MkEquiv ab ba) => f ab
                   ((Nop f), (Nop g)) => Nop $ \(MkEquiv ab ba) => g ba

iff_imp : (x : Dec a) -> (y : Dec b) -> (L x `iff` L y) ~~ L (x `iff_dec` y)
iff_imp (Yep x) (Yep y) = Refx
iff_imp (Yep x) (Nop f) = Refx
iff_imp (Nop f) (Yep x) = Refx
iff_imp (Nop f) (Nop g) = Refx

TTrue : Dec a -> Type
TTrue q = Lift (L q)

minusSafe : (m, n : Nat) -> (0 prf : n `LTE` m) -> Nat
minusSafe m 0 LTEZero = m
minusSafe (S l) (S r) (LTESucc x) = minusSafe l r x


minus : (m, n : Nat) -> {0 prf : Lift (n `lteb` m)} -> Nat
minus m n {prf} = minusSafe m n (toWitness (isLTE n m) prf)
