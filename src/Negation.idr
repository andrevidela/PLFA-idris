
module Negation

import Connectives
import Relations
import Isomorphism
import Equality

%hide not
%hide Not
%hide EqOrd.(<)
%default total

public export
Not : Type -> Type
Not a = a -> Bot

public export
elim_not : Not a -> a -> Bot
elim_not f x = f x

not_not_intro : a -> Not (Not a)
not_not_intro x f = f x

infix 1 =/=

public export
(=/=) : Type -> Type -> Type
x =/= y = Not (x ~~ y)

public export
sym_not : (a =/= b) -> (b =/= a)
sym_not f Refx = f Refx


export
not_cong : {0 t: Type} -> {0 a, b : t} ->
           (0 f : (t -> u)) -> (1 _ : Not (a ~~ b)) -> Not (f a ~~ f b)
not_cong f g x = g (funinj {f} x)

public export
lt_irreflexive : {n : Nat} -> Not (n < n)
lt_irreflexive {n = Z} LTZero impossible
lt_irreflexive {n = Z} (LTSucc x) impossible
lt_irreflexive {n = (S k)} (LTSucc x) = lt_irreflexive {n=k} x


deMorgan : (Not (a |+| b)) ~= ((Not a) `X` (Not b))
deMorgan = MkIso (\c => (\x => c (Left x)) >< (\x => c (Right x)))
                 (\(x >< y) => (\v => case v of
                                      (Left a) => x a
                                      (Right b) => y b))
                 (\contra => ?what)
                 (\(c1 >< c2) => rewrite apply_prf c1 in
                                 rewrite apply_prf c2 in Refx)

em_irrefutable : {x : a} -> Not (Not (a |+| Not a))
em_irrefutable f = f (Right (\y => f (Left x)))

excluded_middle : (a : Type) -> a |+| Not a

double_neg : (a : Type) -> Not (Not a) -> a

pierce_law : (a, b : Type) -> ((a -> b) -> a)

impl_disj : (a, b : Type) -> (a -> b) -> Not a |+| b

excluded_middle_to_everything : (a : Type) -> a |+| Not a
  ->  ( Not (Not a) -> a
      , (b : Type) -> (a -> b) -> a
      , (b : Type) -> ((Not a) |+| b)
      )
excluded_middle_to_everything a x = (\na => case x of {Left a => a; Right n => elim_bot $ na n}
  , \tpe, ab => ?qwe, ?zxc)

