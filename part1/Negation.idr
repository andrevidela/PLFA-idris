
module Negation

import Connectives
import Relations
import Isomorphism
import Equality

%hide not
%hide Not
%hide EqOrd.(<)
%default total

Not : Type -> Type
Not a = a -> Bot

elim_not : Not a -> a -> Bot
elim_not f x = f x

not_not_intro : a -> Not (Not a)
not_not_intro x f = f x

infix 4 =/=

(=/=) : Type -> Type -> Type
x =/= y = Not (x ~~ y)

lt_irreflexive : {n : Nat} -> Not (n < n)
lt_irreflexive {n = Z} LTZero impossible
lt_irreflexive {n = Z} (LTSucc x) impossible
lt_irreflexive {n = (S k)} (LTSucc x) = lt_irreflexive {n=k} x

deMorgan : Not (a |+| b) ~= ((Not a) `X` (Not b))
deMorgan = MkIso (\c => (\x => c (Left x)) >< (\x => c (Right x)))
                 (\(x >< y) => (\case (Left a) => x a
                                      (Right b) => y b)) 
                 (\contra => ?tofr_2) 
                 (\(c1 >< c2) => ?whuat)
