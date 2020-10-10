module Quantifiers

import Equality
import Isomorphism
import Connectives

forall_elim : {a : Type} -> {0 b : a -> Type} -> (l : (x : a) -> b x) -> (m : a) -> b m
forall_elim l m = l m

lift_arg : {0 a, b : u -> Type} -> (((x : u) -> a x) ~~ ((x : u) -> b x) ) -> ((x : u) -> a x ~~ b x)
lift_arg Refx x = Refx

forall_distrib : {a : Type} -> {b, c : a -> Type} ->
                 ((x : a) -> (b x `X` c x)) ~= (((x : a) -> b x) `X` ((x : a) -> c x))
forall_distrib = MkIso 
  (\prod => (\x => proj1 $ prod x)  >< (\x => proj2 $ prod x)) 
  (\(p1 >< p2), x => p1 x >< p2 x)
  (\prod => depfunext $ \x => eta_prod (prod x))
  (\(p1 >< p2) => rewrite apply_dep_prf p1 in 
                  rewrite apply_dep_prf p2 in Refx)

plus_forall_plus : {0 b, c : a -> Type} -> 
                   ((x : a) -> b x) |+| ((x : a) -> c x) -> 
                   (x : a) -> b x |+| c x
plus_forall_plus (Left y) x = Left (y x)
plus_forall_plus (Right y) x = Right (y x)
