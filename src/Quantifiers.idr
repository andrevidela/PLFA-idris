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

record E (a : Type) (b : a -> Type) where
  constructor (&&)
  proj1' : a
  proj2' : b proj1'

elim_exists : {0 b : a -> Type} -> ((x : a) -> b x -> c) -> (x ** b x) -> c
elim_exists f (MkDPair fst snd) = f fst snd

forall_exists_curr : {0 b : a -> Type} -> ((x : a) -> b x -> c) ~= ((x ** b x) -> c)
forall_exists_curr = MkIso elim_exists
                           (\p, v, x => p (v ** x) ) 
                           (\arg => depfunext \v => 
                               rewrite sym $ apply_dep_prf (arg v) in Refx )
                           (\arg => funext \(MkDPair x y) => Refx)

exists_distrib_plus : {b, c : a -> Type} -> (x ** b x |+| c x) ~= (x ** b x) |+| (x ** c x)
exists_distrib_plus = MkIso (\case
                               (MkDPair fst (Left x)) => Left (MkDPair fst x)
                               (MkDPair fst (Right x)) => Right (MkDPair fst x))
                               (\case
                                 (Left (MkDPair fst snd)) => MkDPair fst (Left snd)
                                 (Right (MkDPair fst snd)) => MkDPair fst (Right snd))
                               (\case 
                                 (MkDPair fst (Left x)) => Refx 
                                 (MkDPair fst (Right x)) => Refx )
                               (\case
                                 (Left (MkDPair fst snd)) => Refx
                                 (Right (MkDPair fst snd)) => Refx)

existprod_to_prodexists : {0 b, c : a -> Type} -> (x : a ** X (b x) (c x)) -> 
                          X (x ** b x) (x ** c x)
existprod_to_prodexists (MkDPair fst (x >< y)) = MkDPair fst x >< MkDPair fst y

-- This is impossible because we can't pick two existentials at the same time to
-- prove both b x and c x at the same time
-- prodexists_to_existsprod : {0 b, c : a -> Type}
--                        -> X (x ** b x) (x ** c x)
--                        -> (x : a ** X (b x) (c x)) 

not_ex_all_not : {0 b : a -> Type} -> Not (x ** b x) ~= (x : a) -> Not (b x )
not_ex_all_not = MkIso (\v, w, e => v (w ** e)) 
                       (\xbxv, (MkDPair x bx) => xbxv x bx) 
                       (\xbxv => funext \(MkDPair x bx) => Refx) 
                       (\xbxv => let prf = apply_dep_prf2 xbxv in 
                                 rewrite sym prf in Refx)

existsnot_to_notforall : {0 b : a -> Type} -> (x ** Not (b x)) -> Not ((x : a) -> b x)
existsnot_to_notforall (MkDPair fst snd) f = snd (f fst)


