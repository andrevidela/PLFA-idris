module List

import Equality
import Induction
import Connectives
import Isomorphism

%hide List
%hide List.(++)
%hide Strings.(++)
%default total

data List : Type -> Type where
  Nil : List a
  (::) : a -> List a -> List a

(++) : List a -> List a -> List a 
(++) [] y = y
(++) (x :: z) y = x :: (++) z y 

append_assoc : (xs, ys, zs : List a) -> (xs ++ ys) ++ zs ~~ xs ++ (ys ++ zs)
append_assoc [] ys zs = Refx
append_assoc (x :: y) ys zs = eq_cong (x ::) (append_assoc y ys zs)

append_idl : (xs : List a) -> [] ++ xs ~~ xs
append_idl [] = Refx
append_idl (x :: y) = Refx

append_idr : (xs : List a) -> xs ++ [] ~~ xs
append_idr [] = Refx
append_idr (x :: y) = eq_cong (x ::) (append_idr y)

Length : List a -> Nat
Length [] = 0
Length (x :: y) = S (Length y)

length_append : (xs, ys : List a) -> Length (xs ++ ys) ~~ Length xs + Length ys
length_append [] ys = Refx
length_append (x :: y) ys = eq_cong S (length_append y ys)

Reverse : List a -> List a
Reverse [] = []
Reverse (x :: y) = Reverse y ++ [x]

rev_append_distrib : 
                     (xs, ys : List a) -> Reverse (xs ++ ys) ~~ Reverse ys ++ Reverse xs
rev_append_distrib [] ys = eq_sym $ append_idr (Reverse ys)
rev_append_distrib (x :: y) [] = rewrite eq $ append_idr y in Refx
rev_append_distrib (x :: y) (z :: w) = 
  begin (~~) $ (Reverse (y ++ (z :: w)) ++ [x]) 
              -< eq_cong (++ [x]) (rev_append_distrib y (z :: w)) >- 
               (((Reverse w ++ [z]) ++ Reverse y) ++ [x])
              -< append_assoc (Reverse w ++ [z]) (Reverse y) [x]  >-
                (Reverse (z :: w) ++ Reverse y ++ [x])
              -< byDefinition >- 
                (Reverse (z :: w) ++ Reverse (x :: y))
              -< byDefinition >-
                End ((Reverse w ++ [z]) ++ (Reverse y ++ [x]))


rev_rev_id :  (xs : List a) -> Reverse (Reverse xs) ~~ xs
rev_rev_id [] = Refx
rev_rev_id (x :: y) = let rec = rev_rev_id y 
                          try = rev_append_distrib (Reverse y) [x] in 
                          rewrite eq try in eq_cong (x ::) rec


tailrec : List a -> List a -> List a
tailrec [] y = y
tailrec (x :: xs) ys = tailrec xs (x :: ys)

mapL : (f : a -> b) -> List a -> List b
mapL f [] = []
mapL f (x :: y) = f x :: mapL f y 

mapL_compose : (f : b -> c) -> (g : a -> b) -> (xs : List a) 
            -> mapL (f . g)  xs ~~ ((mapL f) . (mapL g)) xs
mapL_compose f g [] = Refx
mapL_compose f g (x :: y) = eq_cong ((f (g x)) ::) (mapL_compose f g y)


mapL_compose_ext : (f : b -> c) -> (g : a -> b)
                -> mapL (f . g) ~~ ((mapL f) . (mapL g))
mapL_compose_ext f g = funext $ mapL_compose f g 


map_append_distrib : (f : a -> b) -> (xs, ys : List a) 
                  -> mapL f (xs ++ ys) ~~ mapL f xs ++ mapL f ys
map_append_distrib f [] ys = Refx
map_append_distrib f (x :: y) ys = eq_cong (f x :: ) (map_append_distrib f y ys)


foldr : (f : a -> b -> b) -> b -> List a -> b
foldr f acc [] = acc
foldr f acc (x :: xs) = f x (foldr f acc xs)

fold_cons : (xs : List a) -> foldr (::) [] xs ~~ xs
fold_cons [] = Refx
fold_cons (x :: y) = eq_cong (x ::) (fold_cons y)

fold_append : (xs, ys : List a) -> xs ++ ys ~~ foldr (::) ys xs
fold_append [] ys = Refx
fold_append (x :: y) ys = eq_cong (x ::) (fold_append y ys)

map_is_fold : (ls : List a) -> mapL f ls ~~ foldr (\x, xs => f x :: xs) [] ls
map_is_fold [] = Refx
map_is_fold (x :: y) = eq_cong (f x ::) (map_is_fold y)


downFrom : Nat -> List Nat
downFrom 0 = []
downFrom (S k) = k :: downFrom k

sumNat : List Nat -> Nat
sumNat [] = Z
sumNat (x :: y) = x + sumNat y


record IsMonoid {a : Type} (c : a -> a -> a) (e : a) where
  constructor MkMonoid
  assoc : (x, y, z : a) -> ((x `c` y) `c` z) ~~ (x `c` (y `c` z))
  id_left : (x : a) -> c e x ~~ x
  id_right : (x : a) -> c x e ~~ x
 
plus_monoid : IsMonoid Prelude.(+) Z
plus_monoid = MkMonoid (\x, y , z => fromEq (plus_assoc x y z))
                       (\x => fromEq (plus_id_left x))
                       (\x => fromEq (plus_id_right x))

list_monoid : IsMonoid (++) []
list_monoid = MkMonoid append_assoc append_idl append_idr

foldr_monoid : {0 a : Type} -> (c : a -> a -> a) -> (e : a) -> IsMonoid c e ->
               (xs : List a) -> (acc : a) -> List.foldr c acc xs ~~ (List.foldr c e xs `c` acc)
foldr_monoid c e (MkMonoid assoc id_left id_right) [] acc = 
  eq_sym $ id_left acc 
foldr_monoid c e (MkMonoid ass idl idr) (y :: z) acc = 
  begin (~~) $ (y `c` foldr c acc z) 
            -< eq_cong (c y) (foldr_monoid c e (MkMonoid ass idl idr) z acc) >- 
               (y `c` (List.foldr c e z `c` acc))
            -< (eq_sym $ ass y (List.foldr c e z) acc) >-                   
            End (List.foldr c e (y :: z) `c`  acc)
                                         

namespace Predicates
  public export
  data All : (p : a -> Type) -> List a -> Type where
    Nil : All p []
    (::) : {x : a} -> p x -> All p xs -> All p (x :: xs)
  
  public export
  data Any : (p : a -> Type) -> List a -> Type where
    Here : {xs : List a} -> p x -> Any p (x :: xs)
    There : {p : a -> Type} -> {xs : List a} -> Any p xs -> Any p (x :: xs)

Inn : (x : a) -> (xs : List a) -> Type
Inn x xs = Any (x ~~) xs

NotIn : (x : a) -> (xs : List a) -> Type
NotIn x xs = Not (x `Inn` xs)

to_prod : (xs, ys : List a) -> All p (xs ++ ys) -> X (All p xs) (All p ys)
to_prod [] ys x = [] >< x
to_prod (y :: z) ys (x :: w) with (to_prod z ys w)
  to_prod (y :: z) ys (x :: w) | (v >< s) = (x :: v) >< s

from_prod : (xs, ys : List a) -> X (All p xs) (All p ys) -> All p (xs ++ ys)
from_prod [] ys (x >< y) = y
from_prod (y :: z) ys ((x :: v) >< w) = x :: from_prod z ys (v >< w)


all_append_iff : (xs, ys : List a) -> All p (xs ++ ys) <=> (All p xs `X` All p ys)
all_append_iff xs ys = MkEquiv (to_prod xs ys) (from_prod xs ys)


find_pred : (xs : List a) -> Any p xs -> (x : a ** X (Any (x ~~) xs) (p x))
find_pred (x :: xs) (Here wit) = (x ** Here Refx >< wit)
find_pred (x :: xs) (There p) = 
  let (MkDPair x (prf >< pred)) = find_pred xs p in (x ** (There prf) >< pred)

extract_witness : {p : a -> Type} -> (xs : List a) 
               -> (x : a ** X (Any (x ~~ ) xs) (p x)) 
               -> Any p xs
extract_witness [] (MkDPair fst (Here p >< y)) impossible
extract_witness (x :: xs) (MkDPair fst (Here p >< y)) = 
  rewrite sym $ eq p in Here y
extract_witness (x :: xs) (MkDPair fst (There prf >< y)) = 
  let rec : Any p xs = extract_witness xs ((fst ** (prf >< y))) in There rec 

any_exists : {p : a -> Type} -> (xs : List a) -> Any p xs ~= (x : a  ** ((Inn x xs) `X` p x))
any_exists xs = MkIso (find_pred xs) (extract_witness xs) ?toFr ?any_exists_rhs






