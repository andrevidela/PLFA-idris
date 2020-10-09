module Equality

import Data.Nat
import Decidable.Order

%default total

infix 4 ~~


public export
data (~~) : {a : Type} -> (u, v : a) -> Type where
  Refx : x ~~ x

public export
eq_sym : (0 _ : a ~~ b) -> b ~~ a
eq_sym Refx = Refx

public export
eq_trans : (0 _ : a ~~ b) -> (0 _ : b ~~ c) -> a ~~ c
eq_trans Refx Refx = Refx

public export
eq_cong : {0 t, u : Type} -> {0 a, b : t} ->
          (0 f : (t -> u)) -> (1 _ : a ~~ b) -> (f a) ~~ (f b)
eq_cong f Refx = Refx

public export
eq_cong_2: {0 t, u, v : Type} -> {0 a, b : t} -> {0 x, y : u} ->
          (0 f : (t -> u -> v)) -> (1 _ : a ~~ b) -> (1 _ : x ~~ y) -> (f a x ) ~~ (f b y)
eq_cong_2 f Refx Refx = Refx

public export
subst : (p : a -> Type) -> (0 _ : x ~~ y) -> p x -> p y
subst p Refx = id

infixr 4 -<
infixr 4 >-

public export
data Step : {a : Type} -> (x, y : a) -> (a -> a -> Type) -> Type where
  End : (x : a) -> Step x x p
  (-<) : (x : a) -> Step x y p -> Step x y p
  (>-) : {0 p : a -> a -> Type} -> {x, y, z : a} -> (p x y) -> Step y z p -> Step x z p

export
begin : {0 a : Type} -> {0 x, y : a} -> (p : a -> a -> Type) -> (Preorder a p) => Step x y p -> p x y
begin p (End a) = reflexive a
begin p (a -< y) = begin p y
begin p ((>-) u v {x} {y} {z}) {a} = let w = begin p v in
                                         transitive x y z u w

export
implementation Preorder Nat LTE where
  reflexive v = lteRefl
  transitive a b c = lteTransitive

export
implementation Preorder a (~~) where
  reflexive v = Refx
  transitive x x x Refx Refx = Refx

public export
byDefinition : x ~~ x
byDefinition = Refx

pre_trans : {a : Type} -> {p : a -> a -> Type} -> Preorder a p => {x, y, z : a} -> p x y -> p y z -> p x z
pre_trans w v = begin p (x -< w >-
                         y -< v >- End z)

plus_id : (m : Nat) -> m + 0 ~~ m

plus_S : (m, n : Nat) -> m + S n ~~ S (m + n)

plus_comm : (m, n : Nat) -> m + n ~~ n + m
plus_comm m Z = begin (~~) $
    m + Z
  -< plus_id m >-
    m
  -< byDefinition >-
    End (Z + m)
plus_comm m (S n) = begin (~~) $
    m + S n
  -< plus_S m n >-
    S (m + n)
  -< eq_cong S (plus_comm m n) >-
    End (S (n + m))

infix 0 =*=

data (=*=) : {a : Type} -> (x, y : a) -> Type where
  LEIB : ((p : a -> Type) -> p x -> p y) -> x =*= y

lieb_refl : a =*= a
lieb_refl = LEIB $ \_ => id

lieb_trans : x =*= y -> y =*= z -> x =*= z
lieb_trans (LEIB f) (LEIB g) = LEIB (\p => \w => g p (f p w))

martin_leib : x ~~ y -> x =*= y
martin_leib v = LEIB $ \p, x => subst p v x

lieb_martin : {a : Type} -> {x, y: a} -> x =*= y -> x ~~ y
lieb_martin (LEIB f) = f (x ~~) Refx
