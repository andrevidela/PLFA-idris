
%default total

infix 4 ~~


data (~~) : {a : Type} -> (u, v : a) -> Type where
  Refx : x ~~ x

eq_sym : (0 _ : a ~~ b) -> b ~~ a
eq_sym Refx = Refx

eq_trans : (0 _ : a ~~ b) -> (0 _ : b ~~ c) -> a ~~ c
eq_trans Refx Refx = Refx

eq_cong : {0 t, u : Type} -> {0 a, b : t} ->
          (0 f : (t -> u)) -> (1 _ : a ~~ b) -> (f a) ~~ (f b)
eq_cong f Refx = Refx

eq_cong_2: {0 t, u, v : Type} -> {0 a, b : t} -> {0 x, y : u} ->
          (0 f : (t -> u -> v)) -> (1 _ : a ~~ b) -> (1 _ : x ~~ y) -> (f a x ) ~~ (f b y)
eq_cong_2 f Refx Refx = Refx

subst : (p : a -> Type) -> (0 _ : x ~~ y) -> p x -> p y
subst p Refx = id

infixr 4 -<
infixr 4 >-

data Step : {a : Type} -> (x, y : a) -> Type where
  End : (0 x : a) -> Step x x
  (-<) : (0 x : a) -> Step x y -> Step x y
  (>-) : (0 _ : x ~~ y) -> Step y z -> Step x z

begin : Step a b -> a ~~ b
begin (End b) = Refx
begin (a -< y) = begin y
begin (x >- y) = let k = begin y in eq_trans x k

byDefinition : x ~~ x
byDefinition = Refx

trans'' : {x, y, z : Type}
       -> x ~~ y -> y ~~ z -> x ~~ z
trans'' w v = begin (x -< w >-
                     y -< v >- End z)

plus_id : (m : Nat) -> m + 0 ~~ m

plus_S : (m, n : Nat) -> m + S n ~~ S (m + n)

plus_comm : (m, n : Nat) -> m + n ~~ n + m
plus_comm m Z = begin $
    m + Z
  -< plus_id m >-
    m
  -< byDefinition >-
    End (Z + m)
plus_comm m (S n) = begin $
    m + S n
  -< plus_S m n >-
    S (m + n)
  -< eq_cong S (plus_comm m n) >-
    S (n + m)
  -< byDefinition >-
    End (S (n + m))
