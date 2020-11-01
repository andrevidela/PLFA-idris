module More

import Data.Nat
import Equality

prefix 9 \\
infixl 7 |>
prefix 9 ^
prefix 9 #

infixr 0 ==> -- function application, like $
infixr 4 ~>  -- Single Reduction step
infixr 2 ->> -- "Reduces to"
infixr 7 =>> -- Type in Lambda calculus

infix 5 :-

infixl 6 .:
infixr 4 >:
infixl 5 &.
infixl 5 |-

-- lambda type
public export
data LType : Type where
  (=>>) : LType -> LType -> LType
  NatType : LType

-- Context
public export
data Ctxt : Type where
  Nil : Ctxt
  (&.) : Ctxt -> LType -> Ctxt

public export
data (>:) : Ctxt -> LType -> Type where
  Z : gam &. a >: a
  S : gam >: a -> gam &. b >: a

public export
data (|-) : Ctxt -> LType -> Type where

  (^) : gam >: a 
     --------------
     -> gam |- a

  (\\) : {a, b : LType} 
      -> gam &. a |- b
      --------------------
      -> gam |- a =>> b

  (|>) : {a, b : LType} 
      -> gam |- a  =>> b
      -> gam |- a
      -> gam |- b

--  Zero : gam |- NatType
--
--  Succ : gam |- NatType
--      ------------------
--      -> gam |- NatType
--
--  Case : {a : LType} 
--      -> gam |- NatType
--      -> gam |- a
--      -> gam &. NatType |- a
--      ----------------------
--      -> gam |- a
--
--  Mu : {a : LType}
--      -> gam &. a |- a
--      ------------------
--      -> gam |- a

  Let : {a : LType}
     -> gam |- a
     -> gam &. a |- body
     -> gam |- body

-- data SuccCase : Ctxt -> LType -> Type where
--   CaseS : (gam &. NatType |- a) -> SuccCase gam a
-- 
-- data ZeroCase : Ctxt -> LType -> Type where
--   CaseZ : (gam |- a) -> SuccCase gam a -> ZeroCase gam a
-- 
-- Case' : {a : _} -> gam |- NatType -> ZeroCase gam a -> gam |- a
-- Case' scrutinee (CaseZ zero (CaseS suc)) = Case scrutinee zero suc


-- cTwo' : Nil |- (NatType =>> NatType) =>> NatType =>> NatType
-- cTwo' = \\ \\ (^(S Z) |> (^(S Z) |> ^Z))

length : Ctxt -> Nat
length Nil = Z
length (gam &. _) = S (length gam)

lookup : (gam : Ctxt) -> (n : Nat) -> (p : n `LT` length gam) -> LType
lookup [] 0 p = absurd p
lookup (x &. y) 0 (LTESucc z) = y
lookup [] (S k) p = absurd p
lookup (x &. y) (S k) (LTESucc z) = lookup x k z

count : (n : Nat) -> (gam : Ctxt) -> (p : n `LT` length gam) -> gam >: lookup gam n p
count 0 [] p = absurd p
count 0 (x &. y) (LTESucc z) = Z
count (S k) [] p = absurd p
count (S k) (x &. y) (LTESucc z) = S (count k x z)

(#) :  (n : Nat) -> {gam : Ctxt} -> {auto inGam : n `LT` length gam}
   -> gam |- lookup gam n inGam
(#) n = ^(count n gam inGam)


-- two : gam |- NatType
-- two = Succ (Succ (Zero))
-- 
-- plus : {gam : Ctxt} -> gam |- NatType =>> NatType =>> NatType
-- plus = Mu $ \\ \\ (Case (#1) (#0) (Succ (#3 |> #0 |> #1)))
-- 
-- twoPlusTwo : {gam : Ctxt} -> gam |- NatType
-- twoPlusTwo = plus |> two |> two
-- 
-- cTwo : Nil |- (NatType =>> NatType) =>> NatType =>> NatType
-- cTwo = \\ \\ (#1 |> (#1 |> #0))
-- 
-- Ch : LType -> LType 
-- Ch a = (a =>> a) =>> a =>> a
-- 
-- cPlus : {a : LType} -> {gam : Ctxt} -> gam |- Ch a =>> Ch a =>> Ch a
-- cPlus = \\ \\ \\ \\ (#3 |> #1 |> (#2 |> #1 |> #0))
-- 
-- cSuc : {gam : Ctxt} -> gam |- NatType =>> NatType
-- cSuc = \\ (Succ (#0))
-- 
-- cTwoPlusTwo : [] |- NatType
-- cTwoPlusTwo = cPlus |> cTwo |> cTwo |> cSuc |> Zero
-- 
-- mult : {gam : Ctxt} -> gam |- NatType =>> NatType =>> NatType
-- mult = Mu $ \\ \\ (Case (#1) (Zero) (plus |> #1 |> (#3 |> #0 |> #1)))

public export
Subset : (f : a -> b -> Type) -> (g : a) -> (d : a) -> Type
Subset f g d = {xsub : b} -> f g xsub -> f d xsub

public export
SubsetC : Ctxt -> Ctxt -> Type
SubsetC c1 c2 = Subset (>:) c1 c2

public export
SubsetJ : Ctxt -> Ctxt -> Type
SubsetJ c1 c2 = Subset (|-) c1 c2

public export
extend : {gam, del: Ctxt}
      -> {b : LType} 
      -> SubsetC gam del
      -> SubsetC (gam &. b) (del &. b)
extend f Z = Z
extend f (S x) = S (f x)

public export
rename : {gam, del: Ctxt}
      -> SubsetC gam del
      -> SubsetJ gam del
rename f (^ x) = ^(f x)
rename f (\\ x) = \\ (rename (extend f) x)
rename f (x |> y) = (rename f x) |> rename f y
-- rename f Zero = Zero
-- rename f (Succ x) = Succ (rename f x)
-- rename f (Case x y z) = Case (rename f x) (rename f y) (rename (extend f) z)
-- rename f (Mu x) = Mu (rename (extend f) x)
rename f (Let m n) = Let (rename f m) (rename (extend f) n)

public export
extends : {gam, del : Ctxt} 
       -> ({a    : LType} -> gam      >: a -> del      |- a)
       -> ({a, b : LType} -> gam &. b >: a -> del &. b |- a)
extends f Z = ^Z
extends f (S x) = rename S (f x)

public export
subst : {gam, del : Ctxt} 
     -> ({a : LType} -> gam >: a -> del |- a)
     -> SubsetJ gam del
subst f (^ x) = f x
subst f (\\ x) = \\ (subst (extends f) x)
subst f (x |> y) = (subst f x) |> subst f y
-- subst f Zero = Zero
-- subst f (Succ x) = Succ (subst f x)
-- subst f (Case x y z) = Case (subst f x) (subst f y) (subst (extends f) z)
-- subst f (Mu x) = Mu (subst (extends f) x)
subst f (Let m n ) = Let (subst f m) (subst (extends f) n)

public export
Sigma : {0 x, b : LType} -> (y : gam |- b) -> gam &. b >: x  -> gam |- x
Sigma y Z = y
Sigma y (S z) = ^z

public export
(:-) : {gam : _}
    -> {a, b : LType}
    -> gam &. b |- a
    -> gam |- b
    -> gam |- a
(:-) x y = subst (Sigma y) x

public export
data Value : gam |- a -> Type where
  VLam : Value (\\ n)
--  VZero : Value Zero
--  VSucc : Value v -> Value (Succ v)

data (~>) : (t1, t2 : gam |- a) -> Type where
  Xi1 : l ~> l' -> l |> m ~> l' |> m
  Xi2 : Value v -> m ~> m' -> v |> m ~> v |> m'
  BetaLam : Value v -> \\body |> v ~> body :- v
--   XiSucc : m ~> m' -> Succ m ~> Succ m'
--   XiCase : l ~> l' -> Case l m n ~> Case l' m n
--   BetaZero : Case Zero m n ~> m
--   BetaSucc : Value v -> Case (Succ v) m n ~> n :- v
--   BetaMu : Mu m ~> m :- (Mu m)
  XiLet : m ~> m' -> Let m n ~> Let m' n
  BetaLet : Value v -> Let v b ~> b :- v

public export
data (->>) : (t1, t2 : gam |- a) -> Type where
  Step : m ~> n -> m ->> n
  ReduceRefl : (t : gam |- a) -> t ->> t
  ReduceTrans : l ->> m -> m ->> n -> l ->> n

public export
implementation Preorder (gam |- a) (->>) where
  reflexive = ReduceRefl
  transitive a b c ab bc = ReduceTrans ab bc

-- twoIsTwo : More.cTwo |> More.cSuc |> Zero ->> Succ (Succ Zero)
-- twoIsTwo = begin (->>) $
--            cTwo |> cSuc |> Zero
--            -< Step (Xi1 (BetaLam VLam)) >-
--            \\ (cSuc |> (cSuc |> #0)) |> Zero
--            -< Step (BetaLam VZero) >-
--            (cSuc |> (cSuc |> Zero)) 
--            -< Step (Xi2 VLam (BetaLam VZero)) >-
--            cSuc |> Succ Zero
--            -< Step (BetaLam (VSucc VZero)) >- 
--            End (Succ (Succ Zero))

valuesWontReduce : Value v -> Not (v ~> v')
valuesWontReduce VLam (Xi1 _) impossible
--valuesWontReduce VZero (Xi1 _) impossible
--valuesWontReduce (VSucc x) (Xi1 _) impossible
--valuesWontReduce VLam (Xi2 _ _) impossible
--valuesWontReduce VZero (Xi2 _ _) impossible
--valuesWontReduce (VSucc x) (Xi2 _ _) impossible
--valuesWontReduce VLam (BetaLam _) impossible
--valuesWontReduce VZero (BetaLam _) impossible
--valuesWontReduce (VSucc x) (BetaLam _) impossible
--valuesWontReduce (VSucc x) (XiSucc y) = valuesWontReduce x y
--valuesWontReduce VLam (XiCase _) impossible
--valuesWontReduce VZero (XiCase _) impossible
--valuesWontReduce (VSucc x) (XiCase _) impossible
--valuesWontReduce VLam BetaZero impossible
--valuesWontReduce VZero BetaZero impossible
--valuesWontReduce (VSucc x) BetaZero impossible
--valuesWontReduce VLam (BetaSucc _) impossible
--valuesWontReduce VZero (BetaSucc _) impossible
--valuesWontReduce (VSucc x) (BetaSucc _) impossible
--valuesWontReduce VLam BetaMu impossible
--valuesWontReduce VZero BetaMu impossible
--valuesWontReduce (VSucc x) BetaMu impossible

reductionsCantBeValues : v ~> v' -> Not (Value v)
reductionsCantBeValues x y = valuesWontReduce y x

data Progress : (m : [] |- a) -> Type where
  Step' : {n : _} -> m ~> n -> Progress m
  Done' : Value m -> Progress m

twoProof : 2 + 2 `Equal` 4
twoProof = Refl

public export
progress : {a : LType} -> (m : [] |- a) -> Progress m
progress (^ x) impossible
progress (\\ x) = Done' VLam
progress (x |> y) with (progress x)
  progress (x |> y) | (Step' z) = Step' (Xi1 z)
  progress (x |> y) | (Done' z) with (progress y)
    progress (x |> y) | (Done' z) | (Step' w) = Step' (Xi2 z w)
    progress (\\ x |> y) | (Done' z) | (Done' w) = Step' (BetaLam w)
-- progress Zero = Done' VZero
-- progress (Succ x) with (progress x)
--   progress (Succ x) | (Step' y) = Step' (XiSucc y)
--   progress (Succ x) | (Done' y) = Done' (VSucc y)
-- progress (Case x y z) with (progress x)
--   progress (Case x y z)        | (Step' w) = Step' (XiCase w)
--   progress (Case Zero y z)     | (Done' VZero) = Step' BetaZero
--   progress (Case Zero y z)     | (Done' VLam) impossible
--   progress (Case (Succ v) y z) | (Done' (VSucc w)) = Step' (BetaSucc w)
-- progress (Mu x) = Step' BetaMu
progress (Let m n ) with (progress m)
  progress (Let m n) | (Step' x) = Step' (XiLet x)
  progress (Let m b) | (Done' v) = Step' (BetaLet v)

Gas : Type
Gas = Nat

data Finished : (n : gam |- a) -> Type where
  Done : Value n -> Finished n
  OutOfGas : Finished n

data Steps : [] |- a -> Type where
  MkSteps : l ->> n -> Finished n -> Steps l

eval : {a : LType} -> Gas -> (l : [] |- a) -> Steps l
eval 0 l = MkSteps (ReduceRefl l) OutOfGas
eval (S k) l with (progress l)
  eval (S k) l | (Step' x {n}) with (eval k n)
    eval (S k) l | (Step' x) | (MkSteps y z) = MkSteps (ReduceTrans (Step x) y) z
  eval (S k) l | (Done' x) = MkSteps (ReduceRefl l) (Done x)

-- sucMu : [] |- NatType
-- sucMu = Mu (Succ (#0))

-- evalInf : (More.eval 3 More.sucMu) = MkSteps 
--     (ReduceTrans (Step BetaMu) 
--     (ReduceTrans (Step (XiSucc BetaMu)) 
--     (ReduceTrans (Step (XiSucc (XiSucc BetaMu))) 
--     (ReduceRefl (Succ (Succ (subst (Sigma (Mu (Succ (#0)))) (Succ (#0))))))))) OutOfGas
-- evalInf = Refl


-- evalTwoPlusTwo : (More.eval 100 (More.cTwo |> More.cSuc |> Zero)) ~=~ 
--                  MkSteps 
--                  (ReduceTrans (Step (Xi1 (BetaLam VLam))) 
--                  (ReduceTrans (Step (BetaLam VZero)) 
--                  (ReduceTrans (Step (Xi2 VLam (BetaLam VZero))) 
--                  (ReduceTrans (Step (BetaLam (VSucc VZero))) 
--                  (ReduceRefl (Succ (Succ Zero))))))) (Done (VSucc (VSucc VZero)))
-- evalTwoPlusTwo = Refl























