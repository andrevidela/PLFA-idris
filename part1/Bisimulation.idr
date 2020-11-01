
module Bisimulation

import Data.Nat
import Equality

%default total
%unbound_implicits off

infixl 2 ~!~

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
  Z : {0 gam : Ctxt} -> {0 a : LType} -> gam &. a >: a
  S : {0 gam : Ctxt} -> {0 a, b : LType} -> gam >: a -> gam &. b >: a

public export
data (|-) : Ctxt -> LType -> Type where

  (^) : forall gam, a .
        gam >: a 
     --------------
     -> gam |- a

  (\\) : forall gam, a, b.
         gam &. a |- b
      --------------------
      -> gam |- a =>> b

  (|>) : forall gam, a, b.
         gam |- a  =>> b
      -> gam |- a
      -> gam |- b

  Let : forall gam, a, body.
        gam |- a
     -> gam &. a |- body
     -> gam |- body

length : Ctxt -> Nat
length Nil = Z
length (gam &. _) = S (length gam)

lookup : (gam : Ctxt) -> (n : Nat) -> (p : n `LT` length gam) -> LType
lookup [] 0 p = absurd p
lookup (x &. y) 0 (LTESucc z) = y
lookup [] (S k) p = absurd p
lookup (x &. y) (S k) (LTESucc z) = lookup x k z

public export
Subset : forall a, b. (f : a -> b -> Type) -> (g : a) -> (d : a) -> Type
Subset f g d = {0 xsub : b} -> f g xsub -> f d xsub

public export
SubsetC : Ctxt -> Ctxt -> Type
SubsetC c1 c2 = Subset (>:) c1 c2

public export
SubsetJ : Ctxt -> Ctxt -> Type
SubsetJ c1 c2 = Subset (|-) c1 c2

public export
extend : {0 gam, del: Ctxt}
      -> {0 b : LType} 
      -> SubsetC gam del
      -> SubsetC (gam &. b) (del &. b)
extend f Z = Z
extend f (S x) = S (f x)
public export
rename : {0 gam, del: Ctxt}
      -> SubsetC gam del
      -> SubsetJ gam del
rename f (^ x) = ^(f x)
rename f (\\ x) = \\ (rename (extend f) x)
rename f (x |> y) = (rename f x) |> rename f y
rename f (Let m n) = Let (rename f m) (rename (extend f) n)

public export
extends : {0 gam, del : Ctxt} 
       -> ({0 a    : LType} -> gam      >: a -> del      |- a)
       -> ({0 a, b : LType} -> gam &. b >: a -> del &. b |- a)
extends f Z = ^Z
extends f (S x) = rename S (f x)

public export
subst : {0 gam, del : Ctxt} 
     -> ({0 a : LType} -> gam >: a -> del |- a)
     -> SubsetJ gam del
subst f (^ x) = f x
subst f (\\ x) = \\ (subst (extends f) x)
subst f (x |> y) = (subst f x) |> subst f y
subst f (Let m n ) = Let (subst f m) (subst (extends f) n)

public export
Sigma : forall gam, x, b. (y : gam |- b) -> gam &. b >: x  -> gam |- x
Sigma y Z = y
Sigma y (S z) = ^z

-- _[_] in agda
public export
(:-) : {0 gam : Ctxt}
    -> {0 a, b : LType}
    -> gam &. b |- a
    -> gam |- b
    -> gam |- a
(:-) x y = subst (Sigma y) x

public export
data Value : forall gam, a. gam |- a -> Type where
  VLam : forall n. Value (\\ n)

data (~>) : forall gam, a. (t1, t2 : gam |- a) -> Type where
  Xi1     : forall a, b, c. a ~> b -> a |> c ~> b |> c
  Xi2     : forall m, m', v. Value v -> m ~> m' -> v |> m ~> v |> m'
  BetaLam : forall body, v. Value v -> \\body |> v ~> body :- v
  XiLet   : forall n, n', m, m'. m ~> m' -> Let m n ~> Let m' n
  BetaLet : forall b, v. Value v -> Let v b ~> b :- v

public export
data (->>) : forall gam, a. (t1, t2 : gam |- a) -> Type where
  Step        : forall m, n. m ~> n -> m ->> n
  ReduceRefl  : forall gam, a. (t : gam |- a) -> t ->> t
  ReduceTrans : forall l, m, n. l ->> m -> m ->> n -> l ->> n

public export
implementation (g : _) => (v : _) => Preorder (g |- v) (->>) where
  reflexive = ReduceRefl
  transitive a b c ab bc = ReduceTrans ab bc

valuesWontReduce : forall v, v'. Value v -> Not (v ~> v')
valuesWontReduce VLam (Xi1 _) impossible

reductionsCantBeValues : forall v, v'. v ~> v' -> Not (Value v)
reductionsCantBeValues x y = valuesWontReduce y x

data Progress : forall a. (m : [] |- a) -> Type where
  Step' : forall a. {0 k, l : [] |- a} -> k ~> l -> Progress k
  Done' : forall m. Value m -> Progress m

Gas : Type
Gas = Nat

data (~!~) : forall gam , a. (x, y : gam |- a) -> Type where
  SimTerm : forall gam, a. {x : gam >: a} -> ^x ~!~ ^x
  SimLam : forall n, n'. n ~!~ n' -> \\n ~!~ \\n'
  SimApp : forall l, l', m, m'. l ~!~ l' -> m ~!~ m' -> l |> m ~!~ l' |> m'
  SimLet : forall m, m', n, n'. m ~!~ m' -> n ~!~ n' -> Let m n ~!~ \\ n' |> m'

dagger : forall gam, a. gam |- a -> gam |- a
dagger (^ x) = ^x
dagger (\\ x) = \\ (dagger x)
dagger (x |> y) = (dagger x) |> dagger y
dagger (Let x y) = \\y |> x
 
sameToSim : forall gam, a, n. (m : gam |- a) -> Bisimulation.dagger m = n -> m ~!~ n

simToSame : forall gam, a, n. (m : gam |- a) -> m ~!~ n -> Bisimulation.dagger m = n

valSim : forall m, m'. m ~!~ m' -> Value m -> Value m'
valSim (SimLam l) VLam = VLam

simVal : forall m, m'. m' ~!~ m -> Value m' -> Value m
simVal (SimTerm) VLam impossible
simVal (SimApp a l) VLam impossible
simVal (SimLam l) VLam = VLam
simVal (SimLet l b) VLam impossible

simRename : {0 gam, del: Ctxt} -> {0 a : LType}
         -> (rho : SubsetC gam del)
         -> {0 m, m' : gam |- a}
         -> m ~!~ m' 
         -> (Bisimulation.rename rho m) ~!~ (Bisimulation.rename rho m')
simRename rho SimTerm = SimTerm
simRename rho (SimLam x) = SimLam (simRename (extend rho) x)
simRename rho (SimApp x y) = SimApp (simRename rho x) (simRename rho y)
simRename rho (SimLet x y) = SimLet (simRename rho x) (simRename (extend rho) y)

simExt : forall gam, del. {0 sigma, sigma': {a: LType} -> gam >: a -> del |- a}
      -> ({0 a : LType} -> (x : gam >: a) -> sigma x ~!~ sigma' x)
      -> ({0 a, b: LType} -> (x : gam &. b >: a) -> extends sigma x ~!~ extends sigma' x) 
simExt f Z = SimTerm
simExt f (S x) = simRename S (f x)

simSubst : forall gam, del. {0 sigma, sigma': {a: LType} -> gam >: a -> del |- a}
        -> ({0 a : LType} -> (x : gam >: a) -> sigma x ~!~ sigma' x)
        -> ({0 a : LType} -> {0 m, m' : gam |- a} 
            -> m ~!~ m' -> subst sigma m ~!~ subst sigma' m')
simSubst f (SimTerm {x}) = f x
simSubst f (SimLam x) = SimLam (simSubst (simExt f) x)
simSubst f (SimApp x y) = SimApp (simSubst f x) (simSubst f y)
simSubst f (SimLet x y) = SimLet (simSubst f x) (simSubst (simExt f) y)


simSigma : forall n, n', gam, x, b. {0 m, m' : gam |- b} 
        -> m ~!~ m' 
        -> n ~!~ n' 
        -> (val : (gam &. b) >: x) 
        -> Sigma m val ~!~ Sigma m' val
simSigma y z Z = y
simSigma y z (S w) = SimTerm

simSub : forall m, m', n, n'. n ~!~ n' -> m ~!~ m' -> n :- m ~!~ n' :- m'
simSub x y = simSubst (simSigma y x) x

 -- M  --- —→ --- N
 -- |             |
 -- |             |
 -- ~             ~
 -- |             |
 -- |             |
 -- M† --- —→ --- N†

data BotRight : forall gam, a. (m', n' : gam |- a) -> Type where
  MkBotRight : forall gam, a. {0 n, n', m' : gam |- a} ->  
                              n ~!~ n' -> m' ~> n'  -> BotRight m' n


sim : {0 gam : Ctxt} -> {0 a : LType} -> {0 x, y, z : gam |- a}
   -> x ~!~ y
   -> x ~> z
   -> BotRight y z
sim SimTerm (Xi1 x) impossible
sim SimTerm (Xi2 x y) impossible
sim SimTerm (BetaLam x) impossible
sim SimTerm (XiLet x) impossible
sim SimTerm (BetaLet x) impossible
sim (SimLam _) (Xi1 y) impossible
sim (SimLam _) (Xi2 y z) impossible
sim (SimLam _) (BetaLam y) impossible
sim (SimLam _) (XiLet y) impossible
sim (SimLam _) (BetaLet y) impossible
sim (SimApp {l} v app) (Xi1 f) with (sim v f)
  sim (SimApp {l} v app) (Xi1 f) | (MkBotRight {n'} {n} {m'} w w') = 
    MkBotRight (SimApp w app) (Xi1 w')
sim (SimApp {l'=lprime} v m) (Xi2 {v=value} {m'=n} {m=emm} vv marrow) with (sim m marrow)
  sim (SimApp {l'=lprime} v m) (Xi2 {v=value} {m'=n} {m=emm} vv marrow) | (MkBotRight {n'} {n} {m'} v' w') =
    MkBotRight (SimApp v v') (Xi2 (simVal v vv) w')
sim (SimApp (SimLam {n} {n'} x) z) (BetaLam vv) = 
  MkBotRight (simSub x z) (BetaLam (simVal z vv))
sim (SimLet x z) (XiLet y)   with (sim x y)
  sim (SimLet x z) (XiLet y)   | (MkBotRight w v) = MkBotRight (SimLet w z) (Xi2 VLam v)
sim (SimLet x z) (BetaLet y) = MkBotRight (simSub z x) (BetaLam (simVal x y))


sim_1 : {0 gam : Ctxt} -> {0 a : LType} -> {0 x, y, z : gam |- a}
   -> x ~!~ y
   -> z ~> x
   -> BotRight y z

