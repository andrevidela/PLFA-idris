module Untyped

import public Data.Fin
import Equality
import public Decidable.Order

%default total

prefix 5 \\
infixl 7 |>
prefix 9 ^

infixr 0 ==> -- function application, like $
infixr 4 ~>  -- Single Reduction step
infixr 2 ->> -- "Reduces to"
infixr 7 =>> -- Type in Lambda calculus

infix 6 `∋` -- Checked / inherited 
infix 6 `∈` -- inferred / synthesized

infixr 8 `X` -- Product in Lambda calculus
infixl 5 ?= -- Type equality in lambda calculus

infixl 6 .: -- typed term
infixr 4 >: -- `in`
infixl 5 &. -- extend context
infixl 5 |- -- judgement Inferred
infixl 5 |= -- judgement Check
prefix 10 # -- judgement Check

public export
LType : Type
LType = ()

public export
Context : Type
Context = Nat

public export
Elem : Context -> Type
Elem = Fin

public export
data Jay : Context -> Type where

  (^) : {0 Γ : Context} -> Elem Γ -> Jay Γ

  (\\)  :  {0 Γ : Context} -> Jay (S Γ) ->  Jay Γ

  (|>) :  {0 Γ : Context} 
       -> Jay Γ
       -> Jay Γ
       -> Jay Γ

twoChurch : {n : Nat} -> Jay n
twoChurch = \\ \\ ^1 |> (^1 |> ^0)

fourChurch : {n : Nat} -> Jay n
fourChurch = \\ \\ (^1 |> (^1 |> (^1 |> (^1 |> ^0))))

plusChurch : {n : Nat} -> Jay n
plusChurch = \\ \\ \\ \\ (^3 |> ^1 |> (^2 |> ^1 |> ^0))

twoPlusTwoChurch : Jay Z
twoPlusTwoChurch = plusChurch |> twoChurch |> twoChurch 

public export
ext : (Elem g -> Elem d) -> Elem (S g) -> Elem (S d)
ext f FZ = FZ
ext f (FS x) = FS (f x)

public export
rename : (Elem g -> Elem d) -> Jay g -> Jay d
rename f (^ x) = ^ (f x)
rename f (\\ x) = \\ rename (ext f) x
rename f (x |> y) = rename f x |> rename f y

public export
exts : (Elem g -> Jay d) -> Elem (S g) -> Jay (S d)
exts f FZ = ^FZ
exts f (FS x) = rename FS (f x)

public export
subst : (Elem g -> Jay d) -> Jay g -> Jay d
subst f (^ x) = f x
subst f (\\ x) = \\ (subst (exts f) x)
subst f (x |> y) = (subst f x) |> subst f y

public export
substZero : Jay g -> Elem (S g) -> Jay g
substZero x FZ = x
substZero x (FS y) = ^ y

public export
substOne : Jay (S g) -> Jay g -> Jay g
substOne x y = subst (substZero y)  x

mutual 
  public export
  data Neutral : Jay g -> Type where

    Term : (x : Elem g) -> Neutral (^x)
    App : Neutral l -> Normal m -> Neutral (l |> m)


  public export
  data Normal : Jay g -> Type where

    Term' : Neutral m -> Normal m
    Lam : (n : Jay (S g)) -> Normal n -> Normal (\\ n)

public export
data (~>) : Jay g -> Jay g -> Type where
  
  Xi : l ~> l' -> l |> m ~> l' |> m

  Xi2 : m ~> m' -> l |> m ~> l |> m'

  Beta : (\\ n) |> m ~> substOne n m 
  
  Zeta : n ~> n' -> \\ n ~> \\ n'

namespace TransitiveClosure
  public export
  data (->>) : Jay g -> Jay g -> Type where
    Step : {m : _} -> m ~> n -> m ->> n
    ReduceRefl : (t : Jay g) -> t ->> t
    ReduceTrans : {l, m, n : _} -> l ->> m -> m ->> n -> l ->> n
  
  public export
  implementation Preorder (Jay g) (->>) where
    reflexive = ReduceRefl
    transitive a b c ab bc = ReduceTrans ab bc

data Progress : Jay g -> Type where
  Step : m ~> n -> Progress m
  Done : Normal m -> Progress m


progress : (t : Jay g) -> Progress t
progress (^ x) = Done (Term' $ Term x)
progress (\\ x) with (progress x)
  progress (\\ x) | (Step y) = Step (Zeta y)
  progress (\\ x) | (Done y) = Done (Lam x y)
progress ((\\ x) |> y) = Step Beta

progress ((^ x) |> y) with (progress y)
  progress ((^ x) |> y) | (Step z) = Step (Xi2 z)
  progress ((^ x) |> y) | (Done z) = Done (Term' (App (Term x) z))

progress ((x |> z) |> y) with (progress (x |> z))
  progress ((x |> z) |> y) | (Step w) = Step (Xi w)
  progress ((x |> z) |> y) | (Done w) with (progress y)
    progress ((x |> z) |> y) | (Done w) | (Step v) = Step (Xi2 v)
    progress ((x |> z) |> y) | (Done (Term' w)) | (Done v) = 
      Done (Term' (App w v))

namespace Evaluator
  public export
  Gas : Type
  Gas = Nat
  
  public export
  data Finished : Jay g -> Type where
    Done : Normal n -> Finished n
    Out : Finished n

data Steps : Jay g -> Type where
 MkSteps : l ->> n -> Finished n -> Steps l

eval : Gas -> (l : Jay g) -> Steps l 
eval 0 l = MkSteps (ReduceRefl l) Out
eval (S k) l with (progress l)
  eval (S k) l | (Done x) = MkSteps (ReduceRefl l) (Done x)
  eval (S k) m | (Step x) with (eval k m)
    eval (S k) m | (Step x) | (MkSteps y z) = 
      MkSteps y z

zero' : {g : _} -> Jay g
zero' = \\ \\ ^0

suc' : {g : _} -> Jay g -> Jay g
suc' m = (\\ \\ \\ (^1 |> ^2)) |> m

case' : {g : _} -> Jay g -> Jay g -> Jay (S g) -> Jay g
case' l m n = l |> (\\ n) |> m

mu : {g : _} -> Jay (S g) -> Jay g
mu x = (\\ ((\\ (^1 |> (^0 |> ^0))) |> (\\ (^1 |> (^0 |> ^0))))) |> (\\ x)

two' : {g : _} ->  Jay g
two' = suc' (suc' zero')

four' : {g : _} -> Jay g
four' = suc' (suc' (suc' (suc' zero')))

plus' : {g : _} -> Jay g
plus' = mu $ \\ \\ case' (^1) (^0) (suc' $ (^3) |> (^0) |> (^1))

mult' : {g : _} -> Jay g
mult' = mu $ \\ \\ case' (^1) (suc' zero') 
                              (plus' |> (^1) |> ((^3) |> (^0) |> (^1)))

public export
appL_cong : {l, l', m : _} 
         -> l ->> l'
         -> l |> m ->> l' |> m
appL_cong (Step x) = Step (Xi x)
appL_cong (ReduceRefl l') = ReduceRefl (l' |> m)
appL_cong (ReduceTrans ((Step x)) y) = 
  ReduceTrans (Step (Xi x)) (appL_cong y)
appL_cong (ReduceTrans ((ReduceRefl l)) y) = 
  ReduceTrans (ReduceRefl (l |> m)) (appL_cong y)
appL_cong (ReduceTrans ((ReduceTrans x z)) y) =  
  ReduceTrans (ReduceTrans (appL_cong x) 
                           (ReduceTrans (appL_cong z) 
                                        (ReduceRefl _)))
                                        (appL_cong y)
 
public export
appR_cong : {l, m', m : _} 
         -> m ->> m'
         -> l |> m ->> l |> m'
appR_cong (Step x) = Step (Xi2 x)
appR_cong (ReduceRefl l') = ReduceRefl (l |> m)
appR_cong (ReduceTrans ((Step x)) y) =
  ReduceTrans (Step (Xi2 x)) (appR_cong y)
appR_cong (ReduceTrans ((ReduceRefl l)) y) = ?asjiod
  ReduceTrans (ReduceRefl (_ |> _)) (appR_cong y)
appR_cong (ReduceTrans ((ReduceTrans x z)) y) = 
  ReduceTrans (ReduceTrans (appR_cong x) 
                           (ReduceTrans (appR_cong z) 
                                        (ReduceRefl _)))
                                        (appR_cong y)
 
public export
abs_cong : n ->> n' -> \\ n ->> \\ n'
abs_cong (Step x) = Step (Zeta x)
abs_cong (ReduceRefl n') = ReduceRefl (\\ n')
abs_cong (ReduceTrans x y) = 
  ReduceTrans (abs_cong x) (abs_cong y)

