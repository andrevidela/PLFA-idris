module BigStep

import Equality
import Untyped
import Substitution

infixl 5 |- -- big step judgement
infixl 6 \/ -- reduction
infix 9 ~~ -- equivalence
infix 9 ~~& -- equivalence

infixr 6 &:

%default total

mutual
  ClosEnv : Context -> Type
  ClosEnv gam = Elem gam -> Clos

  data Clos : Type where
    Closed : {g : _} -> (m : Jay g) -> ClosEnv g -> Clos


EmptyEnv : ClosEnv Z
EmptyEnv x = absurd x

(&:) : ClosEnv g -> Clos -> ClosEnv (S g)
(&:) f x FZ = x
(&:) f x (FS y) = f y

data Reduction : Context -> Type where
  (\/) : (j : Jay g) -> (c : Clos) -> Reduction g

data (|-) : ClosEnv g -> Reduction g -> Type where

  BVar : {gam : ClosEnv g} -> {x : Elem g} -> {del : ClosEnv d} -> {m : Jay d}
      -> gam x === Closed m del
      -> def |- m \/ v
      -> gam |- (^x) \/ v

  BLam : {m : Jay (S g)} -> gam |- (\\ m) \/ Closed (\\m) gam

  BApp : {del, n : _} -> gam |- l \/ Closed (\\n) del
      -> gam &: Closed m gam |- n \/ v
      -> gam |- (l |> m) \/ v

big_determ : {0 v, v' : Clos} -> gam |- m \/ v -> gam |- m \/ v' -> v === v'
big_determ (BVar prf x) (BVar prf1 y) = ?big_determ_rhs_4
big_determ BLam BLam = Refl
big_determ (BApp x z) (BApp y w) with (big_determ x y)
  big_determ (BApp x z) (BApp y w) | Refl = big_determ z w

(~~) : Clos -> Jay Z -> Type
(~~) (Closed {g} m gam) n =
  (sig : Subst g Z ** ((x : Elem g) -> gam x ~~ sig x, n === subst sig m))

(~~&) : ClosEnv g -> Subst g Z -> Type
(~~&) gam del = (x : Elem g) -> gam x ~~ del x

equiv_e_id : EmptyEnv ~~& ids
equiv_e_id FZ impossible
equiv_e_id (FS x) impossible

ext_subst : Subst g d -> Jay d -> Subst (S g) d
ext_subst sig n = subst (substZero n) . exts sig

subst_zero_exts : (subst (substZero m) . exts sig) (FS x) === sig x
subst_zero_exts = ?whutosn

equiv_e_ext :  gam ~~& sig -> v ~~ n
           -> (gam &: v) ~~& ext_subst sig n
equiv_e_ext f y FZ = y
equiv_e_ext f y (FS x) = rewrite subst_zero_exts {m=n} {sig} {x} in f x

bigStepEquiv : {g : _} -> {gam : ClosEnv g} -> {sig : Subst g Z} -> {v : Clos} -> {m : Jay g}
            -> gam |- m \/ v -> gam ~~& sig
            -> (n ** (subst sig m ->> n, v ~~ n))
bigStepEquiv (BVar {x} prf v) f with (gam x)
  bigStepEquiv (BVar {x} Refl v) f | (Closed l del) =
    case f x of
         pat => ?wo
bigStepEquiv {v=Closed (\\n) g} BLam f =
  (subst sig (\\ n) ** (ReduceRefl (subst sig (\\ n)), (sig ** (f, Refl))))
bigStepEquiv {m=l |> m} (BApp {n = n} {del} x nv) f =
  let (g' ** (z, (tau ** (s, prf)))) = (bigStepEquiv {sig} x f)
      p = bigStepEquiv {sig = ext_subst tau (subst sig m)} nv ()
   in (?n' ** (?bigStepEquiv_rhs_5, ?vn'))



