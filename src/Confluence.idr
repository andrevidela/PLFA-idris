module Confluence

import Untyped
import Equality
import Substitution

infix 2 =->
infixr 2 =->*

data (=->) : (Jay g) -> (Jay g) -> Type where
  Pvar : (^x) =-> (^x)

  Pabs : {n, n' : Jay (S g)} -> n =-> n' -> \\ n =-> \\ n'

  Papp : {l, l', m, m' : Jay g}
      -> l =-> l'
      -> m =-> m'
      -> l |> m =-> l' |> m'

  Pbeta : {n, n' : Jay (S g)}
       -> {m, m' : Jay g}
       -> (n =-> n')
       -> (m =-> m')
       -> ((\\ n) |> m) =-> (substOne n' m')

par_refl : ( m : Jay g) -> m =-> m
par_refl ((^) x) = Pvar
par_refl ((\\) x) = Pabs (par_refl x)
par_refl (x |> y) = Papp (par_refl x) (par_refl y)


data (=->*) : (a, b : Jay g) -> Type where
  ReduceStep : a =-> b -> a =->* b
  ReduceRefl : (t : Jay g) -> t =->* t
  ReduceTrans : {b : Jay g } -> a =->* b -> b =->* c -> a =->* c

n : {g : _} -> Jay g -> Jay g
n a = (\\ ^0 |> ^0) |> ((\\ ^0) |> a)

m1 : {g : _} -> Jay g -> Jay g
m1 a = (\\ ^0 |> ^0) |> a

m2 : {g : _} -> Jay g -> Jay g
m2 a = (\\ ^0 |> ^0) |> ((\\ ^0) |> a)

n' : {g : _} -> Jay g -> Jay g
n' a = a |> a

beta_par : {m, n : _} -> m ~> n -> m =-> n
beta_par (Xi x) = Papp (beta_par x) (par_refl _)
beta_par (Xi2 x) = Papp (par_refl _) (beta_par x)
beta_par Beta = Pbeta (par_refl _) (par_refl _)
beta_par (Zeta x) = Pabs (beta_par x)

beta_pars : {m, n : _} -> m ->> n -> m =->* n
beta_pars (Step x) = ReduceStep (beta_par x)
beta_pars (ReduceRefl n) = ReduceRefl _
beta_pars (ReduceTrans x y) = ReduceTrans (beta_pars x) (beta_pars y)

par_betas : {m, n : _} -> m =-> n -> m ->> n
par_betas (Pvar) = ReduceRefl _
par_betas (Pabs x) = abs_cong (par_betas x )
par_betas (Papp x y {l} {l'} {m} {m'}) =
  begin (->>) $
    (l |> m ) -< (appL_cong (par_betas x) ) >-
    (l' |> m ) -< appR_cong (par_betas y) >-
    (l' |> m' ) -< ReduceRefl _ >-
    End (l' |> m')
par_betas {m=(\\ n) |> m} (Pbeta {n} {m} {m'} {n'} x y) = begin (->>) $
       ((\\n) |> m) -< appL_cong (abs_cong $ par_betas x) >-
       ((\\n') |> m) -< appR_cong (par_betas y) >-
       ((\\n') |> m') -< Step Beta >-
       End (subst (substZero m') n')

pars_betas : {m, n : _} -> m =->* n -> m ->> n
pars_betas (ReduceStep x) = par_betas x
pars_betas (ReduceRefl n) = ReduceRefl n
pars_betas (ReduceTrans x y) = ReduceTrans (pars_betas x) (pars_betas y)

ParSubst : {g : _} -> Subst g d -> Subst g d -> Type
ParSubst sig sig' = (x : Elem g) -> sig x =-> sig' x

par_rename : {rho : Rename g d} -> {x, x' : Jay g} -> x =-> x' -> rename rho x =-> rename rho x'
par_rename Pvar = Pvar
par_rename (Pabs x) = Pabs (par_rename x)
par_rename (Papp x y) = Papp (par_rename x) (par_rename y)
par_rename (Pbeta a b {n'} {m'}) with (Pbeta (par_rename {rho = ext rho} a) (par_rename {rho = rho} b))
  par_rename (Pbeta a b {n'} {m'}) | rec =
    let prf = rename_subst_commute {n=n'} {m=m'} {rho}
     in rewrite sym prf in rec

par_subst_exts : {sig, tau : Subst g d } -> ParSubst sig tau -> ParSubst (exts sig) (exts tau)
par_subst_exts f FZ = Pvar
par_subst_exts f (FS x) = par_rename (f x)

subst_par : {sig, tau : _ } -> {m, m' : Jay g}
         -> ParSubst sig tau -> m =-> m' -> subst sig m =-> subst tau m'
subst_par f {m=(^x)} Pvar = f x
subst_par f {m=(\\ n)} (Pabs x) = Pabs (subst_par (par_subst_exts f) x)
subst_par f {m=(a |> b)} (Papp x y) = Papp (subst_par f {m=a} x) (subst_par f {m=b} y)
subst_par f {m=((\\n) |> m)} (Pbeta {n'} {m'}x y) with
  (Pbeta (subst_par {sig=exts sig} {tau=exts tau} {m=n} (par_subst_exts f) x) (subst_par f y))
  subst_par f {m=((\\n) |> m)} (Pbeta {n'} {m'} x y) | rec
    = let prf = subst_commute {sig=tau} {m=m'} {n=n'} in
          rewrite sym prf in rec

par_subst_zero : m =-> m' -> ParSubst (substZero m) (substZero m')
par_subst_zero y FZ = y
par_subst_zero y (FS x) = Pvar

sub_par : {n, n' : _} -> {m, m' : Jay g} -> n =-> n' -> m =-> m' -> substOne n m =-> substOne n' m'
sub_par x y = subst_par (par_subst_zero y) x

reduce : Jay g -> Jay g
reduce (^ x) = ^ x
reduce (\\ x) = \\ reduce x
reduce ((\\ x) |> y) = substOne (reduce x) (reduce y)
reduce (x |> y) = reduce x |> reduce y

par_triangle : a =-> b -> b =-> reduce a
par_triangle Pvar = Pvar
par_triangle (Pabs x) = Pabs (par_triangle x)
par_triangle (Pbeta x y) = sub_par (par_triangle x) (par_triangle y)
par_triangle (Papp {l = (\\_)} (Pabs x) y) = Pbeta (par_triangle x) (par_triangle y)
par_triangle (Papp {l = (^ _)} x y) = Papp (par_triangle x) (par_triangle y)
par_triangle (Papp {l = (_ |> _)} x y) = Papp (par_triangle x) (par_triangle y)

par_diamond : {m : _} -> m =-> n -> m =-> n' -> (l : Jay g ** (n =-> l, n' =-> l))
par_diamond x y = (reduce m ** (par_triangle x, par_triangle y))

strip : {m, n, n' : _} -> m =-> n -> m =->* n' -> (l : Jay g ** (n =->* l, n' =-> l))
strip x (ReduceStep y) with (par_diamond x y)
  strip x (ReduceStep y) | (l' **  (nl, n'l)) = (l' ** (ReduceStep nl, n'l))
strip x (ReduceRefl n') = (n ** (ReduceRefl n, x))
strip x (ReduceTrans y z {b} ) with (strip x y)
  strip x (ReduceTrans y z {b} ) | (l' ** (nl, n'l)) = let (h ** (v, w)) = strip n'l z in
                                                           (h ** (ReduceTrans nl v, w))

par_confluence : {l, m1, m2 : _} -> l =->* m1 -> l =->* m2 -> (n : Jay g ** (m1 =->* n, m2 =->* n))
par_confluence (ReduceStep x) y with (strip x y)
  par_confluence (ReduceStep x) y | (z ** (a, b)) = (z ** (a, ReduceStep b))
par_confluence (ReduceRefl m1) y = (m2 ** (y, ReduceRefl m2))
par_confluence (ReduceTrans x z {b}) y with (par_confluence x y)
  par_confluence (ReduceTrans x z {b}) y | (w ** (r, s)) with (par_confluence z r)
    par_confluence (ReduceTrans x z {b}) y | (w ** (r, s)) | (w' ** (r', s'))
      = (w' ** (r', ReduceTrans s s'))

confluence : {l, m1, m2 : _} -> l ->> m1 -> l ->> m2 -> (n ** (m1 ->> n, m2 ->> n))
confluence x y with (par_confluence (beta_pars x) (beta_pars y))
  confluence x y | (n ** (m1n, m2n)) = (n ** (pars_betas m1n, pars_betas m2n))














