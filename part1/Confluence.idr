module Confluence 

import Untyped
import Equality

infix 2 =->
infixr 2 =->*

data (=->) : (Jay g) -> (Jay g) -> Type where
  Pvar : (^x) =-> (^x)

  Pabs : {n, n' : Jay (S g)} -> n =-> n' -> \\ n =-> \\ n'

  Papp : {0 l, l', m, m' : Jay g}
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
  ReduceTrans : a =->* b -> b =->* c -> a =->* c

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
par_betas {m=(\\ k |> l)} (Pbeta {n=k} {m=l} {m'=w} {n'=v} x y) = begin (->>) $ 
  _ -< ?par_betas_rhs_4 >-
  End (subst (substZero c) d)















