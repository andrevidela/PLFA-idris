module Substitution

import Equality
import Untyped

funExt : {f, g : a -> b} -> ((x : a) -> f x === g x) -> f = g

public export
Rename : Context -> Context -> Type
Rename g d = Elem g -> Elem d

public export
Subst : Context -> Context -> Type
Subst g d = Elem g -> Jay d

s : Subst g d -> Jay g -> Jay d
s = subst

ids : Subst g g
ids x = ^ x

Up : Subst g (S g)
Up x = ^ (FS x)

infixr 6 <:>

(<:>) : Jay d -> Subst g d -> Subst (S g) d
(<:>) m sig FZ = m
(<:>) m sig (FS x) = sig x

infixr 5 <.>

(<.>) : Subst g d -> Subst d s -> Subst g s
(<.>) sig tau = (subst tau) . sig

ren : Rename g d -> Subst g d
ren rho = ids . rho

sub_head : subst (m <:> sig) (^ FZ) = m
sub_head = Refl

sub_tail : {m : _} -> {sig : Subst g d} -> (Up <.> (m <:> sig)) = sig
sub_tail = funExt $ \x => Refl

sub_eta : {sig : _} -> subst sig (^ FZ) <:> (Up <.> sig) = sig
sub_eta = funExt $ \case FZ => Refl
                         (FS x) => Refl

z_shift : ((^ FZ) <:> Up) = Substitution.ids
z_shift = funExt $ \case FZ => Refl
                         (FS x) => Refl

sub_idL : {g, d : _} -> {sig : Subst g d} -> Substitution.ids <.> sig = sig
sub_idL = funExt $ \x => Refl

sub_dist : {m : _} -> {sig, tau : _} -> ((m <:> sig) <.> tau) = ((subst tau m) <:> (sig <.> tau))
sub_dist = funExt $ \case FZ => Refl
                          (FS x) => Refl

sub_app : subst sig (l |> m) = (subst sig l) |> (subst sig m)
sub_app = Refl

---- Congruences

cong_app : {b : a -> Type} -> {f, g : (x : a) -> b x} ->
           f = g -> (x : a) -> f x = g x
cong_app Refl x = Refl

cong_ext : (rho, rho' : Rename g d) -> (rho = rho')
        -> ext rho = ext rho'
cong_ext rho rho' prf = cong ext prf

cong_rename : {m : _} -> (rho, rho' : Rename g d) -> rho = rho' 
           -> rename rho m = rename rho' m
cong_rename rho rho' prf = cong (\x =>  rename x m) prf

cong_exts : Subst g d -> sig = sig' -> exts sig = exts sig'
cong_exts f prf = cong exts prf

cong_sub : (Subst g d) -> sig = sig' -> m = m' -> 
           Untyped.subst sig m = Untyped.subst sig' m'
cong_sub f prf prf1 = cong2 Untyped.subst prf prf1

cong_sub_zero : (m, m' : Jay b) -> m = m' -> substZero m = substZero m'
cong_sub_zero m m' prf = cong substZero prf

cong_cons : (sig, tau : Subst g d) -> m = n -> sig = tau 
         -> (m <:> sig) = (n <:> tau)
cong_cons sig tau prf prf1 = cong2 (<:>) prf prf1

cong_seq : {d : _} -> (sig, sig' : Subst g d) -> (tau, tau' : Subst d s) -> sig = sig' -> tau = tau'
        -> (sig <.> tau) = (sig' <.> tau')
cong_seq sig sig' tau tau' prf prf1 = funExt lemma
  where
    lemma : (x : Elem g) -> (sig <.> tau) x = (sig' <.> tau') x
    lemma x = begin (===) $ 
              ((sig <.> tau ) x) -< Refl >- 
              (subst tau (sig x)) -< cong (subst tau) (cong_app prf x) >- 
              (subst tau (sig' x)) -< cong_sub sig' prf1 Refl >- 
              (subst tau' (sig' x)) -< Refl >- 
              End ((sig' <.> tau') x)

ren_ext : {rho : Rename g d} -> ren (ext rho) = exts (ren rho)
ren_ext = funExt $ lemma
  where
    lemma : (x : Elem (S g)) -> ren (ext rho) x = exts (ren rho) x
    lemma FZ = Refl
    lemma (FS x) = Refl

rename_subst_ren : {g : Nat} -> {rho : Rename g d} -> (m : Jay g)
                -> rename rho m = subst (ren rho) m
rename_subst_ren (^ x) = Refl
rename_subst_ren {rho=r} (\\ x) = 
  begin (===) $
    rename r (\\ x) 
      -< cong (\\) (rename_subst_ren{rho = ext r} x) >-
    (\\ (subst (ren (ext r)) x)) 
      -< cong (\\) (cong_sub (ren r) (ren_ext )  Refl) >-
    (\\ (subst (exts (ren r)) x)) 
      -< Refl >-
    End (subst (ren r) (\\ x))
rename_subst_ren (x |> y) = 
  cong2 (|>) (rename_subst_ren x) (rename_subst_ren y)











