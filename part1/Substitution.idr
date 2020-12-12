module Substitution

import Equality
import Untyped

funExt : {0 f, g : a -> b} -> ((x : a) -> f x === g x) -> f = g

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

sub_tail : (Up <.> (m <:> sig)) = sig
sub_tail = funExt $ \x => Refl

sub_eta : subst sig (^ FZ) <:> (Up <.> sig) = sig
sub_eta = funExt $ \case FZ => Refl
                         (FS x) => Refl

z_shift : ((^ FZ) <:> Up) = Substitution.ids
z_shift = funExt $ \case FZ => Refl
                         (FS x) => Refl

sub_idL : Substitution.ids <.> sig = sig
sub_idL = funExt $ \x => Refl

sub_dist : {m : _} -> {sig, tau : _} -> ((m <:> sig) <.> tau) = ((subst tau m) <:> (sig <.> tau))
sub_dist = funExt $ \case FZ => Refl
                          (FS x) => Refl

sub_app : subst sig (l |> m) = (subst sig l) |> (subst sig m)
sub_app = Refl

---- Congruences

cong_app : {0 b : a -> Type} -> {0 f, g : (x : a) -> b x} ->
           f = g -> (x : a) -> f x = g x
cong_app Refl x = Refl

cong_ext : (rho, rho' : Rename g d) -> (rho = rho')
        -> ext rho = ext rho'
cong_ext rho rho' prf = cong ext prf

cong_rename : (rho, rho' : Rename g d) -> rho = rho' 
           -> rename rho m = rename rho' m
cong_rename rho rho' prf = cong (\x =>  rename x m) prf

cong_exts : Subst g d -> sig = sig' -> exts sig = exts sig'
cong_exts f prf = cong exts prf

cong_sub : sig = sig' -> m = m' -> 
           Untyped.subst sig m = Untyped.subst sig' m'
cong_sub prf prf1 = cong2 Untyped.subst prf prf1

cong_sub_zero : (m, m' : Jay b) -> m = m' -> substZero m = substZero m'
cong_sub_zero m m' prf = cong substZero prf

cong_cons : (sig, tau : Subst g d) -> m = n -> sig = tau 
         -> (m <:> sig) = (n <:> tau)
cong_cons sig tau prf prf1 = cong2 (<:>) prf prf1

cong_seq : (sig, sig' : Subst g d) -> (tau, tau' : Subst d s) -> sig = sig' -> tau = tau'
        -> (sig <.> tau) = (sig' <.> tau')
cong_seq sig sig' tau tau' prf prf1 = funExt lemma
  where
    lemma : (x : Elem g) -> (sig <.> tau) x = (sig' <.> tau') x
    lemma x = begin (===) $ 
              ((sig <.> tau ) x) -< Refl >- 
              (subst tau (sig x)) -< cong (subst tau) (cong_app prf x) >- 
              (subst tau (sig' x)) -< cong_sub {-sig'-} prf1 Refl >- 
              (subst tau' (sig' x)) -< Refl >- 
              End ((sig' <.> tau') x)

ren_ext : {0 rho : Rename g d} ->  ren (ext rho) = exts (ren rho)
ren_ext = funExt $ lemma
  where
    lemma : (x : Elem (S g)) -> ren (ext rho) x = exts (ren rho) x
    lemma FZ = Refl
    lemma (FS x) = Refl

rename_subst_ren : {0 g : Nat} -> {rho : Rename g d} -> (m : Jay g)
                -> rename rho m = subst (ren rho) m
rename_subst_ren (^ x) = Refl
rename_subst_ren {rho=r} (\\ x) = 
  begin (===) $
    rename r (\\ x) 
      -< cong (\\) (rename_subst_ren{rho = ext r} x) >-
    (\\ (subst (ren (ext r)) x)) 
      -< cong (\\) (cong_sub {-(ren r)-} (ren_ext )  Refl) >-
    (\\ (subst (exts (ren r)) x)) 
      -< Refl >-
    End (subst (ren r) (\\ x))
rename_subst_ren (x |> y) = 
  cong2 (|>) (rename_subst_ren x) (rename_subst_ren y)

ren_shift : Substitution.ren FS = Up 
ren_shift = funExt (\x => Refl)

rename_shift : {m : _} -> rename FS m = subst Up m
rename_shift = begin (===) $ 
               rename FS m -< rename_subst_ren m >-
               subst (ren FS) m -< cong_sub ren_shift Refl >-
               End (subst Up m)

exts_cons_shift : {sig : _} -> exts sig = (^ FZ <:> (sig <.> Up))
exts_cons_shift = funExt $ \case FZ => Refl
                                 (FS x) => rename_shift

ext_cons_Z_shift : {0 rho : _} -> ren (ext rho) = ^ FZ <:> (ren rho <.> Up)
ext_cons_Z_shift = funExt $ \case FZ => Refl
                                  (FS x) => Refl

subst_Z_cons_ids : {0 m : _} -> substZero m = (m <:> Substitution.ids)
subst_Z_cons_ids = funExt $ \case FZ => Refl
                                  (FS x) => Refl

sub_abs : {sig : Subst g d} -> {0 n : Jay (S g)} -> 
          (subst sig (\\ n)) = (\\ (subst ((^ FZ) <:> (sig <.> Up)) n))
sub_abs = cong (\\) $ cong_sub (exts_cons_shift) Refl

exts_ids : exts Substitution.ids = Substitution.ids
exts_ids = funExt $ \case FZ => Refl
                          (FS x) => Refl

sub_id : (m : Jay d) -> subst Substitution.ids m = m
sub_id (^ x) = believe_me $ Refl {x = ^x}
sub_id (\\ x) = cong (\\) $ begin (===) $ 
                (subst (exts Substitution.ids) x)  -< cong_sub exts_ids Refl >-
                subst Substitution.ids x -< sub_id x >-
                End x
sub_id (x |> y) = cong2 (|>) (sub_id x) (sub_id y)

rename_id : {m : _} -> rename (\x => x) m = m
rename_id = begin (===) $ 
            rename (\x => x) m -< rename_subst_ren m >-
            subst (ren (\x => x)) m -< sub_id m >-
            End m

sub_idR : {sig : Subst g d} -> (sig <.> Substitution.ids) = sig
sub_idR = funExt $ \x => sub_id _

composeExt : {rho : Rename d s} -> {rho' : Rename g d}
          -> ((ext rho) . (ext rho')) = ext (rho . rho') 
composeExt = funExt $ \case FZ => Refl
                            (FS x) => Refl

compose_rename : (m : Jay g) -> {rho : Rename d s} -> {rho' : Rename g d}
              -> rename rho (rename rho' m) = rename (rho . rho') m
compose_rename (^ x) = Refl
compose_rename (\\ x) = cong (\\) $ begin (===) $
   rename (ext rho) (rename (ext rho') x) -< compose_rename x >-
   rename ((ext rho) . (ext rho')) x  -< cong_rename _ _ composeExt >-
   End (rename (ext (\x => rho (rho' x))) x)
compose_rename (x |> y) = cong2 (|>) (compose_rename x) (compose_rename y) 

-- TODO
commute_subst_rename : {g, d: _} -> (m : Jay g) -> {sig : Subst  g d} 
  -> {rho : {g' : _} -> Rename g' (S g')}
  -> ((x : Elem g) -> Untyped.exts sig (rho x) = rename (rho) (sig x))
  -> subst (exts sig) (rename (rho) m) = rename (rho) (subst sig m)
commute_subst_rename (^ t) f = f t
commute_subst_rename (\\ x) {rho=r} {sig=s} f = 
  let 
    checkRho : {g'' : _} -> Rename g'' (S g'')
    checkRho {g''=0} x = absurd x
    checkRho {g''=(S k)} x = ext r x
    fn : (x : Fin (S g)) -> exts (exts s) (ext r x) = rename (ext r) (exts s x)
    fn = ?pls
  in cong (\\) $ ?dunno
                                
commute_subst_rename (a |> b) f = 
  cong2 (|>) (commute_subst_rename {rho} a f )
             (commute_subst_rename {rho} b f)

-- TODO
exts_seq : {sig1 : Subst g d} -> {sig2 : Subst d d'} -> 
           (exts sig1 <.> exts sig2) = exts (sig1 <.> sig2)

-- TODO
sub_sub : {sig1 : Subst g d} -> {sig2 : Subst d s}
       -> subst sig2 (subst sig1 m) = subst (sig1 <.> sig2) m

-- TODO
rename_subst : {rho : Rename g d } -> {sig : Subst d d'}
            -> subst sig (rename rho m) = subst (sig . rho) m

-- TODO
sub_assoc : {sig : Subst g d} -> {tau : Subst d s} -> {tht : Subst s p}
         -> (sig <.> tau) <.> tht = sig <.> (tau <.> tht)

-- TODO
subst_zero_exts_cons : {sig : Subst g d}
  -> exts sig <.> substZero m = (m <:> sig)

-- TODO
subst_commute : {n : Jay (S g)} -> {m : Jay g} -> {sig : Subst g d} 
  ->  (substOne (subst (exts sig) n) (subst sig m)) = subst sig (substOne n m)

-- TODO
rename_subst_commute : 
  substOne (rename (ext rho) n) (rename rho m) = rename rho (substOne n m)

subst2 : Jay (S (S g)) -> Jay g -> Jay (S g)
subst2 n m = subst (exts (substZero m)) n

substitution : substOne (substOne m n) l = substOne (subst2 m l) (substOne n l)
substitution = sym subst_commute




