
module Properties

import Equality
import Isomorphism
import Connectives
import Lambda

data Exists : (this : type -> Type) -> Type where
    Evidence : (0 value : type)
            -> (prf : this value)
            -> Exists this

values_wont_reduce : {0 m, n : Term} -> Value m -> Not (m ~> n)
values_wont_reduce VLam (Xi1 x) impossible
values_wont_reduce VLam (Xi2 x y) impossible
values_wont_reduce VLam (BetaLam x) impossible
values_wont_reduce VLam (XiSucc x) impossible
values_wont_reduce VLam (XiCase x) impossible
values_wont_reduce VLam BetaZero impossible
values_wont_reduce VLam (BetaSucc x) impossible
values_wont_reduce VLam BetaMu impossible
values_wont_reduce VZero (Xi1 x) impossible
values_wont_reduce VZero (Xi2 x y) impossible
values_wont_reduce VZero (BetaLam x) impossible
values_wont_reduce VZero (XiSucc x) impossible
values_wont_reduce VZero (XiCase x) impossible
values_wont_reduce VZero BetaZero impossible
values_wont_reduce VZero (BetaSucc x) impossible
values_wont_reduce VZero BetaMu impossible
values_wont_reduce (VSucc x) (XiSucc y) = values_wont_reduce x y

reduce_wont_be_value : m ~> n -> Not (Value m)
reduce_wont_be_value = flip values_wont_reduce

data Canonical : TypedTerm -> Type where

  CanonicalLam : Nil && xCan .: a |- n .: b ->
                 ---------------------
                 Canonical ((\\xCan ==> n) .: a =>> b)

  CanonicalZero : Canonical (Zero .: NatType)

  CanonicalSucc : Canonical (v .: NatType) ->
                  -------------------------
                  Canonical (Succ v .: NatType)

canonical : Nil |- v .: a -> Value v ->
            ---------------------------
            Canonical (v .: a)
canonical (Axiom _) VLam impossible
canonical (Axiom _) VZero impossible
canonical (Axiom _) (VSucc y) impossible
canonical (Impl x) y = CanonicalLam x
canonical (Elim _ _) VLam impossible
canonical (Elim _ _) VZero impossible
canonical (Elim _ _) (VSucc y) impossible
canonical ZeroNat y = CanonicalZero
canonical (SuccNat x) (VSucc v) = CanonicalSucc (canonical x v)
canonical (CaseElim _ _ _) VLam impossible
canonical (CaseElim _ _ _) VZero impossible
canonical (CaseElim _ _ _) (VSucc y) impossible
canonical (MuRec _) VLam impossible
canonical (MuRec _) VZero impossible
canonical (MuRec _) (VSucc y) impossible

value : Canonical (m .: a) ->
        ---------------------
        Value m
value (CanonicalLam x) = VLam
value CanonicalZero = VZero
value (CanonicalSucc x) = VSucc (value x)

typed : Canonical (m .: a) ->
        ---------------------
        Nil |- m .: a
typed (CanonicalLam x) = Impl x
typed CanonicalZero = ZeroNat
typed (CanonicalSucc x) = SuccNat (typed x)

data Progress : (m : Term) -> Type where
  Step : m ~> n -> Progress m
  Done : Value m -> Progress m

progress : Nil |- m .: a ->
           ----------------
           Progress m
progress (Axiom Z) impossible
progress (Axiom (S notEq x)) impossible
progress (Impl x) = Done VLam
progress ZeroNat = Done VZero
progress (SuccNat x) with (progress x)
  progress (SuccNat x) | (Step y) = Step (XiSucc y)
  progress (SuccNat x) | (Done y) = Done (VSucc y)
progress (Elim x y) with (progress x)
  progress (Elim x y) | (Step z) = Step (Xi1 z)
  progress (Elim x y) | (Done z) with (progress y)
    progress (Elim x y) | (Done z) | (Step w) = Step (Xi2 z w)
    progress (Elim x y) | (Done z) | (Done w) with (canonical x z)
      progress (Elim x y) | (Done z) | (Done w) | (CanonicalLam l) = Step (BetaLam w)
progress (CaseElim x y z) with (progress x)
  progress (CaseElim x y z) | (Step w) = Step (XiCase w)
  progress (CaseElim x y z) | (Done w) with (canonical x w)
    progress (CaseElim x y z) | (Done w) | CanonicalZero = Step BetaZero
    progress (CaseElim x y z) | (Done w) | (CanonicalSucc v) = Step (BetaSucc $ value v)
progress (MuRec x) = Step BetaMu


progress_iso : Progress m ~= (Value m |+| (Exists (m ~>)))
progress_iso = MkIso 
  (\case
    (Step x) => Right (Evidence _ x)
    (Done x) => Left x)
  (\case
    (Left x) => Done x
    (Right (Evidence value prf)) => Step prf) 
  (\case 
    (Step x) => Refx
    (Done x) => Refx )
  (\case
    (Left x) => Refx
    (Right (Evidence v prf)) => Refx)

varNotVal : Not (Value (^x))
varNotVal VLam impossible
varNotVal VZero impossible
varNotVal (VSucc y) impossible

appNotVal : Not (Value (l |> m))
appNotVal VLam impossible
appNotVal VZero impossible
appNotVal (VSucc x) impossible

caseNotVal : Value (Case l m x n) -> Void
caseNotVal VLam impossible
caseNotVal VZero impossible
caseNotVal (VSucc y) impossible

muNotVal : Not (Value (Mu x m))
muNotVal VLam impossible
muNotVal VZero impossible
muNotVal (VSucc y) impossible

isValue : Nil |- m .: a -> Dec (Value m)
isValue (Axiom x) = No varNotVal
isValue (Impl x) = Yes VLam
isValue (Elim x y) = No appNotVal
isValue ZeroNat = Yes VZero
isValue (SuccNat x) with (isValue x)
  isValue (SuccNat x) | (Yes prf) = Yes (VSucc prf)
  isValue (SuccNat x) | (No contra) = No (\(VSucc x) => contra x)
isValue (CaseElim x y z) = No caseNotVal
isValue (MuRec x) = No muNotVal

extend : {0 Γ, Δ : Ctxt} -> 
         (Γ >: x .: a -> 
          Δ >: x .: a) ->
         (Γ && y .: b >: x .: a -> 
          Δ && y .: b >: x .: a)
extend f Z = Z
extend f (S notEq z) = S notEq (f z)

rename : {0 Γ, Δ : Ctxt} -> 
         (Γ >: x .: a -> Δ >: x .: a) ->
         (Γ |- m .: a -> Δ |- m .: a)
rename f (Axiom y) = ?rename_rhs_1
rename f (Impl y) = ?rename_rhs_2
rename f (Elim y z) = ?rename_rhs_3
rename f ZeroNat = ?rename_rhs_4
rename f (SuccNat y) = ?rename_rhs_5
rename f (CaseElim y z w) = ?rename_rhs_6
rename f (MuRec y) = ?rename_rhs_7

-- nicer type signature using Subset

Subset : (f : a -> b -> Type) -> (g : a) -> (d : a) -> Type
Subset f g d = {0 xsub : b} -> f g xsub -> f d xsub

SubsetC : Ctxt -> Ctxt -> Type
SubsetC c1 c2 = Subset (>:) c1 c2

SubsetJ : Ctxt -> Ctxt -> Type
SubsetJ c1 c2 = Subset (|-) c1 c2

extend' : {0 Γ, Δ : Ctxt} -> 
         SubsetC Γ Δ  -> 
         ({0 y : Typed} -> SubsetC (Γ && y) (Δ && y))
extend' f Z = Z
extend' f (S notEq z) = S notEq (f z)

rename' : {0 Γ, Δ : Ctxt} -> 
          SubsetC Γ Δ -> 
          SubsetJ Γ Δ 
rename' f (Axiom y) = Axiom (f y)
rename' f (Impl y) = Impl (let e = extend' f in
                           rename' e y )
rename' f (Elim y z) = Elim (rename' f y) (rename' f z)
rename' f ZeroNat = ZeroNat
rename' f (SuccNat y) = SuccNat (rename' f y)
rename' f (CaseElim y z w) = CaseElim (rename' f y) (rename' f z) (rename' (extend' f) w)
rename' f (MuRec y) = MuRec (rename' (extend' f) y)
