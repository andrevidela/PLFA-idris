
module Properties

import Lambda

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
reduce_wont_be_value x y = values_wont_reduce y x

data Canonical : TypedTerm -> Type where
  CanonicalLam : Nil && x .: a |- n .: b ->
                 ---------------------
                 Canonical ((\\x ==> n) .: a =>> b)
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
  progress (CaseElim x y z) | (Step w) = ?progress_rhs_1
  progress (CaseElim x y z) | (Done w) = ?progress_rhs_2
progress (MuRec x) = Step BetaMu




