
module Preservation

import Properties
import Lambda


notImpl : ([] &. (xi .: a)) |- (t .: b) -> ((\\) xi t) ->> n -> Void
notImpl _ (Step (Xi1 y)) impossible
notImpl _ (Step (Xi2 y z)) impossible
notImpl _ (Step (BetaLam y)) impossible
notImpl _ (Step (XiSucc y)) impossible
notImpl _ (Step (XiCase y)) impossible
notImpl _ (Step BetaZero) impossible
notImpl _ (Step (BetaSucc y)) impossible
notImpl _ (Step BetaMu) impossible
notImpl x (ReduceRefl ((\\) v w)) = 
  let r = ReduceRefl (\\ v ==> w) in notImpl x r
notImpl x (ReduceTrans y z) = notImpl x y

zeroLemma : Zero ->> n -> [] |- (n .: NatType)

preserve : {0 m, n : Term} -> [] |- m .: a -> m ~> n -> [] |- n .: a
preserve (Elim x z) (Xi1 y) = (preserve x y) `Elim` z
preserve (Elim x z) (Xi2 y w) = x `Elim` preserve z w
preserve (Elim (Impl x) z) (BetaLam {arg} y) = substitution arg z x
preserve (SuccNat x) (XiSucc y) = SuccNat (preserve x y)
preserve (CaseElim x z w) (XiCase y) = CaseElim (preserve x y) z w
preserve (CaseElim ZeroNat z w) BetaZero = z
preserve (CaseElim (SuccNat x) z w) (BetaSucc {x=str} y) = 
  substitution str x w
preserve (MuRec {x=str} x) BetaMu = substitution str (MuRec x) x

Gas : Type
Gas = Nat

data Finished : (n : Term) -> Type where
  Done : Value n -> Finished n
  RanOut : Finished n

data Steps : Term -> Type where
  MkSteps : {nTerm : Term} -> l ->> nTerm -> Finished nTerm -> Steps l

eval :  {l : Term} -> Gas -> [] |- l .: a -> Steps l
eval 0 x = MkSteps (ReduceRefl l) RanOut
eval (S k) x with (progress x)
  eval (S k) x | (Step y) with (eval k (preserve x y))
    eval (S k) x | (Step y) | (MkSteps z w) = 
      MkSteps (ReduceTrans (Step y) z) w
  eval (S k) x | (Done y) = MkSteps (ReduceRefl l) (Done y)

  
-- 
-- chuchSucc : Preservation.eval 100 (jTwo `Elim` (jSuccChurch `Elim` jZero))
--           = MkSteps ?whut (Done (VSucc (VSucc VZero)))
-- chuchSucc = Refl

Normal : Term -> Type
Normal m = {n : Term} -> Not (m ~> n)

Stuck : Term -> Type
Stuck m = (Normal m, Not (Value m))

unstuck : {m : _} -> [] |- m .: a -> Not (Stuck m)
unstuck x y = 
  case progress x of
      (Done val) => snd y val
      (Step step) => fst y step

preserves : [] |- m .: a
         -> m ->> n
         -> [] |- n .: a
preserves x (Step y) = preserve x y
preserves x (ReduceRefl n) = x
preserves x (ReduceTrans y z) = 
  let v = preserves x y 
      w = preserves v z 
   in w
     
-- prnounced "whatdogs"
wttdgs : {n : _} -> [] |- m .: a
      -> m ->> n
      -> Not (Stuck n)
wttdgs x y z = 
  let t = preserves x y in
      case progress t of
          (Done val) => snd z val  
          (Step step) => fst z step

cong4 : {p, q, l, m, n : Type} -> 
        {a, x : p} -> 
        {b, y : q} -> 
        {c, z : l} -> 
        {d, w : m} -> 
        (f : p -> q -> l -> m -> n) ->
        a = x -> b = y -> c = z -> d = w -> 
        f a b c d = f x y z w
cong4 f Refl Refl Refl Refl = Refl

det : m ~> m' -> m ~> m'' -> m' = m''


