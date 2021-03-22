module Inference


import Decidable.Equality
import Data.DPair
import Debrujn as DB

public export
Id : Type
Id = String

prefix 5 \\
infixl 7 |>
prefix 9 ^

infix 6 `∋` -- Checked / inherited 
infix 6 `∈` -- inferred / synthesized

infixr 0 ==> -- function application, like $
infixr 4 ~>  -- Single Reduction step
infixr 2 ->> -- "Reduces to"
infixr 7 =>> -- Type in Lambda calculus
infixr 8 `X` -- Product in Lambda calculus
infixl 5 ?= -- Type equality in lambda calculus

infixl 6 .: -- typed term
infixr 4 >: -- `in`
infixl 5 &. -- extend context
infixl 5 |- -- judgement Inferred
infixl 5 |= -- judgement Check

public export
(==>) : (a -> b) -> a -> b
(==>) f = f

data LType : Type where
  Nat' : LType
  (=>>) : Inference.LType -> Inference.LType -> LType
  X : Inference.LType -> Inference.LType -> LType

mutual 
  data TermInf : Type where --Term⁻
    (^) : Id -> TermInf
    (|>) : TermInf -> TermChk -> TermInf
    ToInf : TermChk -> Inference.LType -> TermInf
  
  data TermChk : Type where --Term⁺
    (\\) : Id -> TermChk -> TermChk
    Zero : TermChk
    Succ : TermChk -> TermChk
    Case : TermInf -> TermChk -> Id -> TermChk -> TermChk
    Mu : Id -> TermChk -> TermChk
    Prod : TermChk -> TermChk -> TermChk
    CaseProd : TermInf -> Id -> Id -> TermChk -> TermChk
    ToChk : TermInf -> TermChk

two : TermChk
two = Succ (Succ Zero)

plus : TermInf
plus = (Mu "p" ==> \\ "m" ==> \\ "n" ==>
          Case (^"m") (ToChk (^"n")) "m" (Succ $ ToChk (^"p" |> (ToChk $ ^"m") |> (ToChk $ ^"n")))) 
          `ToInf` (Nat' =>> Nat' =>> Nat')

twoPlusTwo : TermInf
twoPlusTwo = (plus |> two) |> two

public export
record Typed where
  constructor (.:)
  name : Id
  type : Inference.LType

-- Context
public export
data Context : Type where
  Nil : Context
  (&.) : Context -> Typed -> Context

-- namespace Terms
--   public export
--   record TypedTerm where
--     constructor (.:)
--     name : Term
--     type : LType
-- 

data (>:) : Context -> Typed -> Type where
  Z : gam &. x .: a >: x .: a
  S : Not (x = y) -> gam >: x .: a
   -> gam &. y .: b >: x .: a

-- infix 5 `∋` -- Checked / inherited 
-- infix 5 `∈` -- inferred / synthesized

record UpArrow where
  constructor ∈
  chkTerm : TermInf
  chkType : Inference.LType

record DownArrow where
  constructor ∋
  infType : Inference.LType
  infTerm : TermChk

mutual
  data (|-) : Context -> UpArrow -> Type where
    JudgeSet : gam >: x .: a
            -> gam |- (^x `∈` a)

    JudgeApp : {a : _} 
            -> gam |- (l `∈` a =>> b)
            -> gam |= (a `∋` m)
            -> gam |- (l |> m `∈` b)

    JudgeDown : gam |= (a `∋` m)
             -> gam |- (ToInf m a `∈` a)

  data (|=) : Context -> DownArrow -> Type where

    JudgeLam : {a, b : _} 
            -> gam &. x .: a |= b `∋` n
            -> gam |= ((a =>> b) `∋` (\\ x ==> n))

    JudgeZero : gam |= Nat' `∋` Zero

    JudgeSucc : gam |= Nat' `∋` m
             -> gam |= Nat' `∋` (Succ m)

    JudgePair : gam |= a `∋` x
             -> gam |= b `∋` y
             -> gam |= a `X` b `∋` Prod x y

    JudgeCase : gam |- l `∈` Nat'
             -> gam |= a `∋` m
             -> gam &. x .: Nat' |= a `∋` n
             -> gam |= a `∋` Case l m x n

    JudgeMu : gam &. x .: a |= a `∋` n
           -> gam |= a `∋` Mu x n

    JudgeUp : gam |- m `∈` a
           -> a = b
           -> gam |= b `∋` (ToChk m)

    JudgeProd : {a, b: _}
             ->  gam |- l `∈` a `X` b
             -> gam &. x .: a &. y .: b |= c `∋` n
             -> gam |= c `∋` CaseProd l x y n 

mult : TermInf
mult = (Mu "mult" ==> \\ "m" ==> \\ "n" ==>
          Case (^"m") 
               Zero
               "m" (ToChk (plus |> ToChk (^"n") 
                                |> ToChk (^"mult" |> ToChk (^"m") 
                                                  |> ToChk (^"n"))) ))
          `ToInf` (Nat' =>> Nat' =>> Nat')


natNotFun : Nat' = x =>> y -> Void
natNotFun Refl impossible

natNotProd : Nat' = x `X` y -> Void
natNotProd Refl impossible

funNotProd : x =>> y = z `X` w -> Void
funNotProd Refl impossible

prodInj : z `X` y = x `X` w -> y = w
prodInj Refl = Refl

prodInj' : y `X` z = w `X` x -> y = w
prodInj' Refl = Refl

implInj : z =>> y = Inference.(=>>) x w -> y = w
implInj Refl = Refl

implInj' : y =>> z = Inference.(=>>) w x -> y = w
implInj' Refl = Refl

--  QTT / linearity / resources

(?=) : (a, b : Inference.LType) -> Dec (a = b)
(?=) Nat' Nat' = Yes Refl
(?=) Nat' (x =>> y) = No natNotFun
(?=) Nat' (x `X` y) = No natNotProd
(?=) (x =>> y) Nat' = No (\x => (natNotFun (sym x)))
(?=) (x =>> y) (z =>> w) with (x ?= z)
  (?=) (x =>> y) (x =>> w) | Yes Refl with (y ?= w)
    (?=) (x =>> w) (x =>> w) | Yes Refl | Yes Refl = Yes Refl
    (?=) (x =>> y) (x =>> w) | Yes Refl | No contra = No (contra . implInj)
  (?=) (x =>> y) (z =>> w) | No contra = No (contra . implInj' )
(?=) (x =>> y) (z `X` w) = No funNotProd
(?=) (x `X` y) Nat' = No (\x => (natNotProd (sym x)))
(?=) (x `X` y) (z =>> w) = No (\x => funNotProd (sym x))
(?=) (x `X` y) (z `X` w) with (x ?= z)
  (?=) (x `X` y) (z `X` w) | Yes prf with (y ?= w)
    (?=) (z `X` w) (z `X` w) | Yes Refl | Yes Refl = Yes Refl
    (?=) (z `X` y) (z `X` w) | Yes Refl | No prf2 = No (prf2 . prodInj)
  (?=) (x `X` y) (z `X` w) | No contra = No (contra . prodInj')

domEq : a =>> b = Inference.(=>>) a' b' -> a = a'
domEq Refl = Refl

imgEq : a =>> b = Inference.(=>>) a' b' -> b = b'
imgEq Refl = Refl

uniqueType : gam >: x .: a -> gam >: x .: b -> a = b
uniqueType Z Z = Refl
uniqueType Z (S f y) = void (f Refl)
uniqueType (S f y) Z = void (f Refl)
uniqueType (S f y) (S g z) = uniqueType y z

uniqueInfer : gam |- m `∈` a -> gam |- m `∈` b -> a = b
uniqueInfer (JudgeSet x) (JudgeSet y) = uniqueType x y
uniqueInfer (JudgeApp x z) (JudgeApp y w) = imgEq (uniqueInfer x y)
uniqueInfer (JudgeDown x) (JudgeDown y) = Refl

extendIn : Not (x = y) 
        -> Not (a ** gam >: x .: a)
        -> Not (a ** gam &. y .: b >: x .: a)
extendIn f g (MkDPair b Z) = f Refl
extendIn f g (MkDPair fst (S f1 z)) = g (fst ** z)

lookupContra : (a : Inference.LType ** [] >: (x .: a)) -> Void
lookupContra (MkDPair fst snd) = ?ashuifd

lookup : (gam : Context) -> (x : Id) -> Dec (a ** gam >: x .: a)
lookup [] x = No lookupContra
lookup (y &. (name .: type)) x with (decEq name x)
  lookup (y &. (name .: type)) name | (Yes Refl) = Yes (type ** Z)
  lookup (y &. (name .: type)) x | (No contra) with (lookup y x)
    lookup (y &. (name .: type)) x | (No contra) | (Yes (a ** prf)) = 
      Yes (a ** S (\x => contra (sym x) ) prf)
    lookup (y &. (name .: type)) x | (No contra) | (No f) = 
      No (extendIn (\x => contra (sym x)) f)

notArg : gam |- l `∈` a =>> b
      -> Not (gam |= a `∋` m)
      -> Not (b' ** gam |- l |> m `∈` b')
notArg l notM (MkDPair b' (JudgeApp l' m')) = 
  let uniq = (uniqueInfer l l') in
  let d = domEq uniq in 
      notM (rewrite d in m')

0 notSwitch : gam |- m `∈` a
         -> Not (a = b)
         -> Not (gam |= b `∋` (ToChk m) )
notSwitch m notEq (JudgeUp m' prf) = notEq (rewrite uniqueInfer m m' in prf)

natNotLam : gam |= (Nat' `∋` (\\ x ==> y)) -> Void
natNotLam (JudgeLam z) impossible
natNotLam JudgeZero impossible
natNotLam (JudgeSucc z) impossible
natNotLam (JudgePair z w) impossible
natNotLam (JudgeCase z w v) impossible
natNotLam (JudgeMu z) impossible
natNotLam (JudgeUp z prf) impossible
natNotLam (JudgeProd z w) impossible

prodNotLam : gam |= ((z `X` w) `∋` (\\ x ==> y)) -> Void
prodNotLam (JudgeLam v) impossible
prodNotLam JudgeZero impossible
prodNotLam (JudgeSucc v) impossible
prodNotLam (JudgePair v s) impossible
prodNotLam (JudgeCase v s t) impossible
prodNotLam (JudgeMu v) impossible
prodNotLam (JudgeUp v prf) impossible
prodNotLam (JudgeProd v s) impossible

funNotNumber : gam |= ((x =>> y) `∋` Zero) -> Void
funNotNumber (JudgeLam z) impossible
funNotNumber JudgeZero impossible
funNotNumber (JudgeSucc z) impossible
funNotNumber (JudgePair z w) impossible
funNotNumber (JudgeCase z w v) impossible
funNotNumber (JudgeMu z) impossible
funNotNumber (JudgeUp z prf) impossible
funNotNumber (JudgeProd z w) impossible

prodNotNumber : gam |= ((x `X` y) `∋` Zero) -> Void
prodNotNumber (JudgeLam z) impossible
prodNotNumber JudgeZero impossible
prodNotNumber (JudgeSucc z) impossible
prodNotNumber (JudgePair z w) impossible
prodNotNumber (JudgeCase z w v) impossible
prodNotNumber (JudgeMu z) impossible
prodNotNumber (JudgeUp z prf) impossible
prodNotNumber (JudgeProd z w) impossible

funNotSuccesssor : gam |= ((a =>> b) `∋` Succ x) -> Void
funNotSuccesssor (JudgeLam y) impossible
funNotSuccesssor JudgeZero impossible
funNotSuccesssor (JudgeSucc y) impossible
funNotSuccesssor (JudgePair y z) impossible
funNotSuccesssor (JudgeCase y z w) impossible
funNotSuccesssor (JudgeMu y) impossible
funNotSuccesssor (JudgeUp y prf) impossible
funNotSuccesssor (JudgeProd y z) impossible

prodNotSuccessor : gam |= ((a `X` b) `∋` Succ x) -> Void
prodNotSuccessor (JudgeLam y) impossible
prodNotSuccessor JudgeZero impossible
prodNotSuccessor (JudgeSucc y) impossible
prodNotSuccessor (JudgePair y z) impossible
prodNotSuccessor (JudgeCase y z w) impossible
prodNotSuccessor (JudgeMu y) impossible
prodNotSuccessor (JudgeUp y prf) impossible
prodNotSuccessor (JudgeProd y z) impossible

numberNotProd : gam |= (Nat' `∋` Prod x y) -> Void
numberNotProd (JudgeLam z) impossible
numberNotProd JudgeZero impossible
numberNotProd (JudgeSucc z) impossible
numberNotProd (JudgePair z w) impossible
numberNotProd (JudgeCase z w v) impossible
numberNotProd (JudgeMu z) impossible
numberNotProd (JudgeUp z prf) impossible
numberNotProd (JudgeProd z w) impossible

lamNotProd : gam |= ((z =>> w) `∋` Prod x y) -> Void
lamNotProd (JudgeLam v) impossible
lamNotProd JudgeZero impossible
lamNotProd (JudgeSucc v) impossible
lamNotProd (JudgePair v s) impossible
lamNotProd (JudgeCase v s t) impossible
lamNotProd (JudgeMu v) impossible
lamNotProd (JudgeUp v prf) impossible
lamNotProd (JudgeProd v s) impossible

mutual 
  infer : (gam : Context) -> (m : TermInf)
       -> Dec (tp ** gam |- m `∈` tp)
  infer gam (^ x) with (lookup gam x)
    infer gam (^ x) | (Yes (a ** t)) = Yes (MkDPair a (JudgeSet t))
    infer gam (^ x) | (No contra) = No (\(a ** JudgeSet t) => contra (a ** t))

  infer gam (x |> y) with (infer gam x)
    infer gam (x |> y) | (No contra) = 
      No $ \(MkDPair type (JudgeApp t v)) => contra (MkDPair (_ =>> type) t)
    infer gam (x |> y) | (Yes (MkDPair Nat' snd)) = 
      No (\(type ** JudgeApp fun app) => natNotFun (uniqueInfer snd fun))

    infer gam (x |> y) | (Yes (MkDPair (a `X` b) snd)) = 
      No (\(type ** JudgeApp fun app) => funNotProd (uniqueInfer fun snd))

    infer gam (x |> y) | (Yes (MkDPair (a =>> b) snd)) with (check gam y a)
      infer gam (x |> y) | (Yes (MkDPair (a =>> b) snd)) | (Yes prf) = 
        Yes (b ** JudgeApp snd prf)
      infer gam (x |> y) | (Yes (MkDPair (a =>> b) snd)) | (No contra) = 
        No $ notArg snd contra
  infer gam (ToInf x y) with (check gam x y)
    infer gam (ToInf x y) | (Yes prf) = Yes (_ ** JudgeDown prf)
    infer gam (ToInf x y) | (No contra) = No $ \(a ** JudgeDown t) => contra t



  check : (gam : Context) -> (m : TermChk) -> (a : Inference.LType)
       -> Dec (gam |= a `∋` m)

  check gam ((\\) x y) Nat' = No $ natNotLam 
  check gam ((\\) x y) (z `X` w) = No prodNotLam
  check gam ((\\) arg body) (a =>> b) with (check (gam &. arg .: a) body b)
    check gam ((\\) x y) (z =>> w) | (Yes term) = Yes (JudgeLam term)
    check gam ((\\) x y) (z =>> w) | (No contra) = No (\(JudgeLam v) => contra v)

  check gam Zero Nat' = Yes JudgeZero
  check gam Zero (x =>> y) = No funNotNumber
  check gam Zero (x `X` y) = No prodNotNumber

  check gam (Succ x) (a =>> b) = No funNotSuccesssor
  check gam (Succ x) (a `X` b) = No prodNotSuccessor
  check gam (Succ x) Nat' with (check gam x Nat')
    check gam (Succ x) Nat' | (Yes prf) = Yes (JudgeSucc prf)
    check gam (Succ x) Nat' | (No contra) = No $ \(JudgeSucc nat) => contra nat

  check gam (Case scrutinee b1 pred b2) a with (infer gam scrutinee)
    check gam (Case scrutinee b1 pred b2) a | (No contra) = 
      No $ \(JudgeCase x y z) => contra (Nat' ** x) 
    check gam (Case scrutinee b1 pred b2) a | (Yes (MkDPair (x =>> y) sc)) = 
      No $ \(JudgeCase x y z) => natNotFun (uniqueInfer x sc)
    check gam (Case scrutinee b1 pred b2) a | (Yes (MkDPair (x `X` y) sc)) = 
      No $ \(JudgeCase x y z) => natNotProd (uniqueInfer x sc)
    check gam (Case scrutinee b1 pred b2) a | (Yes (MkDPair Nat' sc)) with (check gam b1 a)
      check gam (Case scrutinee b1 pred b2) a | (Yes (MkDPair Nat' sc)) | (Yes prf) with (check (gam &. pred .: Nat') b2 a)
        check gam (Case scrutinee b1 pred b2) a | (Yes (MkDPair Nat' sc)) | (Yes b1') | (Yes b2') = 
          Yes (JudgeCase sc b1' b2')
        check gam (Case scrutinee b1 pred b2) a | (Yes (MkDPair Nat' sc)) | (Yes prf) | (No contra) = 
          No $ \(JudgeCase x y z) => contra z
      check gam (Case scrutinee b1 pred b2) a | (Yes (MkDPair Nat' sc)) | (No contra) = 
        No $ \(JudgeCase x y z) => contra y

  check gam (Mu x body) a with (check (gam &. x .: a) body a)
    check gam (Mu x y) a | (Yes prf) = Yes (JudgeMu prf)
    check gam (Mu x y) a | (No contra) = No $ \case (JudgeMu z) => contra z

  check gam (Prod x y) Nat' = No numberNotProd
  check gam (Prod x y) (z =>> w) = No lamNotProd
  check gam (Prod x y) (z `X` w) with (check gam x z)
    check gam (Prod x y) (z `X` w) | (Yes prf) with (check gam y w)
      check gam (Prod x y) (z `X` w) | (Yes a') | (Yes b') = Yes $ JudgePair a' b'
      check gam (Prod x y) (z `X` w) | (Yes prf) | (No contra) = No $ \case (JudgePair v s) => contra s
    check gam (Prod x y) (z `X` w) | (No contra) = No $ \case (JudgePair v s) => contra v

  check gam (CaseProd pair y z w) a with (infer gam pair)
    check gam (CaseProd pair y z w) a | (No contra) = 
      No $ \case (JudgeProd x v) => contra (_ ** x) 
    check gam (CaseProd pair y z w) a | (Yes (MkDPair Nat' snd)) = 
      No $ \case (JudgeProd x v) => natNotProd (uniqueInfer snd x) 
    check gam (CaseProd pair y z w) a | (Yes (MkDPair (v =>> s) snd)) = 
      No $ \case (JudgeProd x v) => funNotProd (uniqueInfer snd x)
    check gam (CaseProd pair f s body) t | (Yes (MkDPair (k `X` l) snd)) with (check (gam &. f .: k &. s .: l) body t)
      check gam (CaseProd pair f s body) t | (Yes (MkDPair (k `X` l) snd)) | (Yes prf) = 
        Yes (JudgeProd snd prf)
      check gam (CaseProd pair f s body) t | (Yes (MkDPair (k `X` l) snd)) | (No contra) = 
        No $ \case (JudgeProd x y) => let prf = uniqueInfer snd x in (contra $ rewrite prodInj prf in 
                                                                               rewrite prodInj' prf in y)

  check gam (ToChk x) a with (infer gam x)
    check gam (ToChk x) a | (Yes (MkDPair type term)) with (a ?= type)
      check gam (ToChk x) a | (Yes (MkDPair type term)) | (Yes prf) = 
        Yes (rewrite prf in JudgeUp term Refl)
      check gam (ToChk x) a | (Yes (MkDPair type term)) | (No contra) = 
        No $ \(JudgeUp t Refl) => contra (uniqueInfer t term)
    check gam (ToChk x) a | (No contra) = 
      No $ \case (JudgeUp y Refl) => contra (a ** y)


fail1 : infer [] (ToInf (\\ "x" ==> ToChk (^ "y")) (Nat' =>> Nat')) = No ?
fail1 = Refl

failZero : infer [] (ToInf Zero (Nat' =>> Nat')) = No ?
failZero = Refl


forget : Inference.LType -> DB.LType
forget Nat' = DB.NatType
forget (x =>> y) = DB.(=>>) (forget x) (forget y)
forget (x `X` y) = ?ignore_products

forgetCtx : Context -> Ctxt
forgetCtx [] = []
forgetCtx (x &. (v .: t)) = (forgetCtx x) &. forget t

forgetJudge : gam >: c .: a -> Inference.forgetCtx gam >: forget a
forgetJudge Z = Z
forgetJudge (S f x) = S (forgetJudge x)

mutual 
  forgetInf : {t : _} -> gam |- v `∈` t -> forgetCtx gam |- forget t
  forgetInf (JudgeSet x) = DB.(^) (forgetJudge x)
  forgetInf (JudgeApp x y) = DB.(|>) (forgetInf x) (forgetChk y)
  forgetInf (JudgeDown x) = forgetChk x

  forgetChk : {t : _} -> gam |= t `∋` v -> forgetCtx gam |- forget t
  forgetChk (JudgeLam x) = DB.(\\) (forgetChk x)
  forgetChk JudgeZero = DB.Zero
  forgetChk (JudgeSucc x) = DB.Succ (forgetChk x)
  forgetChk (JudgePair x y) = ?ignore_Pair
  forgetChk (JudgeProd x y) = ?ingore_pair_match
  forgetChk (JudgeCase x y z) = DB.Case (forgetInf x) (forgetChk y) (forgetChk z)
  forgetChk (JudgeMu x) = DB.Mu (forgetChk x)
  forgetChk (JudgeUp x Refl) = forgetInf x

