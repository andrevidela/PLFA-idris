module Lambda

import Decidable.Equality
import Connectives
import Equality

public export
Id : Type
Id = String

prefix 5 \\
infixl 7 |>
prefix 9 ^

infixr 0 ==> -- function application, like $
infixr 4 ~>  -- Single Reduction step
infixr 2 ->> -- "Reduces to"
infixr 7 =>> -- Type in Lambda calculus

public export
data Term : Type where
  (^)    : Id -> Term
  (\\)  : Id -> Term -> Term
  (|>) : Term -> Term -> Term
  Zero : Term
  Succ : Term -> Term
  Case : Term -> Term -> Id -> Term -> Term
  Mu   : Id -> Term -> Term

public export
(==>) : (a -> b) -> a -> b
(==>) f = f

two : Term
two = Succ (Succ Zero)

plus : Term
plus = Mu "+" ==> \\ "m" ==> \\ "n" ==>
         Case (^"m")
              (^"n")
              "m"
              (Succ (^"+" |> ^"m" |> (^"n")))

Two_church : Term
Two_church = \\"s" ==> \\"z" ==> ^"s" |> (^"s" |> ^"z")

plus_church : Term
plus_church = \\"m" ==> \\"n" ==> \\"s" ==> \\"z" ==>
               ^"m" |> ^"s" |> (^"n" |> ^"s" |> ^"z")

Succ_church : Term
Succ_church = \\"n" ==> Succ (^"n")

mult : Term
mult = Mu "*" ==> \\"m" ==> \\"n" ==>
          Case (^"m")
               Zero
               "m" (plus |> ^"m" |> (^"*" |> ^"m" |> ^"n"))

mult_church : Term
mult_church = \\"m" ==> \\"n" ==> \\"s" ==> \\"z" ==>
               ^"m" |> (plus_church |> ^"n") |> (^"n" |> ^"s" |> ^"z")

public export
data Value : Term -> Type where
  VLam : Value (\\x ==> n)
  VZero : Value Zero
  VSucc : Value v -> Value (Succ v)

public export
subst : Term -> (name : Id) -> (replacement : Term) -> Term
subst (^ x) y z with (decEq x y)
  subst (^ x) y z | (Yes prf) = z
  subst (^ x) y z | (No contra) = ^x
subst ((\\) x w) y v with (decEq x y)
  subst ((\\) x w) y v | (Yes prf) = \\x ==> w
  subst ((\\) x w) y v | (No contra) = \\x ==> (subst w y v)
subst (x |> w) y v = subst x y v |> subst w y v
subst Zero y v = Zero
subst (Succ x) y v = Succ (subst x y v)
subst (Case l m x n) y v with (decEq x y)
  subst (Case l m x n) y v | (Yes prf) =
    Case (subst l y v) (subst m y v) x n
  subst (Case l m x n) y v | (No contra) =
    Case (subst l y v) (subst m y v) x (subst n y v)
subst (Mu x w) y v with (decEq x y)
  subst (Mu x w) y v | (Yes prf) = Mu x ==> w
  subst (Mu x w) y v | (No contra) = Mu x ==> (subst w y v)

mutual
  substEq : Id -> Id -> (Term -> Term) -> Term -> Term -> Term
  substEq x y f w v with (decEq x y)
    substEq x y f w v | (Yes prf) = f w
    substEq x y f w v | (No contra) = f (subst' w y v)

  subst' : Term -> Id -> Term -> Term
  subst' (^ x) y z with (decEq x y)
    subst' (^ x) y z | (Yes prf) = z
    subst' (^ x) y z | (No contra) = ^x
  subst' (x |> w) y v = subst' x y v |> subst' w y v
  subst' Zero y z = Zero
  subst' (Succ x) y z = Succ (subst' x y z)
  subst' ((\\) x w) y v = substEq x y (\\x) w v
  subst' (Case l m x n) y v =
    substEq x y (Case (subst' l y v) (subst m y v) x) n v
  subst' (Mu x w) y v = substEq x y (Mu x) w v


-- Single reduction step
public export
data (~>) : Term -> Term -> Type where
  Xi1 : l ~> l' -> l |> m ~> l' |> m
  Xi2 : Value v -> m ~> m' -> v |> m ~> v |> m'
  BetaLam : Value v -> (\\arg ==> body) |> v ~> subst body arg v
  XiSucc : m ~> m' -> Succ m ~> Succ m'
  XiCase : l ~> l' -> Case l m x n ~> Case l' m x n
  BetaZero : Case Zero m x n ~> m
  BetaSucc : Value v -> Case (Succ v) m x n ~> subst n x v
  BetaMu : Mu x m ~> subst m x (Mu x m)


-- "Reduces to"
public export
data (->>) : Term -> Term -> Type where
  Step : m ~> n -> m ->> n
  ReduceRefl : (t : Term) -> t ->> t
  ReduceTrans : l ->> m -> m ->> n -> l ->> n

implementation Preorder Term (->>) where
  reflexive = ReduceRefl
  transitive a b c ab bc = ReduceTrans ab bc

confluence : (l ->> m, l ->> n) -> (p ** (m ->> p, n ->> p))
confluence ((Step x), y) = ?confluence_rhs_2
confluence ((ReduceRefl m), y) = ?confluence_rhs_3
confluence ((ReduceTrans x z), y) = ?confluence_rhs_4

diamond : (l ~> m, l ~> n) -> (p ** (m ->> p, n ->>p))
diamond (x, y) = confluence (Step x, Step y)

deterministic : {n, m : Term} -> l ~> m -> l ~> n -> m ~~ n

testTwo : Two_church |> Succ_church |> Zero ->> Succ (Succ Zero)
testTwo = begin (->>) $
          ((Two_church |> Succ_church) |> Zero)
        -< Step (Xi1 $ BetaLam VLam) >-
          (\\"z" ==> Succ_church |> (Succ_church |> ^"z")) |> Zero
        -< Step (BetaLam VZero) >-
          Succ_church |> (Succ_church |> Zero)
        -< Step (Xi2 VLam (BetaLam VZero)) >-
          Succ_church |> Succ Zero
        -< Step (BetaLam (VSucc VZero)) >-
          End (Succ (Succ Zero))

testTwoPlusTwo : Lambda.plus |> Lambda.two |> Lambda.two ->>
                 Succ (Succ (Succ (Succ Zero)))
testTwoPlusTwo = begin (->>) $
                 plus |> two |> two
              -< Step (Xi1 (Xi1 BetaMu)) >-
                 ((\\"m" ==> \\"n" ==>
                     Case (^"m")
                          (^"n")
                          "m" (Succ $ plus |> (^"m") |> (^"n")))
                  |> two |> two)
              -< Step (Xi1 $ BetaLam (VSucc (VSucc VZero))) >-
                 ((\\"n" ==>
                         Case two
                              (^"n")
                              "m" (Succ $ plus |> ^"m" |> ^"n")) |> two)
              -< Step (BetaLam (VSucc (VSucc VZero))) >-
                 Case two two "m" (Succ $ plus |> ^"m" |> two)
              -< Step (BetaSucc (VSucc VZero)) >-
                 Succ (plus |> Succ Zero |> two)
              -< Step (XiSucc (Xi1 (Xi1 BetaMu))) >-
                 Succ ((\\"m" ==> \\"n" ==>
                          Case (^"m")
                               (^"n")
                               "m" (Succ (plus |> ^"m" |> ^"n")))
                        |> Succ Zero |> two)
              -< Step (XiSucc (Xi1 (BetaLam (VSucc VZero)))) >-
                 Succ ((\\"n" ==>
                           Case (Succ Zero)
                                (^"n")
                                "m" (Succ (plus |> ^"m" |> ^"n")))
                        |> two)
              -< Step (XiSucc (BetaLam (VSucc (VSucc VZero)))) >-
                 Succ (Case (Succ Zero)
                            two
                            "m" (Succ (plus |> ^"m" |> two)))
              -< Step (XiSucc (BetaSucc VZero)) >-
                 Succ (Succ (plus |> Zero |> two))
              -< Step (XiSucc (XiSucc (Xi1 (Xi1 BetaMu)))) >-
                 Succ (Succ ((\\"m" ==> \\"n" ==>
                     Case (^"m")
                          (^"n")
                          "m" (Succ $ plus |> (^"m") |> (^"n"))) |> Zero |> two))
              -< Step (XiSucc (XiSucc (Xi1 (BetaLam VZero)))) >-
                 Succ (Succ ((\\"n" ==>
                     Case Zero
                          (^"n")
                          "m" (Succ $ plus |> (^"m") |> (^"n"))) |> two))
              -< Step (XiSucc (XiSucc (BetaLam (VSucc (VSucc VZero))))) >-
                 Succ (Succ (
                     Case Zero
                          two
                          "m" (Succ $ plus |> (^"m") |> two)))
              -< Step (XiSucc $ XiSucc BetaZero) >-
                 End (Succ (Succ (Succ (Succ Zero))))


-- Lambda Calculus Type
public export
data LType : Type where
  (=>>) : LType -> LType -> LType
  NatType : LType

infixl 6 .:
infixr 4 >:
infixl 5 &&
infixl 5 |-

-- Typed identifier
public export
record Typed where
  constructor (.:)
  name : Id
  type : LType

namespace Terms
  public export
  record TypedTerm where
    constructor (.:)
    name : Term
    type : LType

-- Context
public export
data Ctxt : Type where
  Nil : Ctxt
  (&&) : Ctxt -> Typed -> Ctxt

-- Judgement
public export
data (>:) : Ctxt -> Typed -> Type where
  Z : gam && xZ .: a >: xZ .: a
  S : (0 notEq : Not (xS = y)) -> gam >: xS .: a -> gam && y .: b >: xS .: a

LiftContra : {0 a, b : String} ->  a == b = False -> Not (a = b)
LiftContra prf Refl = ?LiftContra_rhs_1

public export
S' : {auto prf : (x == y) = False} -> gam >: x .: a -> gam && y .: b >: x .: a
S' prev = S (LiftContra prf) prev

-- Typing judgement
public export
data (|-) : Ctxt -> TypedTerm -> Type where

  Axiom : {x : Id} ->
          gam >: x .: a ->
          ---------------
          gam |- (^x) .: a

  Impl : {xImpl : Id} -> {0 a, b : LType} ->
         gam && xImpl .: a |- n .: b ->
         -----------------------------
         gam |- (\\xImpl ==> n) .: a =>> b

  Elim : {0 a, b : LType} -> {0 l, m : Term} ->
         gam |- l .: a =>> b ->
         gam |- (m .: a) ->
         --------------------
         gam |- (l |> m) .: b

  ZeroNat : gam |- Zero .: NatType

  SuccNat : gam |- m .: NatType ->
            -------------------------
            gam |- (Succ m) .: NatType

  CaseElim : {x : Id} ->
             gam |- l .: NatType ->
             gam |- m .: a ->
             gam && x .: NatType |- n .: a ->
             ------------------------------
             gam |- (Case l m x n) .: a

  MuRec : {x : Id} ->
          gam && x .: a |- m .: a ->
          ------------------------
          gam |- (Mu x ==> m) .: a


jTwo : {0 gam : Ctxt} -> gam |- Lambda.two .: NatType
jTwo = SuccNat (SuccNat ZeroNat)

jPlus : gam |- Lambda.plus .: NatType =>> NatType =>> NatType
jPlus  = MuRec $ Impl (Impl (CaseElim
                            (Axiom (S' Z))
                            (Axiom Z)
                            (SuccNat $ (Axiom (S' (S' (S' Z))) `Elim` Axiom Z) `Elim` Axiom (S' Z))))

jTwoPlusTwo : [] |- (Lambda.plus |> Lambda.two |> Lambda.two) .: NatType
jTwoPlusTwo = (jPlus `Elim` jTwo) `Elim` jTwo


jSuccChurch : [] |- Succ_church .: NatType =>> NatType
jSuccChurch = Impl (SuccNat (Axiom Z))

context_injective : gam >: x .: a -> gam >: x .: b -> a = b
context_injective Z Z = Refl
context_injective Z (S notEq y) = void (notEq Refl)
context_injective (S notEq y) Z = void (notEq Refl)
context_injective (S notEq y) (S prf z) = context_injective y z

-- jMul : [] |- Lambda.mult .: NatType =>> NatType =>> NatType
-- jMul = MuRec $ Impl $ Impl $ CaseElim (Axiom (S Refl Z)) ZeroNat
--              (Elim (Elim jPlus (Axiom Z)) (Axiom (S Refl Z)))
