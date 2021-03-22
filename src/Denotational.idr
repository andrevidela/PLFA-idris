module Denotational

import Untyped

-- functional extensionality, erased
0 funExt : {0 f, g : a -> b} -> ((x : a) -> f x === g x) -> f = g

infixr 7 |->
infixl 6 `U`

data Value : Type where
  Bot : Value
  (|->) : Value -> Value -> Value
  U : Value -> Value -> Value

infix 4 ||<
infix 4 .||<

data (||<) : Value -> Value -> Type where

  IncBot : {v : Value} -> Bot ||< v

  IncConjL : v ||< u -> w ||< u
          -> -------------------
             (v `U` w) ||< u

  IncConjR1 :    u ||< v
           -> -----------------
              u ||< (v `U` w)

  IncConjR2 :    u ||< w
           -> -----------------
              u ||< (v `U` w)

  IncTrans : u ||< v -> v ||< w
          -> ------------------
                  u ||< w

  IncFun : v' ||< v -> w ||< w'
        -> -----------------------
         (v |-> w) ||< (v' |-> w')

  IncDist :
           -----------------------------------------------
            v |-> (w `U` w') ||< (v |-> w) `U` (v |-> w')

IncRefl : (v : Value) -> v ||< v
IncRefl Bot = IncBot
IncRefl (x |-> y) = IncFun (IncRefl x) (IncRefl y)
IncRefl (x `U` y) = IncConjL (IncConjR1 (IncRefl x)) (IncConjR2 (IncRefl y))

UnionMonotonic : v ||< v' -> w ||< w'
            -> ----------------------------
                (v `U` w) ||< (v' `U` w')
UnionMonotonic x y = IncConjL (IncConjR1 x) (IncConjR2 y)

UnionDistr : {v, v', w, w' : Value}
       -> ------------------------------------------------------
          (v `U` v') |-> (w `U` w') ||< (v |-> w) `U` (v' |-> w')
UnionDistr = IncTrans IncDist
  (UnionMonotonic {v = (v `U` v') |-> w }
                  {v' = v |-> w}
                  {w = (v `U` v') |-> w'}
                  {w' = v' |-> w'}
                  (IncFun (IncConjR1 (IncRefl v)) (IncRefl w))
                          (IncFun (IncConjR2 (IncRefl v')) (IncRefl w')))

UnionInvL : u `U` v ||< w
         -> --------------
               u ||< w
UnionInvL (IncConjL x y) = x
UnionInvL (IncConjR1 x) = IncConjR1 (UnionInvL x)
UnionInvL (IncConjR2 x) = IncConjR2 (UnionInvL x)
UnionInvL (IncTrans x y) = IncTrans (UnionInvL x) y

UnionInvR : u `U` v ||< w
         -> --------------
               v ||< w
UnionInvR (IncConjL x y) = y
UnionInvR (IncConjR1 x) = IncConjR1 (UnionInvR x)
UnionInvR (IncConjR2 x) = IncConjR2 (UnionInvR x)
UnionInvR (IncTrans x y) = IncTrans (UnionInvR x) y

-- Environements

Env : Context -> Type
Env n = Elem n -> Value

Nil : Env Z
Nil FZ impossible
Nil (FS x) impossible

infixl 5 +.

append : Env g -> Value -> Env (S g)
append e f FZ = f
append e f (FS x) = e x

(+.) : Env g -> Value -> Env (S g)
(+.) = append

init : Env (S g) -> Env g
init f x = f (FS x)

last : Env (S g) -> Value
last f = f FZ

0 initLast : (e : Env (S g)) -> e === (init e +. last e)
initLast e = funExt $ \case FZ => Refl
                            (FS x) => Refl

(.||<) : {g : Nat} -> Env g -> Env g -> Type
c1 .||< c2 = (x : Elem g) -> c1 x ||< c2 x

BotEnv : Env g
BotEnv x = Bot

UEnv : Env g -> Env g -> Env g
UEnv c1 c2 x = c1 x `U` c2 x

IncEnvRefl : {c : Env g} -> c .||< c
IncEnvRefl x = IncRefl (c x)

IncEnvConjR1 : (c1 : Env g) -> (c2 : Env g) -> c1 .||< (c1 `UEnv` c2)
IncEnvConjR1 c1 c2 x = IncConjR1 (IncRefl (c1 x))


IncEnvConjR2 : (c1 : Env g) -> (c2 : Env g) -> c2 .||< (c1 `UEnv` c2)
IncEnvConjR2 c1 c2 x = IncConjR2 (IncRefl (c2 x))

infix 3 |-

infix 4 \/

record JPair (g : Context) where
  constructor (\/)
  ctxt : Jay g
  val : Value

data (|-) : Env g -> JPair g -> Type where
  Var : {0 g : Context} -> {0 c : Env g} -> {0 x : Elem g}
        -----------
        -> c |- (^x) \/ (c x)

  ImpElim : {c : Env g}
         -> c |- l \/ (v |-> w)
         -> c |- m \/ v
         ----------------------------------
         -> c |- (l |> m) \/ w

  ImpIntro : {c : Env g}
          -> c +. v |- n \/ w
          ------------------
          -> c |- (\\n) \/ (v |-> w)

  BotIntro : {c : Env g} -> c |- m \/ Bot

  IncIntro : {c : Env g}
          -> c |- m \/ v
          -> c |- m \/ w
          -----------------
          -> c |- m \/ (v `U` w)

  Sub : {c : Env g}
     -> c |- m \/ v
     -> w ||< v
     -------------
     -> c |- m \/ w


ID : Jay Z
ID = \\ ^0

denotId1 : {c : Env Z} -> c |- (ID \/ (Bot |-> Bot))
denotId1 = ImpIntro Var

denotId2 : {c : Env Z} -> c |- (ID \/ ((Bot |-> Bot) |-> (Bot |-> Bot)))
denotId2 = ImpIntro Var

denotId3 : [] |- ID \/ (Bot |-> Bot) `U` (Bot |-> Bot) |-> (Bot |-> Bot)
denotId3 = IncIntro denotId1 denotId2

idAppId : {u : Value} -> [] |- ID |> ID \/ (u |-> u)
idAppId = ImpElim (ImpIntro Var) (ImpIntro Var)

denotTwoC : {u, v, w : Value} ->
            [] |- Untyped.twoChurch \/ ((u |-> v `U` v |-> w) |-> u |-> w)

-- \x. (x x) -- apply x to itself
Delta : Jay Z
Delta = \\ ^FZ |> ^FZ

denotDelta : {u, v, w : Value} ->
             [] |- Delta \/ ((v |-> w `U` v) |-> w)
denotDelta =  ImpIntro impIntro
  where
    impIntro : (Nil +. ((v |-> w) `U` v)) |- ((^FZ |> ^FZ) \/ w)
    impIntro =
      let
          var1 : append [] ((v |-> w) `U` v) |- (^ FZ \/ ((v |-> w) `U` v))
            = Var {g = S Z} {c = the (Env 1) (append {g=0} Nil (v |-> w `U` v))} {x = FZ}
          incRe = IncRefl (v |-> w)
          incRe2 = IncConjR1 {u = v |-> w} {v= v |-> w} {w = v } incRe
          leSub = Sub {v=v |-> w `U` v} {m= ^FZ} {w=v |-> w} {c = Nil +. v |-> w `U` v}
                      var1 incRe2
          leSub2 = Sub {v=v |-> w `U` v} {m= ^FZ} {w=v} {c = Nil +. v |-> w `U` v}
                       var1
                       (IncConjR2 (IncRefl v))
       in ImpElim {l = ^FZ} {m = ^FZ} {v}
                   leSub
                   leSub2
