module Substitution

import Equality
import Untyped

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

up : Subst g (S g)
up x = ^ (FS x)

infixr 6 <:>

(<:>) : Jay d -> Subst g d -> Subst (S g) d
(<:>) m sig FZ = m
(<:>) m sig (FS x) = sig x

infixr 5 <.>

(<.>) : Subst g d -> Subst d s -> Subst g s
(<.>) sig tau = (subst tau) . sig




