module Isomorphism

import Equality
import Decidable.Order

public export
apply_prf : (f : a -> b) -> (\x => f x) = f
apply_prf _ = Refl

export
apply_dep_prf : {0 b : u -> Type} -> (f : (a : u) -> b a) -> (\x => f x) = f
apply_dep_prf _ = Refl

export
funext : {f, g : a ->  b}
    -> ((x : a) -> f x ~~ g x)
      -----------------------
    -> f ~~ g

export
depfunext : {b : a -> Type} -> {f, g : (x : a) -> b x}
    -> ((x : a) -> f x ~~ g x)
    --------------------------
    -> f ~~ g

infix 0 ~=
  
public export
data (~=) : (a, b : Type) -> Type where 
  MkIso : (to      : a -> b)
       -> (from    : b -> a)
       -> (from_to : (x : a) -> from (to x) ~~ x)
       -> (to_from : (x : b) -> to (from x) ~~ x)
       -> a ~= b

to : a ~= b -> a -> b

from : a ~= b -> b -> a

from_to : (iso : a ~= b) -> (x : a) -> from iso (to iso x) ~~ x

to_from : (iso : a ~= b) -> (x : b) -> to iso (from iso x) ~~ x

public export
reflIso : a ~= a
reflIso = MkIso id id (\x => Refx) (\x => Refx)

public export
Preorder Type (~=) where
  reflexive a = reflIso
  transitive a b c ab bc = MkIso (to bc . to ab) (from ab . from bc) 
                                 (\x => begin (~~) $
                                      from ab (from bc (to bc (to ab x)))
                                     -< eq_cong (from ab) (from_to bc (to ab x))>- 
                                      from ab (to ab x)  
                                     -< from_to ab x >-
                                      End x ) 
                                 (\x => begin (~~) $
                                       (to bc (to ab (from ab (from bc x)))) 
                                      -< eq_cong (to bc) (to_from ab (from bc x)) >-
                                       (to bc (from bc x))
                                      -< bc.to_from x >-
                                       End x)

infix 4 ~<

namespace Embedding
  public export
  record (~<) (a : Type) (b : Type) where 
    constructor MkEmb
    to : a -> b
    from : b -> a
    from_to : (x : a) -> from (to x) ~~ x

public export
reflEmb : a ~< a
reflEmb = MkEmb id id (\x => Refx)

export
Preorder Type (~<) where
  reflexive a = reflEmb
  transitive a b c ab bc = MkEmb (to bc . to ab) (from ab . from bc) 
                                 (\x => begin (~~) $
                                      from ab (from bc (to bc (to ab x)))
                                     -< eq_cong (from ab) (from_to bc (to ab x))>- 
                                      from ab (to ab x)  
                                     -< from_to ab x >-
                                      End x ) 

export
Iso_to_Emb : a ~= b -> a ~< b
Iso_to_Emb (MkIso to from from_to to_from) = MkEmb to from from_to

infix 4 <=>


namespace Equiv
  public export
  record (<=>) (a : Type) (b : Type) where
    constructor MkEquiv
    to : a -> b
    from : b -> a

export
Preorder Type (<=>) where
  reflexive a = MkEquiv id id
  transitive a b c ab bc = MkEquiv (to bc . to ab) (from ab . from bc)
