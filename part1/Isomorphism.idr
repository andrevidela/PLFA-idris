module Isomorphism

import Equality
import Decidable.Order

funext : {f, g : a ->  b}
    -> ((x : a) -> f x ~~ g x)
      -----------------------
    -> f ~~ g

depfunext : {b : a -> Type} -> {f, g : (x : a) -> b x}
    -> ((x : a) -> f x ~~ g x)
      -----------------------
    -> f ~~ g

infix 4 ~=
  
public export
record (~=) (a : Type) (b : Type) where 
  constructor MkIso
  to : a -> b
  from : b -> a
  from_to : {a : Type} -> (x : a) -> from (to x) ~~ x
  to_from : (x : b) -> to (from x) ~~ x

public export
reflIso : a ~= a
reflIso = MkIso id id (\x => Refx) (\x => Refx)

public export
Preorder Type (~=) where
  reflexive a = reflIso
  transitive a b c ab bc = MkIso (bc.to . ab.to) (ab.from . bc.from) 
                                 (\x => begin (~~) $
                                      from ab (from bc (to bc (to ab x)))
                                     -< eq_cong (ab.from) (bc.from_to (ab.to x))>- 
                                      from ab (to ab x)  
                                     -< ab.from_to x >-
                                      End x ) 
                                 (\x => begin (~~) $
                                       (to bc (to ab (from ab (from bc x)))) 
                                      -< eq_cong (bc.to) (ab.to_from (bc.from x)) >-
                                       (bc.to (bc.from x))
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
  transitive a b c ab bc = MkEmb (bc.to . ab.to) (ab.from . bc.from) 
                                 (\x => begin (~~) $
                                      from ab (from bc (to bc (to ab x)))
                                     -< eq_cong (ab.from) (bc.from_to (ab.to x))>- 
                                      from ab (to ab x)  
                                     -< ab.from_to x >-
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
  transitive a b c ab bc = MkEquiv (bc.to . ab.to) (ab.from . bc.from)

