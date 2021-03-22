
module Connectives

import Isomorphism
import Equality
import Decidable.Order

%hide Num

infixr 2 ><
infixr 1 |+|

public export
data X : Type -> Type -> Type where
  (><) : a -> b -> a `X` b

public export
left : a `X` b -> a
left (a >< b) = a

public export
right : a `X` b -> b
right (a >< b) = b

public export
proj1 : a `X` b -> a
proj1 (a >< b) = a

public export
proj2 : a `X` b -> b
proj2 (a >< b) = b

public export
proj1_same : (x : a) -> proj1 (x >< x) ~~ x
proj1_same _ = Refx

public export
proj2_same : (x : a) -> proj2 (x >< x) ~~ x
proj2_same _ = Refx

public export
eta_prod : (w : X a b) ->  ((proj1 w) >< (proj2 w)) ~~ w
eta_prod (x >< y) = Refx

public export
impl_distrib_prod : {0 a, b, c : Type} -> (a -> (b `X` c)) ~= ((a -> b) `X` (a -> c))
impl_distrib_prod = MkIso (\x => proj1 . x >< proj2 . x)
                          (\(l >< r), a => l a >< r a) 
                          (\f => funext $ (\x => eta_prod (f x)))
                          (\(l >< r) => rewrite  apply_prf l in 
                                        rewrite apply_prf  r in Refx)

equiv_iso_prod : {a, b : Type} -> (a <=> b) ~= ((a -> b) `X` (b -> a))
equiv_iso_prod = MkIso (\eq => eq.to >< eq.from) 
                       (\(a >< b) => MkEquiv a b) 
                       (\(MkEquiv to from) => Refx)
                       (\(to >< from) => Refx)

public export
data Top : Type where
  TT : Top

top_identity : {a : Type} -> (Top `X` a) ~= a
top_identity = MkIso right (TT ><) (\(TT >< x) => Refx) (\x => Refx)

public export
data (|+|) : Type -> Type -> Type where
  Left : a -> a |+| b
  Right : b -> a |+| b

public export
elim_plus : (a -> c) -> (b -> c) -> a |+| b -> c
elim_plus l r (Left a) = l a
elim_plus l r (Right b) = r b

flip : a |+| b -> b |+| a
flip (Left x) = Right x
flip (Right x) = Left x

plus_comm_iso : a |+| b ~= b |+| a
plus_comm_iso = MkIso flip flip (\case 
                                   (Left a) => Refx
                                   (Right b) => Refx) 
                                (\case 
                                   (Left a) => Refx
                                   (Right b) => Refx) 

plus_assoc_iso : a |+| (b |+| c) ~= (a |+| b) |+| c
plus_assoc_iso = MkIso (\case
                         (Left a) => Left (Left a)
                         (Right (Left b)) => Left (Right b)
                         (Right (Right c)) => Right c)
                       (\case 
                         (Left (Left a)) => Left a
                         (Left (Right b)) => Right (Left b)
                         (Right c) => Right (Right c)) 
                       (\case
                         (Left a) => Refx 
                         (Right (Left b)) => Refx
                         (Right (Right c)) => Refx)
                       (\case
                         (Left (Left x)) => Refx
                         (Left (Right x)) => Refx
                         (Right x) => Refx)

export
data Bot : Type 

public export
elim_bot : Bot -> a
elim_bot x impossible

left_bot_id : Bot |+| a ~= a
left_bot_id = MkIso (\case 
                       (Left a) => elim_bot a
                       (Right b) => b) 
                    Right
                    (\case
                       (Left a) => elim_bot a
                       (Right b) => Refx) 
                    (\x => Refx)

plus_embed_prod : ((a `X` b) |+| c) ~< ((a |+| c) `X` (b |+| c))
plus_embed_prod = MkEmb (\case 
                           (Left (x >< y)) => Left x >< Left y
                           (Right x) => Right x >< Right x)
                        (\case
                          ((Left x) >< (Left y)) => Left (x >< y)
                          ((Left x) >< (Right y)) => Right y
                          ((Right x) >< (Left y)) => Right x
                          ((Right x) >< (Right y)) => Right x)
                        (\case
                          (Left (x >< y)) => Refx
                          (Right x) => Refx)

plus_weak_prod : (a |+| b) `X` c -> a |+| (b `X` c)
plus_weak_prod ((Left x) >< y) = Left x
plus_weak_prod ((Right x) >< y) = Right (x >< y)
