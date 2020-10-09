
module Connectives

import Isomorphism
import Equality
import Decidable.Order

infixr 2 ><

data X : Type -> Type -> Type where
  (><) : a -> b -> a `X` b

left : a `X` b -> a
left (a >< b) = a

right : a `X` b -> b
right (a >< b) = b

equiv_iso_prod : (a <=> b) ~= ((a -> b) `X` (b -> a))
equiv_iso_prod = MkIso (\eq => eq.to >< eq.from) (\(a >< b) => MkEquiv a b) 
                       (\eq => begin (~~) $ MkEquiv (to eq) (from eq)
                                           -< ?frto2 >- End eq) (\x => ?toFr)
