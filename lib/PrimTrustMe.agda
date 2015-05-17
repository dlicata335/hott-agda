
open import Agda.Primitive

module lib.PrimTrustMe where

  data PId {l : Level} {A : Set l} (M : A) : A → Set l where
    Refl : PId M M

  {-# BUILTIN EQUALITY PId #-}
  {-# BUILTIN REFL Refl #-}

  primitive primTrustMe : {l : Level} {A : Set l} {x y : A} -> PId x y

  unsafe-cast : {l : Level} {A B : Set l} → A → B
  unsafe-cast {_}{A}{B} with primTrustMe {x = A} {y = B}
  unsafe-cast | Refl = \ x -> x

  funext/primtrustme : {l : Level} {A : Set l} {B : Set l} {f g : A → B}
                     → ((x : A) → PId (f x) (g x) )
                     → PId f g 
  funext/primtrustme h = primTrustMe

  transport/PId : {l : Level} {B : Set l} (E : B → Set l) 
                  {b1 b2 : B} → PId b1 b2 → (E b1 → E b2)
  transport/PId E Refl x = x

  ap/PId :  {l : Level} {A B : Set l} {M N : A}
            (f : A → B) → PId M N → PId (f M) (f N)
  ap/PId f Refl = Refl

