
module lib.PrimTrustMe where

  -- universe levels
  postulate
    Level : Set 
    lZ : Level
    lS : Level -> Level
    lmax : Level -> Level -> Level

  {-# BUILTIN LEVEL     Level #-}
  {-# BUILTIN LEVELZERO lZ  #-}
  {-# BUILTIN LEVELSUC  lS   #-}
  {-# BUILTIN LEVELMAX lmax #-}

  data PId {l : Level} {A : Set l} (M : A) : A → Set l where
    Refl : PId M M

  {-# BUILTIN EQUALITY PId #-}
  {-# BUILTIN REFL Refl #-}

  primitive primTrustMe : {l : Level} {A : Set l} {x y : A} -> PId x y

  unsafe-cast : {l : Level} {A B : Set l} → A → B
  unsafe-cast {_}{A}{B} with primTrustMe {x = A} {y = B}
  unsafe-cast | Refl = \ x -> x