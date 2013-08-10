{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude

module misc.Parametricity where

  -- example that doesn't follow from univalence
  -- want universe of sets and retractions?

  l : (Σ \ (A : Type) → A × (A → Bool)) → Bool
  l (_ , x , f) = f x

  r : Bool → (Σ \ (A : Type) → A × (A → Bool))
  r v = Unit , <> , (λ _ → v)

  rl : (x : _) → r (l x) == x
  rl (A , v , f) = {!!}