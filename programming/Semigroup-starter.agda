{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude

module programming.Semigroup-starter where

  Semigroup : Type → Type
  Semigroup A = Σ \ (_⊙_ : A → A → A) → 
                  (x y z : A) → x ⊙ (y ⊙ z) ≃ (x ⊙ y) ⊙ z

  transport-Semigroup-eqv : ∀ {A B} -> Equiv A B → Semigroup A → Semigroup B
  transport-Semigroup-eqv {A}{B}(f , isequiv g α β γ) (_⊙_ , assoc) = {!!}

  