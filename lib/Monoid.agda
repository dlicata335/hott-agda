{-# OPTIONS --type-in-type #-}

open import lib.Paths

module lib.Monoid where

  record Monoid (A : Set) : Set where
    field
      _⊙_ : A -> A -> A
      `1  : A
      assoc : ∀ {x y z} -> (x ⊙ y) ⊙ z ≃ x ⊙ (y ⊙ z)
      unitl : ∀ {x} -> (x ⊙ `1) ≃ x
      unitr : ∀ {x} -> (`1 ⊙ x) ≃ x