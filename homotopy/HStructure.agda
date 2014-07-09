-- FIXME move to library


{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude

module homotopy.HStructure where

  record H-Structure (A : Type) (a0 : A) : Type where
   field 
     _⊙_      : A → A → A
     unitl    : ((a : A) → a0 ⊙ a ≃ a)
     unitr    : ((a : A) → a ⊙ a0 ≃ a)
     unitcoh  : unitl a0 ≃ unitr a0 
     isequivl : ((a : A) → IsEquiv (_⊙_ a))
