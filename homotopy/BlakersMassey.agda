{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open import lib.Pushout
open Truncation
open Int
open ConnectedProduct

module homotopy.BlakersMassey where

  module BMEquiv 
    (A B : Type)
    (P : A → B → Type)
    (a₀ : A) (b₀ : B) (p₀ : P a₀ b₀)
    (i j : TLevel)
    (iA : (a : A) → Connected i (Σ[ b ∶ A ] P a b₀))
    (jB : (b : B) → Connected j (Σ[ b ∶ B ] P a₀ b))
    where
