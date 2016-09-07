{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open import mso.Signatures

open ListM 

module mso.Formulas where

  data Terms (Σ : Signature) : List Tp → Type where
    []   : Terms Σ []
    _,t_ : ∀ {τ τs} → (i τ) ∈ Σ → Terms Σ τs → Terms Σ (τ :: τs)

  data Formula (Σ : Signature) : Type where
    ∀i ∃i : (τ : Tp) → Formula (Σ ,i τ) → Formula Σ
    ∀p ∃p : (τ : Tp) → Formula (Σ ,r (τ :: [])) → Formula Σ
    _∧_ _∨_ : Formula Σ → Formula Σ → Formula Σ
    ⊤ ⊥ : Formula Σ
    R ¬R : ∀ {τs} → (r τs) ∈ Σ → Terms Σ τs → Formula Σ -- e.g edge : (node,node → *) ∈ Σ , x : node, y:node ∈ Σ, then R edge (x,y) is a proposition

  postulate
    _* : ∀ {Σ} → Formula Σ → Formula Σ 
  --  φ * = {!!}
