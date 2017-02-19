

{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open import mso.Signatures
open import mso.Formulas

open ListM

module mso.ClosedTruth where

  Value : Subset → SigThing → Type
  Value A (i τ) = IndividS A τ
  Value A (r τs) = (IndividsS A τs → Type)

  get : ∀ {Σ} {st : SigThing}
      → st ∈ Σ
      → (A : Structure Closed Σ)
      → Value (fst A) st
  get i0 (A , (_ ,is a)) = a
  get i0 (A , (_ ,rs rel)) = rel
  get (iS i1) (A , SA ,is _) = get i1 (A , SA)
  get (iS i1) (A , SA ,rs _) = get i1 (A , SA)

  gets : ∀ {Σ} {τs : List Tp}
       → Terms Σ τs
       → (A : Structure Closed Σ)
       → IndividsS (fst A) τs
  gets [] A = <>
  gets (x ,t xs) A = (gets xs A) , (get x A)

  _⊩c_ : ∀ {Σ} → Structure Closed Σ → Formula Σ → Type
  (A , SA) ⊩c ∀i τ φ = (a : IndividS A τ) → (A , (SA ,is a)) ⊩c φ
  (A , SA) ⊩c ∃i τ φ = Σ \ (a : IndividS A τ) → (A , (SA ,is a)) ⊩c φ
  (A , SA) ⊩c ∀p τ φ = (P : Unit × IndividS A τ → Type) → (A , (SA ,rs P)) ⊩c φ
  (A , SA) ⊩c ∃p τ φ = Σ \ (P : Unit × IndividS A τ → Type) → (A , (SA ,rs P)) ⊩c φ
  A ⊩c (φ1 ∧ φ2) = A ⊩c φ1 × A ⊩c φ2
  A ⊩c (φ1 ∨ φ2) = Either (A ⊩c φ1) (A ⊩c φ2)
  A ⊩c ⊤ = Unit
  A ⊩c ⊥ = Void
  A ⊩c (R rel xs) = get rel A (gets xs A)
  A ⊩c (¬R rel xs) = (get rel A (gets xs A)) → Void

  _⊩c_false : ∀ {Σ} → Structure Closed Σ → Formula Σ → Type
  A ⊩c φ false = A ⊩c (φ *)

  -- naive : ∀ {Σ φ} {A : Structure Closed Σ} → Either (A ⊩c φ) (A ⊩c φ false)
  -- naive = {!!}
