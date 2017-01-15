
{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open import mso.Signatures
open import mso.Formulas
open import mso.ClosedTruth

open ListM

module mso.opentruth where

  ValueOpen : Subset → SigThing → Type
  ValueOpen A (i τ) = Maybe (IndividS A τ)  --could be a nil but only for a nullary const.
  ValueOpen A (r τs) = (IndividsS A τs → Type)
  --interpreting a signature; result type of get

  getOpen : ∀ {Σ oc} {st : SigThing}
      → st ∈ Σ
      → (A : Structure oc Σ)
      → ValueOpen (fst A) st
  getOpen i0 (A , (_ ,is a)) = Some a
  getOpen i0 (A , (_ ,rs rel)) = rel
  getOpen i0 (A , (_ ,none)) = None
  getOpen (iS i1) (A , SA ,is _) = getOpen i1 (A , SA)
  getOpen (iS i1) (A , SA ,rs _) = getOpen i1 (A , SA)
  getOpen (iS i1) (A , SA ,none) = getOpen i1 (A , SA)
  --lokup in signature

  getsOpen : ∀ {Σ oc} {τs : List Tp}
       → Terms Σ τs
       → (A : Structure oc Σ)
       → Maybe (IndividsS (fst A) τs)   --wanna make sure ALL constant are in domain
  getsOpen [] A = Some <>
  getsOpen (x ,t xs) A  with  (getsOpen xs A) | (getOpen x A)
  ... | Some vs | Some v = Some (vs , v)  --making sure all elements are interpreted
  ... | _ | _ = None  --if not its dead to us

  --lets you look up a bunch of terms

  _⊩o_ : ∀ {Σ} → Structure Open Σ → Formula Σ → Type
  (A , SA) ⊩o ∀i τ φ = ((a : IndividS A τ) → (A , (SA ,is a)) ⊩o φ) × ((A , (SA ,none)) ⊩o φ)
  (A , SA) ⊩o ∃i τ φ = Either (Σ \ (a : IndividS A τ) → (A , (SA ,is a)) ⊩o φ) ((A , (SA ,none)) ⊩o φ)
  (A , SA) ⊩o ∀p τ φ = (P : Unit × IndividS A τ → Type) → (A , (SA ,rs P)) ⊩o φ
  (A , SA) ⊩o ∃p τ φ = Σ \ (P : Unit × IndividS A τ → Type) → (A , (SA ,rs P)) ⊩o φ
  A ⊩o (φ1 ∧ φ2) = A ⊩o φ1 × A ⊩o φ2
  A ⊩o (φ1 ∨ φ2) = Either (A ⊩o φ1) (A ⊩o φ2)
  A ⊩o ⊤ = Unit
  A ⊩o ⊥ = Void
  A ⊩o (R rel xs) = Σ \ vs -> ((getsOpen xs A) == (Some vs)) × (getOpen rel A) (vs)
  A ⊩o (¬R rel xs) = Σ \ vs -> ((getsOpen xs A == (Some vs))) × (getOpen rel A) (vs) → Void

  _⊩o_false : ∀ {Σ} → Structure Open Σ → Formula Σ → Type
  A ⊩o φ false = A ⊩o (φ *)

  -- naive : ∀ {Σ φ} {A : Structure Closed Σ} → Either (A ⊩c φ) (A ⊩c φ false)
  -- naive = {!!}
