{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open import mso.Signatures
open import mso.Formulas
open import mso.ClosedTruth
open import mso.opentruth
open import mso.treedecomp

open ListM
open Index

module mso.outerlemmas where

--tried to make a lemma where you can get whether a structureS is open/closed
  openOrClosedhelp : ∀ {oc A Σ} →  StructureS oc A Σ → OC
  openOrClosedhelp strucS = {!!}

  postulate
    nonils : (Σ : Signature) → Signature
{-
--truncating structure?
  truncstruc : ∀ {oc A Σ} → (struc : StructureS oc A Σ) → Either (StructureS Closed A Σ) (StructureS Closed A (truncsig Σ))
  truncstruc [] = Inl []
  truncstruc (struc ,is x) = Inl (struc ,is x)
  truncstruc (struc ,none) = Inr {!struc!}
  truncstruc (struc ,rs x) = {!!}
-}
--you can close a structureS
  closurehelp : ∀ {oc Σ A} → (ostrucS :  StructureS oc A Σ) →  (StructureS Closed A (nonils Σ))
  closurehelp  [] = {![]!}
  closurehelp (ostrucS ,is x) = {!!}
  closurehelp (ostrucS ,none) = {!!}
  closurehelp (ostrucS ,rs x) = {!!}
  {-closurehelp Σ
  closurehelp Σ (ostrucS ,is x) =  {!!} -- (closurehelp ostrucS) ,is x
  closurehelp Σ (ostrucS ,none) = {!!}
  closurehelp Σ (ostrucS ,rs xs) =  {!!} --(closurehelp ostrucS) ,rs xs -}

--you can close a structure
  closure : ∀ {oc Σ} → (ostruc :  Structure oc Σ) → Structure Closed (nonils Σ)
  closure ostruc = fst ostruc , {!closurehelp (snd ostruc)!}

--open truth implies closed truth

  openToClosed : ∀ {Σ} → (so : Structure Open Σ) (φ : Formula Σ) → (otruth : so ⊩o φ) → (closure so) ⊩c φ
  openToClosed (SetA , StrucA) (∀i τ φ) otruth a = {!!}
  openToClosed (SetA , StrucA) (∃i τ φ) otruth = {!!}
  openToClosed (SetA , StrucA) (∀p τ φ) otruth P = {!!}
  openToClosed (SetA , StrucA) (∃p τ φ) otruth = {!!}
  openToClosed (SetA , StrucA) (φ ∧ φ₁) otruth = {!!}
  openToClosed (SetA , StrucA) (φ ∨ φ₁) otruth = {!!}
  openToClosed (SetA , StrucA) ⊤ otruth = {!!}
  openToClosed (SetA , StrucA) ⊥ otruth = {!!}
  openToClosed (SetA , StrucA) (R x x₁) otruth = {!!}
  openToClosed (SetA , StrucA) (¬R x x₁) otruth x₂ = {!!}
