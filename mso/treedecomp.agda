
{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open import mso.Signatures
open import mso.Formulas
open import mso.ClosedTruth

open ListM
open Index

module mso.treedecomp {Σ : Signature} {A : Structure Closed Σ} where

--did a weird thing for the xnew condition, where I said it was in the complement instead of not in the set.
--This seems stupid but I couldn't figure out how else to do it
  data TreeDecomp : Subset →  Subset → Type where
      Empty : TreeDecomp empty empty
      Delete : ∀ {τ} (X : Subset) (B : Subset) (x : Individ τ) →  TreeDecomp (union X (singleton {τ = τ} x)) B → TreeDecomp X B
      Intro : ∀ {τ} (X : Subset) (B : Subset) (x : Individ τ) → (xnew : (Sub (singleton {τ = τ} x) (complement B)))
                    → TreeDecomp X B → TreeDecomp (union X (singleton {τ = τ} x)) B
      Join : ∀  (X : Subset) (B1 B2 : Subset)
             → (containment1 : Sub X (intersection B1 B2))
             → (containment2 : Sub (intersection B1 B2) X)
             → TreeDecomp X B1 → TreeDecomp X B2 → TreeDecomp X (union B1 B2)

--look at relation (leaves) cases for truth, raw treee, gametree
--ADD CONDITIONS

{- Thoughts for
1) Join condition: for all R (relations), v (list of individuals) where v is in B1 U B2, and R(v) holds, then v ∈ B1 or v ∈ B2.
 (for all Σ and τs???) (xs : Terms Σ τs) (pf : xs ∈ (union B1 B2)) (pf2 : R rel xs ... is true somehow?) (Either (xs ∈ B1) (xs ∈ B2))

2) Intro condition: for all R in ?????? , v in B U {x} (containing x, I think) such that R(v) holds --> v ∈ X U x
(for all Σ and τs???)  (xs : Terms Σ τs) (pf : xs ∈ (union B singleton x)) (pf2 : R rel xs ... is true somehow?) xs ∈ (union X singleton x)
-}
