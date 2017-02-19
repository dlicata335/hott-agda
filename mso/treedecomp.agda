
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
               →  ( ∀ {τs} → (xs : IndividsS (fst A) τs) (inBandx : allin τs (union B (singleton {τ = τ} x)) (nosubset τs (fst A) xs)) -- why is agda mad at this -->(xinxs : indIninds x (nosubset τs (fst A) xs))
               (rel : r τs ∈ Σ ) (relholds : get rel A xs) →  (allin τs (union X (singleton {τ = τ} x)) (nosubset τs (fst A) xs)))
                    → TreeDecomp X B → TreeDecomp (union X (singleton {τ = τ} x)) B
      Join : ∀  (X : Subset) (B1 B2 : Subset)
             → (containment1 : Sub X (intersection B1 B2))
             → (containment2 : Sub (intersection B1 B2) X)
             →  ( ∀ {τs} → (xs : IndividsS (fst A) τs) (inBsunion : allin τs (union B1 B2) (nosubset τs (fst A) xs)) (rel : r τs ∈ Σ )
                  (relholds : get rel A xs) → (Either (allin τs B1 (nosubset τs (fst A) xs)) (allin τs B2  (nosubset τs (fst A) xs))))
             → TreeDecomp X B1 → TreeDecomp X B2 → TreeDecomp X (union B1 B2)

--look at relation (leaves) cases for truth, raw treee, gametree
--ADD CONDITIONS

{- Thoughts for
1) Join condition: for all R (relations), v (list of individuals) where v is in B1 U B2, and R(v) holds, then v ∈ B1 or v ∈ B2.
 (for all τs???) (xs : IndividsS (fst A) τs) (pf : (union B1 B2) xs) (rel : r τs ∈ Σ ) (pf2 : get rel A xs) → (Either (xs ∈ B1) (xs ∈ B2))

2) Intro condition: for all R in signature , v in the stucture in B U {x} (containing x, I think) such that R(v) holds --> v ∈ X U x
(for all Σ and τs???)  (xs : Terms Σ τs) (pf : xs ∈ (union B singleton x)) (pf2 : get rel xs ... is true somehow?) xs ∈ (union X singleton x)
-}
