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

--gets rid of all extensions of signature that had nils in them
  postulate
    nonils : (Σ : Signature) → Signature
{-
--truncating structure?
  truncstruc : ∀ {oc A Σ} → (struc : StructureS oc A Σ) → Either (StructureS Closed A Σ) (StructureS Closed A (truncsig Σ))
  truncstruc [] = Inl []
  truncstruc (struc ,is x) = Inl (struc ,is x)
  truncstruc (struc ,none) = Inr {!struc!}
  truncstruc (struc ,rs x) = {!!}

--you can close a structureS
  closurehelp : ∀ {oc Σ A} → (ostrucS :  StructureS oc A Σ) →  (StructureS Closed A (nonils Σ))
  closurehelp  [] = {![]!}
  closurehelp (ostrucS ,is x) = {!!}
  closurehelp (ostrucS ,none) = {!!}
  closurehelp (ostrucS ,rs x) = {!!}
  closurehelp Σ
  closurehelp Σ (ostrucS ,is x) =  {!!} -- (closurehelp ostrucS) ,is x
  closurehelp Σ (ostrucS ,none) = {!!}
  closurehelp Σ (ostrucS ,rs xs) =  {!!} --(closurehelp ostrucS) ,rs xs -}

--you can close a structure
  {-closure : ∀ {oc Σ} → (ostruc :  Structure oc Σ) → Structure Closed (nonils Σ)
  closure ostruc = fst ostruc , {!closurehelp (snd ostruc)!}

  getOnClosed : -}

--open truth implies closed truth

  openToClosed : ∀ {Σ} → (struc : Structure Closed Σ) (φ : Formula Σ) → (otruth : struc ⊩o φ) → struc ⊩c φ
  openToClosed (SetA , StrucA) (∀i τ φ) (fst , snd) a = openToClosed (SetA , StrucA ,is a) φ (fst a)
  openToClosed (SetA , StrucA) (∃i τ φ) otruth = {!!}
  openToClosed (SetA , StrucA) (∀p τ φ) otruth P = {!!}
  openToClosed (SetA , StrucA) (∃p τ φ) (fst , snd) = fst , (openToClosed (SetA , StrucA ,rs fst) φ snd) --does this get smaller?
  openToClosed (SetA , StrucA) (φ1 ∧ φ2) (fst , snd) = (openToClosed (SetA , StrucA) φ1 fst) , (openToClosed (SetA , StrucA) φ2 snd)
  openToClosed (SetA , StrucA) (φ1 ∨ φ2) (Inl x) = Inl (openToClosed (SetA , StrucA) φ1 x)
  openToClosed (SetA , StrucA) (φ1 ∨ φ2) (Inr x) = Inr (openToClosed (SetA , StrucA) φ2 x)
  openToClosed (SetA , StrucA) ⊤ otruth = otruth
  openToClosed (SetA , StrucA) ⊥ otruth = otruth
  openToClosed (SetA , StrucA) (R x x₁) (fst , snd) = {!!}
  openToClosed (SetA , StrucA) (¬R x x₁) otruth x₂ = {!!}


-- A proves φ reduced -> A proves φ undecided
  redToUndec : ∀ { Σ} (A : Structure Open Σ) (φ : Formula Σ) → (game : A ⊩s φ )→ (X : fixed1 (fst A))
               → (red : isReduced A φ game X) → isUndecided A φ game
  redToUndec A (∀i τ φ) game X red = {!!} , {!!}
  redToUndec A (∃i τ φ) game X red = {!!}
  redToUndec A (∀p τ φ) game X red = {!!}
  redToUndec A (∃p τ φ) game X red = {!!}
  redToUndec A (φ ∧ φ₁) game X red = {!!}
  redToUndec A (φ ∨ φ₁) game X red = {!!}
  redToUndec A ⊤ game X red = {!!}
  redToUndec A ⊥ game X red = {!!}
  redToUndec A (R x x₁) game X red = {!!}
  redToUndec A (¬R x x₁) game X red = {!!}

--closure of A proves φ undec -> Either cl(A) proves φ true (open?) or A proves φ false (??)

--
