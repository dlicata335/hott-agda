
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
  ... | _ | _ = None  --if not it's dead to us

  --lets you look up a bunch of terms

  -- open TRUTH: i.e. the structure is open, but the formula is really provable anyway
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

  -- raw game tree that is compatible with the formula
  _⊩s_ : ∀ {Σ} → Structure Open Σ → Formula Σ → Type 
  A ⊩s ∀i τ φ = Σ \ (bs : List (Branch A (i τ))) → (∀ {bi} → bi ∈ bs → extend A bi ⊩s φ)
  A ⊩s ∃i τ φ = Σ \ (bs : List (Branch A (i τ))) → (∀ {bi} → bi ∈ bs → extend A bi ⊩s φ)
  A ⊩s ∀p τ φ = Σ \ (bs : List (Branch A (r (τ :: [])))) → (∀ {bi} → bi ∈ bs → extend A bi ⊩s φ)
  A ⊩s ∃p τ φ = Σ \ (bs : List (Branch A (r (τ :: [])))) → (∀ {bi} → bi ∈ bs → extend A bi ⊩s φ)
  A ⊩s (φ1 ∧ φ2) = Either (A ⊩s φ1 × A ⊩s φ2) (Either (A ⊩s φ1) (A ⊩s φ2))
  A ⊩s (φ1 ∨ φ2) = Either (A ⊩s φ1 × A ⊩s φ2) (Either (A ⊩s φ1) (A ⊩s φ2))
  A ⊩s ⊤ = Unit
  A ⊩s ⊥ = Void
  A ⊩s (R rel xs) = Unit
  A ⊩s (¬R rel xs) = Unit

  isUndecided : ∀ {Σ} (A : Structure Open Σ) (φ : Formula Σ) → A ⊩s φ → Type
  isUndecided A (∀i τ φ) (bs , ts) = 
    -- (1) every extension in bs is reduced
    (∀ {bi} → (i : bi ∈ bs) → isUndecided (extend A bi) φ (ts i)) × 
    -- (2) every extension not in bs is true
    (∀ {bi} → (bi ∈ bs → Void) → (extend A bi) ⊩o φ)
  isUndecided A (∃i τ φ) (bs , ts) = 
    -- (1) every extension in bs is reduced
    (∀ {bi} → (i : bi ∈ bs) → isUndecided (extend A bi) φ (ts i)) × 
    -- (2) every extension not in bs is true
    (∀ {bi} → (bi ∈ bs → Void) → (extend A bi) ⊩o φ false)
  isUndecided A (∀p τ φ) (bs , ts) = 
    -- (1) every extension in bs is reduced
    (∀ {bi} → (i : bi ∈ bs) → isUndecided (extend A bi) φ (ts i)) × 
    -- (2) every extension not in bs is true
    (∀ {bi} → (bi ∈ bs → Void) → (extend A bi) ⊩o φ)
  isUndecided A (∃p τ φ) (bs , ts) = 
    -- (1) every extension in bs is reduced
    (∀ {bi} → (i : bi ∈ bs) → isUndecided (extend A bi) φ (ts i)) × 
    -- (2) every extension not in bs is true
    (∀ {bi} → (bi ∈ bs → Void) → (extend A bi) ⊩o φ false)
  isUndecided A (φ1 ∧ φ2) (Inl (t1 , t2)) = isUndecided A φ1 t1 × isUndecided A φ2 t2
  isUndecided A (φ1 ∧ φ2) (Inr (Inl t)) = isUndecided A φ1 t × A ⊩o φ2
  isUndecided A (φ1 ∧ φ2) (Inr (Inr t)) = A ⊩o φ1 × isUndecided A φ2 t 
  isUndecided A (φ1 ∨ φ2) (Inl (t1 , t2)) = isUndecided A φ1 t1 × isUndecided A φ2 t2
  isUndecided A (φ1 ∨ φ2) (Inr (Inl t)) = isUndecided A φ1 t × A ⊩o φ2 false
  isUndecided A (φ1 ∨ φ2) (Inr (Inr t)) = A ⊩o φ1 false × isUndecided A φ2 t 
  isUndecided A ⊤ <> = Void -- NOT Unit because we're not supposed to include winnable branches in a reduced game
  isUndecided A ⊥ ()
  isUndecided A (R U vs) <> = getsOpen vs A == None
  isUndecided A (¬R U vs) <> = getsOpen vs A == None

  -- naive : ∀ {Σ φ} {A : Structure Closed Σ} → Either (A ⊩c φ) (A ⊩c φ false)
  -- naive = {!!}
  
  
