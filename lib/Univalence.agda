{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths 
open import lib.AdjointEquiv
open import lib.Prods
open import lib.Functions
open import lib.NTypes
open Paths

module lib.Univalence where

  pathToEquiv : ∀ {A B} → Path A B → Equiv A B
  pathToEquiv {A} α = transport(\ x -> Equiv A x) α id-equiv


  -- eta-expanded version; makes the later definitions easier
  -- and is maybe better for the computational interp,
  -- at least if it's based on groupoids.
  -- is the conceptual order backwards here? should J come from these, rather than the other way around?
  coe-is-equiv : ∀ {A B} (p : Path A B) → IsEquiv (coe p)
  coe-is-equiv {A}{B} p = isequiv (coe (! p)) (λ _ → coe-inv-1 p) (λ _ → coe-inv-2 p) (triangle p) where
    triangle : ∀ {B} (p : Path A B) → (x : A) → Path (coe-inv-2 p) (ap (transport (λ x' → x') p) (coe-inv-1 p))
    triangle id = λ _ → id

  coe-equiv : ∀ {A B} (p : Path A B) → Equiv A B
  coe-equiv p = (coe p , coe-is-equiv p)

  pathToEquiv' : ∀ {A B} → Path A B → Equiv A B
  pathToEquiv' α = (coe α , coe-is-equiv α)

  -- really the same thing
  pathToEquiv-is-' : ∀ {A B} (α : Path A B) → pathToEquiv α ≃ pathToEquiv' α
  pathToEquiv-is-' id = id

  postulate {- HoTT Axiom -} 
    -- Dan version, using pathToEquiv'
    univalence : ∀ {A B} -> IsEquiv {Path A B} {Equiv A B} pathToEquiv'
  
  -- ua is the intro form; coe is the elim

  ua : ∀ {A B} -> Equiv A B -> Path A B
  ua = IsEquiv.g univalence

  univalence≃ : ∀ {A B} → Path A B ≃ Equiv A B
  univalence≃ = ua (pathToEquiv' , univalence)

  type≃β : {A B : Type} (e : Equiv A B) -> Path (coe (ua e)) (fst e)
  type≃β e = ap fst (IsEquiv.β univalence e)

  type≃β! : {A B : Type} (a : Equiv A B) -> coe (! (ua a)) ≃ IsEquiv.g (snd a)
  type≃β! a = ap (λ x → IsEquiv.g (snd x)) (IsEquiv.β univalence a)

  type≃η : ∀ {A B} (p : Path A B) → ua (coe-equiv p) ≃ p
  type≃η p = IsEquiv.α univalence p

  type≃-coh : ∀ {A B} (p : Path A B) -> ap coe (type≃η p) ≃ type≃β (coe-equiv p)
  type≃-coh p = ap (ap fst) (! (IsEquiv.γ univalence p)) ∘ ap-o fst pathToEquiv' (IsEquiv.α univalence p) 

  type≃-ext : ∀ {A B} (p q : Path A B) → ((x : A) -> coe p x ≃ coe q x) -> p ≃ q
  type≃-ext p q α = type≃η q ∘ ap ua (pair≃ (λ≃ α) (HProp-unique (IsEquiv-HProp (coe q)) _ _)) ∘ ! (type≃η p)

  -- true but don't need it right now
  -- transport-Equiv-post : ∀ {A B C} {b : Equiv B C} {a : Equiv A B} -> Path (transport (\ X -> Equiv A X) (ua b) a) (b ∘equiv a)
  
  !-ua : {A B : Type} (e : Equiv A B) → (! (ua e)) ≃ (ua (!equiv e))
  !-ua e = type≃-ext (! (ua e)) (ua (!equiv e)) (λ x → ap≃ (! (type≃β (!equiv e)) ∘ type≃β! e))

  univalence≃-id : ∀ {A} → coe (univalence≃ {A} {A}) id ≃ id-equiv
  univalence≃-id {A} = ap≃ (type≃β (pathToEquiv' , univalence)) {id}


