{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths 
open import lib.AdjointEquiv
open import lib.Prods
open Paths

module lib.Univalence where

  pathToEquiv : ∀ {A B} → Path A B → Equiv A B
  pathToEquiv {A} α = transport(\ x -> Equiv A x) α id-equiv
  
  postulate 
    univalence : ∀ {A B} -> IsEquiv {Path A B} {Equiv A B} pathToEquiv
  
  ua : ∀ {A B} -> Equiv A B -> Path A B
  ua = IsEquiv.g univalence

  -- FIXME prove from univalence
  postulate
    transport-Equiv-post : ∀ {A B C} {b : Equiv B C} {a : Equiv A B} -> Path (transport (\ X -> Equiv A X) (ua b) a) (b ∘equiv a)

    transport-ua : {A B : Type} (e : Equiv A B) -> Path (transport (\ A -> A) (ua e)) (fst e)

    !-ua : {A B : Type} (e : Equiv A B) → (! (ua e)) ≃ (ua (!equiv e))

    id-ua : {A : Type} → (ua id-equiv) ≃ id{_}{A}
    -- also needed this fact:
    id-ua-transport-ua : ∀ {A} -> (ap (transport (λ x → x)) id-ua) ≃ transport-ua (id-equiv{A})

  transport-ua-back : {A B : Type} {a : Equiv A B}
                    -> transport (\ x -> x) (! (ua a)) ≃ IsEquiv.g (snd a)
  transport-ua-back {a = a} = transport-ua _ ∘ ap (transport (λ X → X)) (!-ua a)