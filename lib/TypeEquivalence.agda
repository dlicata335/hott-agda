{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open Paths
open import lib.Univalence
open import lib.AdjointEquiv
open import lib.WrappedPath

module lib.TypeEquivalence where

  move-transport-right-!≃ : ∀ {A : Type} {M M' : A} (B : A → Type)
                           (α : M' ≃ M) {b : B M} {b' : B M'}
                        -> (transport B (! α) b ≃ b')
                         ≃ (b ≃ transport B α b')
  move-transport-right-!≃ B id = id

  cancel-left≃ : ∀ {A} {m1 m2 : A}
               (q : m1 ≃ m2) 
               (p : m1 ≃ m1)
               -> ((q ∘ p) ≃ q) ≃ (p ≃ id)
  cancel-left≃ id p = ap (λ x → Id x id) (∘-unit-l p)

  flip≃ : ∀ {A} {m1 m2 : A} 
              -> (m1 ≃ m2) ≃ (m2 ≃ m1)
  flip≃ = ua (improve (hequiv ! ! !-invol !-invol))

  move-!≃' : ∀ {A} {m1 m1' m2 m2' : A}
                 (q : m1 ≃ m2) 
                 (a1 : m1 ≃ m1')
                 (a2 : m2 ≃ m2')
                 (p : m2' ≃ m1')
               -> (! q ≃ (! a1 ∘ p ∘ a2)) ≃ (a2 ∘ q ∘ ! a1 ≃ ! p)
  move-!≃' id id a2 id = ap (λ x → Id x id) (∘-unit-l a2 ∘ ap (λ x → id ∘ x) (∘-unit-l a2)) ∘ flip≃

  move-!≃ : ∀ {A} {m1 m2 : A}
                 (q : m1 ≃ m2) 
                 (p : m2 ≃ m1)
               -> (! q ≃ p) ≃ (q ≃ ! p)
  move-!≃ id p = move-!≃' id id id p ∘ ap (λ x → Id id x) (! (∘-unit-l p))

  adj-middle-id : ∀ {A} {m1 m2 : A} (w : m1 ≃ m2) (m : m1 ≃ m1)
                ->  (m ≃ id) ≃ (adj w m ≃ id)
  adj-middle-id id m = ap (λ x → Id x id) (adj-id m)