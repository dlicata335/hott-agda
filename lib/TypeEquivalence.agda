{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open import lib.Prods
open Paths
open import lib.Univalence
open import lib.AdjointEquiv
open import lib.WrappedPath
open import lib.Functions
open import lib.NTypes

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

  move-adj≃ : ∀ {A} {a1 a2 a3 : A} 
             {w : a1 ≃ a2} (m : a1 ≃ a1)
             {w' : a3 ≃ a2} (m' : a3 ≃ a3)
           -> (adj w m ≃ adj w' m') ≃ (m ≃ adj (! w ∘ w') m')
  move-adj≃ {w = id} m1 {w' = id} m1' = ap (λ x → Path x (adj id m1')) (∘-unit-l m1 ∘ (adj-def _ _))

  rotate3≃ : ∀ {A} {x y z t : A} (b : y ≃ z) (f : x ≃ y) (c : x ≃ t) (g : t ≃ z) 
           → (b ∘ f ∘ (! c) ≃ g) ≃ (g ∘ c ∘ ! f ≃ b)
  rotate3≃ id id id g = flip≃

  rotate3≃-2 : ∀ {A} {w z : A} (a : z ≃ z) (b : w ≃ z) (c : w ≃ w)
             -> (a ∘ b ∘ ! c ≃ b) ≃ (a ≃ b ∘ c ∘ ! b)
  rotate3≃-2 a b c = flip≃ ∘ rotate3≃ a b c b 
  
  transport-by-equals≃ : ∀ {A : Type} {a1 a2 : A} (α : a1 ≃ a2) {B B' : A → Type} (b1 : B a1) (b2 : B a2)
                         -> (β : B ≃ B')
                         -> (transport B α b1 ≃ b2) ≃ (transport B' α (coe (ap≃ β) b1) ≃ coe (ap≃ β) b2)
  transport-by-equals≃ _ _ _ id  = id


