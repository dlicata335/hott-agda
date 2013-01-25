
{-# OPTIONS --type-in-type #-}

open import lib.First
open import lib.Paths
open Paths
open import lib.Functions
open import lib.Int
open Int
open import lib.AdjointEquiv
open import lib.Univalence
open import lib.Truncations
open Truncation
open import lib.WrappedPath

module lib.loopspace.Basics where

  mutual
    Loop : (n : Positive) (A : Type) (base : A) → Type
    Loop One A b = Path b b
    Loop (S n) A b = Path {Loop n A b} (id^ n) (id^ n)

    id^ : ∀ n {A b} → Loop n A b
    id^ One = id
    id^ (S n) = id{_}{id^ n}

  mutual 
    ap^ : ∀ {A B} → (n : _) → (f : A → B) → {base : A} → Loop n A base → Loop n B (f base)
    ap^ One   f {base} l = ap f l 
    ap^ (S n) f {base} l = adjust (ap^-id n f) (ap (ap^ n f) l)

    ap^-id : ∀ {A B} → (n : _) → (f : A → B) → {base : A} →
             ap^ n f (id^ n) ≃ id^ n {_} {f base} 
    ap^-id One f = id
    ap^-id (S n) f = !-inv-with-middle-r (ap^-id n f) id

  mutual 
    LoopOver : (n : Positive) {A : Type} {a : A} (α : Loop n A a) 
             → (B : A -> Type) (b : B a) → Type
    LoopOver One α B b = transport B α b ≃ b
    LoopOver (S n) α B b = Path {LoopOver n (id^ n) B b}
                                (transport (λ x → LoopOver n x B b) α (idOver n B b)) 
                                (idOver n B b)

    idOver : (n : Positive) {A : Type} {a : A} (B : A → Type) (b : B a) 
           → LoopOver n (id^ n) B b
    idOver One B b = id
    idOver (S n) B b = id

  {-
  n = (S (S (S (S One))))

  test : {S : Type} {base : S} (loop : Loop n S base) → (B : S → Type) (b : B base) → Type 
  test {Sn} {base} loop X x = {!LoopOver n loop X x !}
  -}
