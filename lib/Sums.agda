{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Nat

module lib.Sums where

  data Void : Set where

  data Either (a : Set) (b : Set) : Set where
    Inl : a -> Either a b
    Inr : b -> Either a b

  data Fin : Nat → Set where
    Z : ∀ {n} → Fin (S n) 
    S : ∀ {n} → Fin n → Fin (S n)

  module Sums where
    case : {A B : Type} (C : Either A B → Type) 
             → ((x : A) → C (Inl x))
             → ((y : B) → C (Inr y))
             → (e : Either A B) -> C e
    case C l r (Inl x) = l x
    case C l r (Inr y) = r y

    casest : {A B C : Type} 
             → (A → C)
             → (B → C)
             → (e : Either A B) -> C 
    casest l r (Inl x) = l x
    casest l r (Inr y) = r y

    abort : {A : Type} → Void → A
    abort ()
    
