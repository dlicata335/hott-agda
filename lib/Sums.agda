{-# OPTIONS --type-in-type --without-K #-}

open import lib.First

module lib.Sums where

  data Void : Set where

  data Either (a : Set) (b : Set) : Set where
    Inl : a -> Either a b
    Inr : b -> Either a b

  module Sums where
    case : {A B : Type} (C : Either A B → Type) 
             → ((x : A) → C (Inl x))
             → ((y : B) → C (Inr y))
             → (e : Either A B) -> C e
    case C l r (Inl x) = l x
    case C l r (Inr y) = r y

    abort : {A : Type} → Void → A
    abort ()
    