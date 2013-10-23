{-# OPTIONS --type-in-type --without-K #-}

-- pushout of two maps f and g.
-- e.g. S2 = Pushout {S1}{Unit}{Unit} cst cst
--      has north, south, and a circle of points in between

open import lib.First
open import lib.NConnected
open import lib.Prods
open import lib.Functions
open import lib.Paths 
open import lib.NType
open import lib.Universe
open import lib.Truncations
open import lib.WEq
open Truncation

module lib.Pushout where

  module Pushout where

    module P where
      private
        data Pushout' {Z X Y : Type} (f : Z → X) (g : Z → Y) : Type where
          inl' : X → Pushout' f g 
          inr' : Y → Pushout' f g

      Pushout : {Z X Y : Type} (f : Z → X) (g : Z → Y) → Type 
      Pushout = Pushout'

      inl : ∀ {Z X Y}{f : Z → X}{g : Z → Y} → X → Pushout f g
      inl = inl'

      inr : ∀ {Z X Y}{f : Z → X}{g : Z → Y} → Y → Pushout f g
      inr = inr'

      postulate {- HoTT Axiom -}
        glue : ∀ {Z X Y} {f : Z → X}{g : Z → Y} (z : Z) → Path{Pushout f g} (inl (f z)) (inr (g z))

      Pushout-rec : {Z X Y C : Type} 
                    {f : Z → X} {g : Z → Y}
                    (b1 : X → C)
                    (b3 : Y → C)
                    (glue' : (z : Z) → (b1 (f z)) ≃ b3 (g z))
                  → Pushout f g → C
      Pushout-rec b1 _ _ (inl' x) = b1 x
      Pushout-rec _ b3 _ (inr' y) = b3 y

{-
      TODO: β rules
      postulate {- HoTT Axiom -}
        Pushout-rec/βcross : {A B C : Type}
                             {P : A → B → Type}
                             {C : Type}
                             (f : (a : A) → C)
                             (g : (b : B) → C)
                             (cross' : (a : A) → (b : B) → (p : P a b) →
                                      Path (f a) (g b)) →
                            (a : A) → (b : B) → (p : P a b) → 
                            Path (ap (Pushout-rec f g cross') (cross p))
                                 (cross' a b p)
-}

      Pushout-elim : {Z X Y : Type} 
                    {f : Z → X} {g : Z → Y}
                    (C : Pushout f g -> Type)
                    (b1 : (x : X) → C (inl x))
                    (b3 : (y : Y) → C (inr y))
                    (glue' : (z : Z) → transport C (glue z) (b1 (f z)) ≃ b3 (g z))
                  → (p : Pushout f g) → C p
      Pushout-elim _ b1 _ _ (inl' x) = b1 x
      Pushout-elim _ _ b3 _ (inr' y) = b3 y

    open P public

