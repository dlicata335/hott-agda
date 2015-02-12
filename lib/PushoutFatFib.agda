{-# OPTIONS --type-in-type --without-K #-}

-- pushout of a predicate P : X → Y → Type
-- includes a constructor for the "middle" space Z = Σ x,y.P(x,y).

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
open import lib.cubical.PathOver

module lib.PushoutFatFib where

  module FatPushoutFib where

    module P where
      private
        data Pushout' {X Y : Type} (P : X → Y → Type) : Type where
          inl' : X → Pushout' P 
          inm' : {x : X} {y : Y} → P x y → Pushout' P
          inr' : Y → Pushout' P

      Pushout : {X Y : Type} (P : X → Y → Type) → Type 
      Pushout = Pushout'

      inl : ∀ {X Y}{P : X → Y → Type} → X → Pushout P
      inl = inl'

      inr : ∀ {X Y}{P : X → Y → Type} → Y → Pushout P
      inr = inr'

      inm : ∀ {X Y}{P : X → Y → Type} → {x : X} {y : Y} → P x y → Pushout P
      inm = inm'

      postulate {- HoTT Axiom -}
        gluel : ∀ {X Y} {P : X → Y → Type} {x : X} {y : Y} → (p : P x y) → Path{Pushout P} (inm p) (inl x)
        gluer : ∀ {X Y} {P : X → Y → Type} {x : X} {y : Y} → (p : P x y) → Path{Pushout P} (inm p) (inr y)

      Pushout-rec : {X Y : Type} {P : X → Y → Type} {C : Type}
                    (b1 : X → C)
                    (b2 : (x : X) (y : Y) (p : P x y) → C)
                    (b3 : Y → C)
                    (gluel' : (x : X) (y : Y) (p : P x y) →  b2 x y p ≃ (b1 x))
                    (gluer' : (x : X) (y : Y) (p : P x y) → (b2 x y p) ≃ b3 y)
                  → Pushout P → C
      Pushout-rec b1 _ _ _ _ (inl' x) = b1 x
      Pushout-rec _ b2 _ _ _ (inm' {x = x} {y} p) = b2 x y p
      Pushout-rec _ _ b3 _ _ (inr' y) = b3 y

{-
      FIXME: TODO: give the beta rules for paths
-}

      Pushout-elim : {X Y : Type} {P : X → Y → Type} (C : Pushout P → Type)
                    (b1 : (x : X) → C (inl x))
                    (b2 : (x : X) (y : Y) (p : P x y) → C (inm p))
                    (b3 : (y : Y) → C (inr y))
                    (gluel' : (x : X) (y : Y) (p : P x y) → PathOver C (gluel p) (b2 x y p) (b1 x))
                    (gluer' : (x : X) (y : Y) (p : P x y) → PathOver C (gluer p) (b2 x y p) (b3 y))
                  → (z : Pushout P) → C z
      Pushout-elim _ b1 _ _ _ _ (inl' x) = b1 x
      Pushout-elim _ _ b2 _ _ _ (inm' {x = x}{y} p) = b2 x y p
      Pushout-elim _ _ _ b3 _ _ (inr' y) = b3 y

      postulate {- HoTT Axiom -}
        Pushout-elim/βgluel : {X Y : Type} {P : X → Y → Type} (C : Pushout P → Type)
                              (b1 : (x : X) → C (inl x))
                              (b2 : (x : X) (y : Y) (p : P x y) → C (inm p))
                              (b3 : (y : Y) → C (inr y))
                              (gluel' : (x : X) (y : Y) (p : P x y) → PathOver C (gluel p) (b2 x y p) (b1 x))
                              (gluer' : (x : X) (y : Y) (p : P x y) → PathOver C (gluer p) (b2 x y p) (b3 y))
                              (x : X) → (y : Y) → (p : P x y) → 
                              Path (apdo (Pushout-elim C b1 b2 b3 gluel' gluer') (gluel p))
                                   (gluel' x y p)

        Pushout-elim/βgluer : {X Y : Type} {P : X → Y → Type} (C : Pushout P → Type)
                              (b1 : (x : X) → C (inl x))
                              (b2 : (x : X) (y : Y) (p : P x y) → C (inm p))
                              (b3 : (y : Y) → C (inr y))
                              (gluel' : (x : X) (y : Y) (p : P x y) → PathOver C (gluel p) (b2 x y p) (b1 x))
                              (gluer' : (x : X) (y : Y) (p : P x y) → PathOver C (gluer p) (b2 x y p) (b3 y))
                              (x : X) → (y : Y) → (p : P x y) → 
                              Path (apdo (Pushout-elim C b1 b2 b3 gluel' gluer') (gluer p))
                                   (gluer' x y p)

    open P public
