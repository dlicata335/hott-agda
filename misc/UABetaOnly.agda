{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open import lib.cubical.Cubical

module misc.UABetaOnly where

  postulate
    ua' : ∀ {A B : Type} → Equiv A B → A == B
    uaβ' : ∀ {A B} (e : Equiv A B) → coe (ua e) == fst e

  full : ∀ {B X} → IsEquiv {B == X} {Equiv B X} (coe-equiv)
  full = retract-of-Id-is-Id coe-equiv ua (λ c → pair≃ (uaβ' c) (HProp-unique (IsEquiv-HProp _) _ _)) 

  
