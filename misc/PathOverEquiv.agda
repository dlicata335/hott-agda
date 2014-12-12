{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude

module misc.PathOverEquiv where

  module Fact (A0 B0 A1 B1 : Type) (e0 : Equiv A0 B0) (e1 : Equiv A1 B1)  (e : Equiv (Σ \ a0 → Σ \ b0 → fst e0 a0 == b0)
                                                                                     (Σ \ a1 → Σ \ b1 → fst e1 a1 == b1)) where
     z : Equiv A0 A1
     z = improve (hequiv (λ x → fst (fst e (x , fst e0 x , id)))
                         (λ y → fst (IsEquiv.g (snd e) (y , fst e1 y , id)))
                         {!!} {!!})

