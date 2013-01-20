
{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open import lib.Suspension
open Suspension
open import lib.spaces.Circle
open import lib.Truncations
open import lib.Int

module lib.spaces.NSphere where


  module NSphereSusp where
    {-
    data S^ : (n : Int.Positive) → Type where
      1sphere : S¹ → S^ Int.One
      nsphere : ∀ {n} → Susp (S^ n) → S^ (Int.S n)
    -}
      
    -- might compute too far, but we'll see
    S^ : (n : Int.Positive) → Type
    S^ Int.One = S¹.S¹
    S^ (Int.S n) = Susp (S^ n)
  

