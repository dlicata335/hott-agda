
{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open import lib.Suspension
open Suspension
open import lib.spaces.Circle
open import lib.Truncations
open Truncation
open import lib.Int
open Int
open import lib.Nat
open import lib.NConnected
open import lib.NType

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
  

    S^-Connected : (n : Nat) → Connected (tl n) (S^ (n +1np))
    S^-Connected Z = 
      ntype ([ S¹.base ] ,
             Trunc-elim _ (λ _ → path-preserves-level Trunc-level)
                       (S¹.S¹-elim _ id (HSet-UIP (Trunc-level {tl 0}) _ _ _ _)))
    S^-Connected (S n) = Susp-Connected _ (S^-Connected n)

    base^ : (n : Positive) → S^ n
    base^ One = S¹.base
    base^ (S n) = No