
{-# OPTIONS --type-in-type --new-without-K #-}

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
    S^ : (n : Positive) → Type
    S^ n = Susp^ (n -1pn) S¹.S¹

    base^ : (n : Positive) → S^ n
    base^ n = point^ (n -1pn) S¹.base

    abstract
      S^-Connected : (n : Nat) → Connected (tl n) (S^ (n +1np))
      S^-Connected n = transport (λ x → NType -2 (Trunc (tl n) x)) (ap (λ x → Susp^ x S¹.S¹) (! (+1-1-cancel n)))
                         (Susp^-Connected0 n (ntype
                                                ([ S¹.base ] ,
                                                 Trunc-elim _ (λ _ → path-preserves-level Trunc-level)
                                                 (S¹.S¹-elim _ id (HSet-UIP (Trunc-level {tl 0}) _ _ _ _))))) 


