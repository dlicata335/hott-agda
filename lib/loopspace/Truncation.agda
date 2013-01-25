
{-# OPTIONS --type-in-type #-}

open import lib.First
open import lib.Paths
open Paths
open import lib.Functions
open import lib.Nat
open import lib.Int
open Int
open import lib.AdjointEquiv
open import lib.Univalence
open import lib.Truncations
open Truncation
open import lib.WrappedPath

open import lib.loopspace.Basics
open import lib.loopspace.Groupoid

module lib.loopspace.Truncation where

  _+1 : Nat → Positive
  Z +1 = One
  (S n) +1 = S (n +1)

  _+'_ : Positive → Nat → Positive
  One +' k = k +1
  S n +' k = S (n +' k)

  tlp+1 : (k : Nat) → tlp (k +1) ≃ S (tl k)
  tlp+1 Z = id
  tlp+1 (S k) = ap S (tlp+1 k)

  postulate
    Trunc-Loop : ∀ n k {A} {a} → IsTrunc (tlp (n +' k)) A → IsTrunc (tl k) (Loop n A a)
  -- Trunc-Loop One k {A = A} p = use-trunc (transport (λ x → IsTrunc x A) (tlp+1 k) p) _ _
  -- Trunc-Loop (S n) k p = use-trunc (Trunc-Loop n (S k) {!!}) _ _

    HSet-Loop : ∀ n {A} {a} → IsTrunc (tlp n) A → HSet (Loop n A a)

    IsNTrunc-Loop : ∀ n {A a} -> IsTrunc (tlp n) A → IsTrunc (tlp n) (Loop n A a)

    IsTrunc-LoopOver : ∀ n k {A} {a} (α : Loop n A a) {B} {b} → ((x : A) → IsTrunc (S k) (B x)) → IsTrunc k (LoopOver n α B b)
  -- IsTrunc-LoopOver One k α p = use-trunc (p _) _ _
  -- IsTrunc-LoopOver (S n) k α p = {!use-trunc (p _) _ _!}
   
