
{-# OPTIONS --type-in-type --without-K #-}

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

  Trunc-Loop : ∀ n k {A} {a} → IsTrunc (tlp (n +pn k)) A → IsTrunc (tl k) (Loop n A a)
  Trunc-Loop One k {A = A} p = use-trunc (transport (λ x → IsTrunc x A) (tlp+1 k) p) _ _
  Trunc-Loop (S n) k {A} p = use-trunc (Trunc-Loop n (S k) (transport (λ x → IsTrunc (tlp x) A) (! (+pn-rh-S n k)) p)) _ _

  IsTrunc-LoopOver : ∀ n k {A} {a} (α : Loop n A a) {B} {b} → ((x : A) → IsTrunc (S k) (B x)) → IsTrunc k (LoopOver n α B b)
  IsTrunc-LoopOver One k α p = use-trunc (p _) _ _
  IsTrunc-LoopOver (S n) k α{B}{b} p = use-trunc{S k} (IsTrunc-LoopOver n (S k) _ (λ x → increment-IsTrunc (p x))) _ _ 

  HSet-Loop : ∀ n {A} {a} → IsTrunc (tlp n) A → HSet (Loop n A a)
  HSet-Loop n {A} i = Trunc-Loop n Z (transport (\ n -> IsTrunc (tlp n) A) (! (+pn-rh-Z n)) i)
   
  IsKTrunc-Loop : ∀ n k {A a} -> IsTrunc k A → IsTrunc k (Loop n A a)
  IsKTrunc-Loop One k tA = path-preserves-IsTrunc tA
  IsKTrunc-Loop (S n) k tA = path-preserves-IsTrunc (IsKTrunc-Loop n k tA)

