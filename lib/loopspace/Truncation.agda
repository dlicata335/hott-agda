
{-# OPTIONS --type-in-type #-}

open import lib.First
open import lib.Paths
open Paths
open import lib.Functions
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

  postulate
    HSet-Loop : ∀ n {A} {a} → IsTrunc (tlp n) A → HSet (Loop n A a)

    IsTrunc-LoopOver : ∀ n k {A} {a} (α : Loop n A a) {B} {b} → ((x : A) → IsTrunc (S k) (B x)) → IsTrunc k (LoopOver n α B b)

    IsNTrunc-Loop : ∀ n {A a} -> IsTrunc (tlp n) A → IsTrunc (tlp n) (Loop n A a)
