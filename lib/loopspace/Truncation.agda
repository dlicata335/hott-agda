
{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open Paths
open import lib.Functions
open import lib.Nat
open import lib.Int
open import lib.Prods
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

  Loop-preserves-pointed-≃ : ∀ n {A B a b} (e : A ≃ B) (p : transport (λ x → x) e a ≃ b) → Loop n A a ≃ Loop n B b
  Loop-preserves-pointed-≃ n e p = ap (λ (p : Σ (λ X → X)) → Loop n (fst p) (snd p)) (pair≃ e p)

  Path-Trunc : ∀ n {A} {x y : A} → Trunc n (Path x y) ≃ Path {(Trunc (S n) A)} [ x ] [ y ]
  Path-Trunc n = ua (improve (hequiv TruncPath.decode TruncPath.encode TruncPath.encode-decode' TruncPath.decode-encode))

  postulate
    Loop-Trunc : ∀ (n : Positive) (k : Nat) {A} {a} → Loop n (Trunc (tlp (n +pn k)) A) [ a ] ≃ Trunc (tl k) (Loop n A a)
    -- Loop-Trunc One k {A} {a} = ! (Path-Trunc (tl k)) ∘ Loop-preserves-pointed-≃ One (ap (λ u → Trunc u A) (tlp+1 k)) (transport-Trunc-tlevel _ _ (tlp+1 k) ∘ ! (ap≃ (transport-ap-assoc (λ u → Trunc u A) (tlp+1 k))))
    -- Loop-Trunc (S n) k {A} {a} = ! (Path-Trunc (tl k)) ∘ Loop-preserves-pointed-≃ One (Loop-Trunc n (S k) ∘ ap (λ t → Loop n (Trunc (tlp t) A) [ a ]) (! (+pn-rh-S n k))) {!!} ∘ id
  postulate
    Loop-Trunc-id : ∀ n k {A a} → coe (Loop-Trunc n k {A} {a}) (id^ n) ≃ [ id^ n ]
    -- Loop-Trunc-id One k = {!!}
    -- Loop-Trunc-id (S n) k = {!!}