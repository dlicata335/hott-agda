
-- second file for stuff that needs to come later in the library

{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open Paths
open import lib.Prods
open import lib.Univalence
open import lib.Sums
open import lib.Functions
open import lib.Nat
open import lib.NTypes
open import lib.AdjointEquiv

module lib.Prods2 where

  module ΣPath where

    eqv : {A : Type} {B : A → Type} {p q : Σ B}
        → Equiv (Σ \ (α : Path (fst p) (fst q)) → Path (transport B α (snd p)) (snd q))
                (Path p q)
    eqv {B = B} {p = p} {q = q} = 
      improve (hequiv 
        (λ p → pair≃ (fst p) (snd p))
        (λ p → fst≃ p , snd≃ p)
        (λ p' → pair≃ (Σ≃β1 (fst p') (snd p')) 
                      (move-left-right (snd≃ (pair≃{B = B} (fst p') (snd p'))) (snd p')
                         (ap (λ v → transport B v (snd p)) (Σ≃β1 (fst p') (snd p')))
                         (Σ≃β2 {B = B} (fst p') (snd p')) ∘
                       transport-Path-pre' (λ v → transport B v (snd p))
                                           (Σ≃β1 (fst p') (snd p'))
                                           (snd≃ (pair≃{B = B} (fst p') (snd p'))))) 
        (λ p → Σ≃η p))

    path : {A : Type} {B : A → Type} {p q : Σ B}
        →   (Σ \ (α : Path (fst p) (fst q)) → Path (transport B α (snd p)) (snd q))
          ≃ (Path p q)
    path = ua eqv 

  Σ-with-Contractible : {A : Type} {B : A → Type}
                        → ( (x : A) → Contractible (B x))
                        -> A ≃ Σ B
  Σ-with-Contractible c = 
     ua (improve (hequiv (λ a → a , fst (c a))
                         fst
                         (λ _ → id)
                         (λ p → pair≃ id (HProp-unique (increment-level (ntype (c (fst p)))) _ _)))) 

  ΣSubsetPath : {A : Type} {B : A → Type} {p q : Σ B} 
                → ( (x : A) → HProp (B x))
                →   (Path (fst p) (fst q))
                  ≃ (Path p q)
  ΣSubsetPath {p = p}{q = q} hp = ΣPath.path ∘ Σ-with-Contractible (λ p' → use-level{n = -2} (use-level{n = S -2} (hp (fst q)) _ _))

  Σlevel : ∀ {n} {A : Type} {B : A → Type}
           → NType n A
           → ((x : A) → NType n (B x))
           → NType n (Σ B)
  Σlevel {n = -2} tA tB = transport (NType -2) (Σ-with-Contractible (λ x → use-level (tB x))) tA
  Σlevel {n = S n} tA tB = ntype (λ x y → transport (NType n) ΣPath.path (Σlevel {n = n} (use-level tA _ _) (λ x → use-level (tB (fst y)) _ _)))

  ContractibleEquivUnit : ∀ {A} → Contractible A → Equiv A Unit
  ContractibleEquivUnit c = (improve (hequiv (λ _ → <>) (λ _ → fst c) (λ x → snd c x) (\ _ -> id)))

  Contractible≃Unit : ∀ {A} → Contractible A → A ≃ Unit
  Contractible≃Unit c = ua (ContractibleEquivUnit c)

  Contractible-Unit : Contractible Unit
  Contractible-Unit = (<> , \ _ -> id) 

