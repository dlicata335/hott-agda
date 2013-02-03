
-- second file for stuff that needs to come later in the library

{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open Paths
open import lib.Prods
open import lib.Sums
open import lib.Functions
open import lib.Nat
open import lib.NTypes
open import lib.AdjointEquiv
open import lib.Univalence

module lib.NTypes2 where

  data _<tl_ : TLevel -> TLevel -> Type where
    ltS   : ∀ {m} → m <tl (S m)
    ltSR  : ∀ {n m} → n <tl m → n <tl (S m)

  subtract-left : ∀ {n m} -> (S n) <tl m → n <tl m
  subtract-left ltS = ltSR ltS
  subtract-left (ltSR lt) = ltSR (subtract-left lt)

  lt-unS : ∀ {n m} → (S n) <tl (S m) → n <tl m
  lt-unS ltS = ltS
  lt-unS (ltSR lt) = subtract-left lt

  lt-unS-right : ∀ {n m} → (S n) <tl (S m) → Either ((S n) <tl m) (m ≃ S n)
  lt-unS-right ltS = Inr id
  lt-unS-right (ltSR y) = Inl y

  postulate 
    Πlevel : ∀{A n}{B : A → Type} → ((x : A) -> NType n (B x)) → NType n ((x : A) → B x)

  postulate
    use-level≃ : ∀ {n A} -> NType n A ≃ NType' n A
    -- arrange modules so we can use univalence here 

  postulate
    Contractible-is-HProp : (A : Type) -> HProp (Contractible A)
    -- Contractible-is-HProp A = {!!} 
    -- λ c1 c2 → (pair≃ (fst (Contractible-Path c1 (fst c1) (fst c2))) {!snd (Contractible-Path c1 (fst c1) (fst c2)) !}) , 
    --           {!!}

  NType-is-HProp   : {n : TLevel} (A : Type) -> HProp (NType n A)
  NType-is-HProp { -2 } A = transport (HProp) (! use-level≃) (Contractible-is-HProp A)
  NType-is-HProp {S n} A = transport HProp (! use-level≃) (Πlevel (λ _ → Πlevel (λ _ → NType-is-HProp {n} _)))

  -- in fact, it decrements, but often you want this lemma
  path-preserves-level : {n : TLevel} {A : Type} -> NType n A -> {x y : A} -> NType n (Path x y)
  path-preserves-level { -2 } {A} tA {x} {y} = ntype (Contractible-Path (use-level tA) x y)
  path-preserves-level { S n } {A} tA {x} {y} = ntype (λ p q → path-preserves-level (use-level tA x y))

  increment-level : {n : TLevel} {A : Type} -> (NType n A) → (NType (S n) A)
  increment-level {n}{A} tA = ntype (λ x y → path-preserves-level tA)

  postulate
    NTypes-NType : ∀ n → NType (S n) (NTypes n)

  ContractibleEquivUnit : ∀ {A} → Contractible A → Equiv A Unit
  ContractibleEquivUnit c = (improve (hequiv (λ _ → <>) (λ _ → fst c) (λ x → snd c x) (\ _ -> id)))

  Contractible≃Unit : ∀ {A} → Contractible A → A ≃ Unit
  Contractible≃Unit c = ua (ContractibleEquivUnit c)

  Contractible-Unit : Contractible Unit
  Contractible-Unit = (<> , \ _ -> id) 



