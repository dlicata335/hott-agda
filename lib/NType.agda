
{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open import lib.Nat
open import lib.Prods
open import lib.Sums
open import lib.Functions

module lib.NType where

  tl : Nat -> TLevel
  tl Z = (S (S -2))
  tl (S n) = (S (tl n))

  -- less than for tlevels
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


  -- alternate characterizations

  contract : {A : Type} -> (x : A) -> ((y : A) -> Path x y) -> Contractible A
  contract = _,_

  use-level≃ : ∀ {n A} -> NType n A ≃ NType' n A
  use-level≃ = ua (improve (hequiv use-level ntype (\ {(ntype _)  -> id}) (\ x -> id)))


  -- more weakening
  
  raise-HProp : ∀ {n} {A : Type} → HProp A → NType (S n) A
  raise-HProp { -2 } hA = hA
  raise-HProp {S n} hA = increment-level (raise-HProp hA)


  -- level of NType predicate

  Contractible-is-HProp : (A : Type) -> HProp (Contractible A)
  Contractible-is-HProp A = unique-HProp 
    (λ p q → pair≃ (snd p (fst q)) 
                   (λ≃ (λ x → transport (λ v → (y : A) → Path v y) (snd p (fst q)) (snd p) x ≃〈 ap≃ (transport-Π-post' Path (snd p (fst q)) (snd p))〉 
                              transport (λ v → Path v x) (snd p (fst q)) (snd p x) ≃〈 transport-Path-pre (snd p (fst q)) (snd p x)〉 
                              (snd p x) ∘ ! (snd p (fst q)) ≃〈 rearrange (snd p x) (snd p (fst q)) (snd q x) (STS p q x)〉 
                              snd q x ∎))) where
    STS : (p q : Contractible A) (x : A) -> snd q x ∘ snd p (fst q) ≃ (snd p x)
    STS p q x = 
      ((snd q x) ∘ (snd p (fst q))) ≃〈 ! (transport-Path-right (snd q x) (snd p (fst q))) 〉 
      (transport (λ z → Id (fst p) z) (snd q x) (snd p (fst q))) ≃〈 apd (snd p) (snd q x) 〉 
      (snd p x) ∎
    rearrange : {a b c : A} (α : a ≃ b) (β : a ≃ c) (γ : c ≃ b) → (γ ∘ β ≃ α) → (α ∘ ! β ≃ γ) 
    rearrange id id g = !

  NType-is-HProp   : {n : TLevel} (A : Type) -> HProp (NType n A)
  NType-is-HProp { -2 } A = transport (HProp) (! use-level≃) (Contractible-is-HProp A)
  NType-is-HProp {S n} A = transport HProp (! use-level≃) (Πlevel (λ _ → Πlevel (λ _ → NType-is-HProp {n} _)))

