
-- second file for stuff that needs to come later in the library

{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open Paths
open import lib.Prods
open import lib.Prods2
open import lib.Univalence
open import lib.Sums
open import lib.Functions
open import lib.Nat
open import lib.NTypes
open import lib.AdjointEquiv

module lib.NTypes2 where

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


  -- would go earlier but need to be later than where they would go

  Πlevel : ∀{A n}{B : A → Type} → ((x : A) -> NType n (B x)) → NType n ((x : A) → B x)
  Πlevel {A} { -2} a = ntype ((λ x → fst (use-level (a x))) , (λ f → λ≃ (λ x → snd (use-level (a x)) (f x))))
  Πlevel {A} {S n} a = ntype (λ f g → transport (NType n) (ua ΠPath.eqv) (Πlevel {A} {n} (λ x → use-level (a x) _ _)))

  use-level≃ : ∀ {n A} -> NType n A ≃ NType' n A
  use-level≃ = ua (improve (hequiv use-level ntype (\ {(ntype _)  -> id}) (\ x -> id)))


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


  -- level of the collection of all ntypes

  Path-Type-level : ∀ n → {A B : Type}
                        → NType (S n) B
                        → NType (S n) (Path A B)
  Path-Type-level n nB = transport (NType (S n)) (! univalence≃) (Σlevel (Πlevel (λ _ → nB)) (λ x → raise-HProp (IsEquiv-HProp _)))

  NTypes-level : ∀ n → NType (S n) (NTypes n)
  NTypes-level -2 = increment-level (ntype ((Unit , ntype Contractible-Unit) ,
                                            (λ y → coe (ΣSubsetPath NType-is-HProp) (! (Contractible≃Unit (use-level (snd y)))))))
  NTypes-level (S n) = ntype (λ An Bn → transport (NType (S n)) (ΣSubsetPath (λ _ → NType-is-HProp _))
                                        (Path-Type-level n (snd Bn)))
    






