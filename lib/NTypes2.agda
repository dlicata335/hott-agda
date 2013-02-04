
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

  -- weakening

  -- in fact, it decrements, but often you want this lemma
  path-preserves-level : {n : TLevel} {A : Type} -> NType n A -> {x y : A} -> NType n (Path x y)
  path-preserves-level { -2 } {A} tA {x} {y} = ntype (Contractible-Path (use-level tA) x y)
  path-preserves-level { S n } {A} tA {x} {y} = ntype (λ p q → path-preserves-level (use-level tA x y))

  increment-level : {n : TLevel} {A : Type} -> (NType n A) → (NType (S n) A)
  increment-level {n}{A} tA = ntype (λ x y → path-preserves-level tA)

  raise-HProp : ∀ {n} {A : Type} → HProp A → NType (S n) A
  raise-HProp { -2 } hA = hA
  raise-HProp {S n} hA = increment-level (raise-HProp hA)


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


  -- would go elsewhere but need to be later on 

  Πlevel : ∀{A n}{B : A → Type} → ((x : A) -> NType n (B x)) → NType n ((x : A) → B x)
  Πlevel {A} { -2} a = ntype ((λ x → fst (use-level (a x))) , (λ f → λ≃ (λ x → snd (use-level (a x)) (f x))))
  Πlevel {A} {S n} a = ntype (λ f g → transport (NType n) (ua ΠPath.eqv) (Πlevel {A} {n} (λ x → use-level (a x) _ _)))

  ContractibleEquivUnit : ∀ {A} → Contractible A → Equiv A Unit
  ContractibleEquivUnit c = (improve (hequiv (λ _ → <>) (λ _ → fst c) (λ x → snd c x) (\ _ -> id)))

  Contractible≃Unit : ∀ {A} → Contractible A → A ≃ Unit
  Contractible≃Unit c = ua (ContractibleEquivUnit c)

  Contractible-Unit : Contractible Unit
  Contractible-Unit = (<> , \ _ -> id) 

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

  -- FIXME move elsewhere

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

  postulate
    Σlevel : ∀ {n} {A : Type} {B : A → Type}
           → NType n A
           → ((x : A) → NType n (B x))
           → NType n (Σ B)

  Path-Type-level : ∀ n → {A B : Type}
                        → NType (S n) B
                        → NType (S n) (Path A B)
  Path-Type-level n nB = transport (NType (S n)) (! univalence≃) (Σlevel (Πlevel (λ _ → nB)) (λ x → raise-HProp (IsEquiv-HProp _)))

  NTypes-level : ∀ n → NType (S n) (NTypes n)
  NTypes-level -2 = increment-level (ntype ((Unit , ntype Contractible-Unit) ,
                                            (λ y → coe (ΣSubsetPath NType-is-HProp) (! (Contractible≃Unit (use-level (snd y)))))))
  NTypes-level (S n) = ntype (λ An Bn → transport (NType (S n)) (ΣSubsetPath (λ _ → NType-is-HProp _))
                                        (Path-Type-level n (snd Bn)))
    






