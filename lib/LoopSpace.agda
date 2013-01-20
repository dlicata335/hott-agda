{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open import lib.Int
open Paths
open Int
open import lib.AdjointEquiv
open import lib.Functions

module lib.LoopSpace where

  mutual
    Loop : (n : Positive) (A : Type) (base : A) → Type
    Loop One A b = Path b b
    Loop (S n) A b = Path {Loop n A b} (id^ n) (id^ n)

    id^ : ∀ n {A b} → Loop n A b
    id^ One = id
    id^ (S n) = id{_}{id^ n}

  collapse : ∀ {A} {a b : A} (α : Path a b) {β : Path a a} → (β ≃ id) → (α ∘ β ∘ ! α) ≃ id
  collapse α δ = (!-inv-r α ∘ ap (λ x → α ∘ x) (∘-unit-l (! α))) ∘ ap (λ x → α ∘ x ∘ ! α) δ

  mutual 
    ap^ : ∀ {A B} → (n : _) → (f : A → B) → {base : A} → Loop n A base → Loop n B (f base)
    ap^ One   f {base} l = ap f l 
    ap^ (S n) f {base} l = ap^-id n f ∘ ap (ap^ n f) l ∘ ! (ap^-id n f)

    ap^-id : ∀ {A B} → (n : _) → (f : A → B) → {base : A} →
             ap^ n f (id^ n) ≃ id^ n {_} {f base} 
    ap^-id One f = id
    ap^-id (S n) f = collapse (ap^-id n f) id

  _∘^_ : ∀ {n A a} → Loop n A a → Loop n A a → Loop n A a
  _∘^_ {One} p q = p ∘ q
  _∘^_ {S n} p q = p ∘ q

{-
  ap^-o : ∀ {A B C} → (n : _) → (g : B → C) (f : A → B)
        → {a : A} (α : Loop n A a)
        → ap^ n (g o f) α ≃ ap^ n g (ap^ n f α) 
  ap^-o One g f α = ap-o g f α
  ap^-o (S n) g f α = {!!}
-}

  mutual 
    LoopOver : (n : Positive) {A : Type} {a : A} (α : Loop n A a) 
             → (B : A -> Type) (b : B a) → Type
    LoopOver One α B b = transport B α b ≃ b
    LoopOver (S n) α B b = Path {LoopOver n (id^ n) B b}
                                (transport (λ x → LoopOver n x B b) α (idOver n B b)) 
                                (idOver n B b)

    idOver : (n : Positive) {A : Type} {a : A} (B : A → Type) (b : B a) 
           → LoopOver n (id^ n) B b
    idOver One B b = id
    idOver (S n) B b = id

  {-
  n = (S (S (S (S One))))

  test : {S : Type} {base : S} (loop : Loop n S base) → (B : S → Type) (b : B base) → Type 
  test {Sn} {base} loop X x = {!LoopOver n loop X x !}
  -}

{-
  Loop→ : ∀ n → ∀ {A} {B : A → Type} {f : _} → 
          Equiv ((x : A) → Loop n (B x) (f x))
                (Loop n ((x : A) -> B x) f)
  Loop→ n {A} {B} {m} = improve (hequiv (i n) (e n) {!!} {!!}) where

   mutual  
    i : ∀ n → ((x : A) → Loop n (B x) (m x)) → Loop n ((x : A) → B x) m
    i One   α = λ≃ α
    i (S n) α = i-id n ∘ ap (i n) (λ≃ α) ∘ ! (i-id n) 

    i-id : ∀ n → i n (\ x -> (id^ n)) ≃ (id^ n)
    i-id One = ! (Π≃η id)
    i-id (S n') = collapse (i-id n') (ap (ap (i n')) (! (Π≃η id)))

   mutual  
    e : ∀ n → Loop n ((x : A) → B x) m → (x : A) → Loop n (B x) (m x)
    e One   = λ α x → ap≃ α {x}
    e (S n) = λ α x → e-id n ∘ ap≃ (ap (e n) α) {x} ∘ ! (e-id n)

    e-id : ∀ n → ∀ {x} → e n (id^ n) x ≃ (id^ n)
    e-id One = id
    e-id (S n') = collapse (e-id n') id

   mutual
    β : ∀ n → (a : (x' : A) → Loop n (B x') (m x')) → (e n (i n a)) ≃ a
    β One a = λ≃ (λ x → Π≃β a)
    β (S n) a = {!!}

    {-
    β-id : ∀ n x → e-id n ∘ ap≃ (ap (e n) (i-id n)) {x} ≃ {!!}
    β-id = {!!}
    -}
-}