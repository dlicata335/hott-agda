
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

module lib.loopspace.Types where

  postulate
    LoopΠ : ∀ n → ∀ {A} {B : A → Type} {f : _} → 
            ((x : A) → Loop n (B x) (f x))
          ≃ (Loop n ((x : A) -> B x) f)

  λl : ∀ n → ∀ {A} {B : A → Type} {f : _} → 
          ((x : A) → Loop n (B x) (f x))
       -> (Loop n ((x : A) -> B x) f)
  λl n h = coe (LoopΠ n) h

  apl : ∀ n → ∀ {A} {B : A → Type} {f : _} → 
          (Loop n ((x : A) -> B x) f)
       -> ((x : A) → Loop n (B x) (f x))
  apl n h = coe (! (LoopΠ n)) h


{-
   LoopΠ n {A} {B} {m} = improve (hequiv (i n) (e n) {!!} {!!}) where
   mutual  
    i : ∀ n → ((x : A) → Loop n (B x) (m x)) → Loop n ((x : A) → B x) m
    i One   α = λ≃ α
    i (S n) α = i-id n ∘ ap (i n) (λ≃ α) ∘ ! (i-id n) 

    i-id : ∀ n → i n (\ x -> (id^ n)) ≃ (id^ n)
    i-id One = ! (Π≃η id)
    i-id (S n') = !-inv-with-middle-r (i-id n') (ap (ap (i n')) (! (Π≃η id)))

   mutual  
    e : ∀ n → Loop n ((x : A) → B x) m → (x : A) → Loop n (B x) (m x)
    e One   = λ α x → ap≃ α {x}
    e (S n) = λ α x → e-id n ∘ ap≃ (ap (e n) α) {x} ∘ ! (e-id n)

    e-id : ∀ n → ∀ {x} → e n (id^ n) x ≃ (id^ n)
    e-id One = id
    e-id (S n') = !-inv-with-middle-r (e-id n') id

   mutual
    β : ∀ n → (a : (x' : A) → Loop n (B x') (m x')) → (e n (i n a)) ≃ a
    β One a = λ≃ (λ x → Π≃β a)
    β (S n) a = {!!}

    {-
    β-id : ∀ n x → e-id n ∘ ap≃ (ap (e n) (i-id n)) {x} ≃ {!!}
    β-id = {!!}
    -}
-}

  postulate
    LoopSType : ∀ n {A} -> ((a : A) -> Loop n A a) ≃ (Loop (S n) Type A)
  {-
  LoopSType n = (! (LoopPath{n})) ∘ 
                ua (improve (hequiv (λ h → {! (coe (Loop→ n) h) !})
                                    (λ α y → (ap^ n (λ x → coe x y) α))
                                    {!!}
                                    {!!}))
  -}

  apt : ∀ n {A} -> Loop (S n) Type A → ((a : A) -> Loop n A a)
  apt n l a = coe (! (LoopSType n)) l a

  postulate
    apt-def : ∀ n {A} -> (l : Loop (S n) Type A) → (a : A) 
            → apt n l a ≃ ap^ n (\ x -> coe x a) (loopSN1 n l) 


  λt : ∀ n {A} -> ((a : A) -> Loop n A a) -> Loop (S n) Type A
  λt n l = coe (LoopSType n) l

  postulate
    apt-! : ∀ n {A} -> (α : Loop (S n) Type A) (a : _) →
              apt n (!^ (S n) α) a
            ≃ !^ n (apt n α a)


