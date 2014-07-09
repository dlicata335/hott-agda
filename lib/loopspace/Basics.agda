
{-# OPTIONS --type-in-type --new-without-K #-}

open import lib.First
open import lib.Paths
open import lib.Prods
open import lib.Functions
open import lib.Int
open Int
open import lib.AdjointEquiv
open import lib.Truncations
open Truncation
open import lib.WrappedPath

module lib.loopspace.Basics where

  mutual
    Loop : (n : Positive) (A : Type) (base : A) → Type
    Loop One A b = Path b b
    Loop (S n) A b = Path {Loop n A b} (id^ n) (id^ n)

    id^ : ∀ n {A b} → Loop n A b
    id^ One = id
    id^ (S n) = id{_}{id^ n}

  mutual 
    ap^ : ∀ {A B} → (n : _) → (f : A → B) → {base : A} → Loop n A base → Loop n B (f base)
    ap^ One   f {base} l = ap f l 
    ap^ (S n) f {base} l = adjust (ap^-id n f) (ap (ap^ n f) l)

    ap^-id : ∀ {A B} → (n : _) → (f : A → B) → {base : A} →
             ap^ n f (id^ n) ≃ id^ n {_} {f base} 
    ap^-id One f = id
    ap^-id (S n) f = !-inv-with-middle-r (ap^-id n f) id


  -- alternative unfolding; could try redoing things with this instead
  Loop' : Positive -> (A : Type) -> A -> Type
  Loop' One A a = Path a a
  Loop' (S k) A a = Loop' k (Path a a) id

  ap^' : ∀ n {A B} {a : A} (f : A -> B) 
       -> Loop' n A a
       -> Loop' n B (f a)
  ap^' One f α = ap f α
  ap^' (S n) f α = ap^' n (ap f) α


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
    idOver (S n) B b = id{_}{idOver n B b}

  {-
  n = (S (S (S (S One))))

  test : {S : Type} {base : S} (loop : Loop n S base) → (B : S → Type) (b : B base) → Type 
  test {Sn} {base} loop X x = {!LoopOver n loop X x !}
  -}

  ap-Loop≃ : ∀ n {A B a b} (e : A ≃ B) (p : coe e a ≃ b) → Loop n A a ≃ Loop n B b
  ap-Loop≃ n e p = ap (λ (p : Σ (λ X → X)) → Loop n (fst p) (snd p)) (pair≃ e p)

  ap-Loop≃-id : ∀ n {A B a b} (e : A ≃ B) (p : coe e a ≃ b) → coe (ap-Loop≃ n e p) (id^ n) ≃ id^ n
  ap-Loop≃-id n id id = id

  ap-Loop-Trunc-tlevel≃ : ∀ n {A} {a : A} {k1 k2 : _} → k1 ≃ k2
                       → Loop n (Trunc k1 A) [ a ]
                       ≃ Loop n (Trunc k2 A) [ a ]
  ap-Loop-Trunc-tlevel≃ n id = id 

  ap-Loop-Trunc-tlevel≃-id : ∀ n {A} {a : A} {k1 k2 : _} (p : k1 ≃ k2)
                              → (coe (ap-Loop-Trunc-tlevel≃ n {a = a} p) (id^ n)) ≃ id^ n
  ap-Loop-Trunc-tlevel≃-id n id = id
  

  π : ∀ n A (a : A) → Type
  π n A a = τ₀ (Loop n A a)


