
{-# OPTIONS --type-in-type #-}

open import lib.First
open import lib.Paths
open Paths
open import lib.Functions
open import lib.Int
open Int
open import lib.Prods
open import lib.AdjointEquiv
open import lib.Univalence
open import lib.Truncations
open Truncation
open import lib.WrappedPath

open import lib.loopspace.Basics
open import lib.loopspace.Groupoid
open import lib.loopspace.Truncation

module lib.loopspace.Types where

  LoopΠ : ∀ n → ∀ {A} {B : A → Type} {f : _} → 
          ((x : A) → Loop n (B x) (f x))
          ≃ (Loop n ((x : A) -> B x) f)
  LoopΠ n {A} {B} {m} = ua (improve (hequiv (i n) (e n) (β n) (η n))) where
    mutual  
     i : ∀ n → ((x : A) → Loop n (B x) (m x)) → Loop n ((x : A) → B x) m
     i One   α = λ≃ α
     i (S n) α = adjust (i-id n) (ap (i n) (λ≃ α))
  
     i-id : ∀ n → i n (\ x -> (id^ n)) ≃ (id^ n)
     i-id One = ! (Π≃η id)
     i-id (S n') = !-inv-with-middle-r (i-id n') (ap (ap (i n')) (! (Π≃η id)))
  
    mutual  
     e : ∀ n → Loop n ((x : A) → B x) m → (x : A) → Loop n (B x) (m x)
     e One   α x = ap≃ α {x}
     e (S n) α x = adjust (e-id n) (ap≃ (ap (e n) α) {x})
  
     e-id : ∀ n → ∀ {x} → e n (id^ n) x ≃ (id^ n)
     e-id One = id
     e-id (S n') = !-inv-with-middle-r (e-id n') id
  
    mutual
     β : ∀ n → (a : (x' : A) → Loop n (B x') (m x')) → (e n (i n a)) ≃ a
     β One a = λ≃ (λ x → Π≃β a)
     β (S n) a = λ≃ (λ x → adjust (e-id n) (ap (λ f → f x) (ap (e n) (adjust (i-id n) (ap (i n) (λ≃ a))))) ≃〈 ap (λ α → adjust (e-id n) (ap (λ f → f x) (ap (e n) α))) (! (adj-def _ _)) 〉
                           adjust (e-id n) (ap (λ f → f x) (ap (e n) (adj (i-id n) (ap (i n) (λ≃ a))))) ≃〈 ! (adj-def _ _) 〉
                           adj (e-id n) (ap (λ f → f x) (ap (e n) (adj (i-id n) (ap (i n) (λ≃ a))))) ≃〈 id 〉
                           adj _ (ap (λ f → f x) (ap (e n) (adj _ (ap (i n) (λ≃ a))))) ≃〈 ap (adj _) (! (ap-o (λ f → f x) (e n) ((adj _ (ap (i n) (λ≃ a)))))) 〉
                           adj _ (ap (λ f → e n f x) (adj _ (ap (i n) (λ≃ a)))) ≃〈 adj-bind (ap-adj (λ f → e n f x) _ _) 〉
                           adj _ (ap (λ f → e n f x) (ap (i n) (λ≃ a))) ≃〈 ap (adj _) (! (ap-o (λ f → e n f x) (i n) _)) 〉
                           adj _ (ap (λ f → e n (i n f) x) (λ≃ a)) ≃〈 adj-bind (ap-loop-by-equals {f = λ f → e n (i n f) x} {g = λ f → f x} (λ f → ap≃ (! (β n f))) _) 〉
                           adj _ (ap (λ f → f x) (λ≃ a)) ≃〈 ap (adj _) (Π≃β a) 〉
                           adj _ (a x) ≃〈 adj-eq-loop n _ _ _ _ id 〉
                           adj id (a x) ≃〈 ! (adj-id _) 〉
                           a x ∎)
  
    mutual
     η : ∀ n → (a : _) → (i n (e n a)) ≃ a
     η One a = ! (Π≃η a)
     η (S n) a = adjust (i-id n) (ap (i n) (λ≃ (λ x → adjust (e-id n) (ap (λ f → f x) (ap (e n) a))))) ≃〈 ap (λ α → adjust (i-id n) (ap (i n) (λ≃ α))) (λ≃ (λ α → ! (adj-def _ _))) 〉
                 adjust (i-id n) (ap (i n) (λ≃ (λ x → adj (e-id n) (ap (λ f → f x) (ap (e n) a))))) ≃〈 ! (adj-def _ _) 〉
                 adj (i-id n) (ap (i n) (λ≃ (λ x → adj (e-id n) (ap (λ f → f x) (ap (e n) a))))) ≃〈 id 〉
                 adj _ (ap (i n) (λ≃ (λ x → adj (e-id n {x}) (ap≃ (ap (e n) a) {x})))) ≃〈 ap (adj _) (ap (λ α → ap (i n) (λ≃ α)) (λ≃ (λ x → adj-ap≃ {x = x} (ap (e n) a) (λ x → e-id n {x})))) 〉
                 adj _ (ap (i n) (λ≃ (λ x → ap≃ (adj (λ≃ (λ x → e-id n {x})) (ap (e n) a)) {x}))) ≃〈 ap (adj _ o ap (i n)) (! (Π≃η _)) 〉
                 adj _ (ap (i n) (adj _ (ap (e n) a))) ≃〈 adj-bind (ap-adj (i n) _ _) 〉
                 adj _ (ap (i n) (ap (e n) a)) ≃〈 ap (adj _) (! (ap-o (i n) (e n) a)) 〉
                 adj _ (ap ((i n) o (e n)) a) ≃〈 adj-bind (ap-loop-by-equals {f = (i n) o (e n)} {g = λ x → x} (λ x → ! (η n x)) a) 〉
                 adj _ (ap (λ x → x) a) ≃〈 ap (adj _) (ap-id a) 〉
                 adj _ a ≃〈 adj-eq-loop n _ _ _ _ id 〉
                 adj id a ≃〈 ! (adj-id _) 〉
                 a ∎


  λl : ∀ n → ∀ {A} {B : A → Type} {f : _} → 
          ((x : A) → Loop n (B x) (f x))
       -> (Loop n ((x : A) -> B x) f)
  λl n h = coe (LoopΠ n) h

  apl : ∀ n → ∀ {A} {B : A → Type} {f : _} → 
          (Loop n ((x : A) -> B x) f)
       -> ((x : A) → Loop n (B x) (f x))
  apl n h = coe (! (LoopΠ n)) h


  abstract
    LoopΣ : ∀ n {A : Type} {B : A → Type} (a : A) (b : B a) → Σ (λ α → LoopOver n α B b) ≃ Loop n (Σ B) (a , b)
    LoopΣ n {A} {B} a b = ua (improve (hequiv (i n) {!!} {!!} {!!})) where
  
      mutual
        i : ∀ n → Σ (λ α → LoopOver n α B b) → Loop n (Σ B) (a , b)
        i One (α , β) = pair≃ α β
        i (S n) (α , β) = adjust (i-id n) (ap (i n) (pair≃ {A = Loop n A a} {B = λ α → LoopOver n α B b} α β))
  
        i-id : ∀ n → i n (id^ n , idOver n B b) ≃ id^ n
        i-id One = id
        i-id (S n) = !-inv-with-middle-r (i-id n) id
  
      mutual
        e : ∀ n → Loop n (Σ B) (a , b) → Σ (λ α → LoopOver n α B b)
        e One α = (fst≃ α , snd≃ α)
        e (S n) α = let β = adjust (e-id n) (ap (e n) α) in (fst≃ β , snd≃ β)
  
        e-id : ∀ n → e n (id^ n) ≃ (id^ n , idOver n B b)
        e-id One = id
        e-id (S n) = let β = (!-inv-with-middle-r (e-id n) id) in pair≃ (ap (ap fst) β) (apd (apd snd) β ∘ {!!})

  pairl : ∀ n {A : Type} {B : A → Type} {a : A} {b : B a} (α : Loop n A a) (β : LoopOver n α B b) → Loop n (Σ B) (a , b)
  pairl n α β = coe (LoopΣ n _ _) (α , β)

  fstl : ∀ n {A : Type} {B : A → Type} {a : A} {b : B a} → Loop n (Σ B) (a , b) → Loop n A a
  fstl n α = fst (coe (! (LoopΣ n _ _)) α)

  sndl : ∀ n {A : Type} {B : A → Type} {a : A} {b : B a} (α : Loop n (Σ B) (a , b)) → LoopOver n (fstl n α) B b
  sndl n α = snd (coe (! (LoopΣ n _ _)) α)

  LoopSType : ∀ n {A} -> ((a : A) -> Loop n A a) ≃ (Loop (S n) Type A)
  LoopSType n = (! (LoopPath n)) ∘
                ua (improve (hequiv (λ h → coe (ap (λ (B : Σ (λ A → A)) → Loop n (fst B) (snd B)) (! (pair≃ univalence≃ univalence≃-id))) (pairl n (λl n h) (fst (use-trunc (IsTrunc-LoopOver n -2 (λl n h) (λ f → IsEquiv-HProp f)))))
                                    (λ α y → (ap^ n (λ x → coe x y) α))
                                    {!!}
                                    {!!}))

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


