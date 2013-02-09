
{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths 
open import lib.NType
open import lib.Universe
open import lib.Truncations
open Truncation

module lib.NConnected where

  Connected : TLevel -> Type -> Type
  Connected n A = NType -2 (Trunc n A)


  out-of-contractible : ∀ {A C} (f : A -> C) (cA : NType -2 A) (a b : A)
                      → f a ≃ f b
  out-of-contractible f cA _ _ = ap f (HProp-unique (increment-level cA) _ _ )

  module ConnectedFib where 
   somewhere : (n : TLevel) {A : Type} {a : A}
             -> Connected (S n) A 
             -> (P : A → NTypes n)
             -> ((x : A) → fst (P x)) → (fst (P a))
   somewhere n {A}{a} c P f = f a

   everywhere : (n : TLevel) {A : Type} {a : A}
             -> Connected (S n) A 
             -> (P : A → NTypes n)
             -> (fst (P a)) → ((x : A) → fst (P x))
   everywhere n {A}{a} c P p = λ x → coe (! (ap fst (ap≃ lemma))) p 
     where lemma1 : (Trunc-rec (NTypes-level n) (λ x' → P x')) ≃ (\ _ -> P a)
           lemma1 = λ≃ (λ x → out-of-contractible (Trunc-rec (NTypes-level n) (λ x' → P x')) c x [ a ])
   
           lemma : P ≃ (\ _ -> P a) 
           lemma = P ≃〈 id 〉
                   Trunc-rec (NTypes-level n) (λ x' → P x') o [_] ≃〈 ap (λ f → f o ([_]{S n})) lemma1 〉
                   (\ _ -> P a) o ([_]{S n}) ≃〈 id 〉
                   ((λ _ → P a) ∎)
   postulate
     everywhereβ : (n : TLevel) {A : Type} {a : A}
               -> (cA : Connected (S n) A)
               -> (P : A → NTypes n)
               -> (at-base : fst (P a)) 
               -> everywhere n cA P at-base a ≃ at-base
{-
   eqv : (n : TLevel) {A : Type} {a : A}
        -> Connected (S n) A 
        -> (P : A → NTypes n)
        -> Equiv (fst (P a)) ((x : A) → fst (P x))
   eqv n c P = improve (hequiv (everywhere n c P) (somewhere n c P) {!!} {!!})

   path : (n : TLevel) {A : Type} {a : A}
        -> Connected (S n) A 
        -> (P : A → NTypes n)
        -> Path (fst (P a)) ((x : A) → fst (P x))
   path n c P = ua (eqv n c P)
-}

  module LeftBiased where
    wedge-rec : ∀ {A B C : Type} {a : A} {b : B}
              -> (fa : B -> C)
              -> (fb : A -> C)
              -> fa b ≃ fb a 
              -> A -> B -> C
    wedge-rec fa fb agree = λ _ b → fa b
  
    wedge-rec-βa : ∀ {A B C : Type} {a : A} {b : B}
              -> (fa : B -> C)
              -> (fb : A -> C)
              -> (agree : fa b ≃ fb a)
              -> (wedge-rec fa fb agree a ≃ fa)
    wedge-rec-βa fa fb agree = id
  
    wedge-rec-βb : ∀ n {A B C : Type} {a : A} {b : B}
                   (cA : Connected (S n) A)
                   (nC : NType (S n) C)
              -> (fa : B -> C)
              -> (fb : A -> C)
              -> (agree : fa b ≃ fb a)
              -> (\ a -> wedge-rec fa fb agree a b) ≃ fb
    wedge-rec-βb n {C = C}{a}{b} cA nC fa fb agree = 
      λ≃ (\ x -> ConnectedFib.everywhere n 
                 cA
                 (λ x → Path (fa b) (fb x) , use-level nC _ _)
                 agree
                 x)

    wedge-elim : ∀ n {A B : Type} (cA : Connected (S n) A) (C : A → B → NTypes n) {a : A} {b : B}
              -> (fa : (b' : B) -> fst (C a b'))
              -> (fb : (a' : A) -> fst (C a' b))
              -> fa b ≃ fb a 
              -> (a' : A) -> (b' : B) -> fst (C a' b')
    wedge-elim n cA C fa fb agree = λ a' b' → ConnectedFib.everywhere n cA (λ a'' → (C a'' b')) (fa b') a'

    wedge-elim-βa : ∀ n {A B : Type} (cA : Connected (S n) A) (C : A → B → NTypes n) {a : A} {b : B}
              -> (fa : (b' : B) -> fst (C a b'))
              -> (fb : (a' : A) -> fst (C a' b))
              -> (agree : fa b ≃ fb a)
              -> (wedge-elim n cA C fa fb agree a ≃ fa)
    wedge-elim-βa n cA C fa fb agree = λ≃ (\ b' -> ConnectedFib.everywhereβ n cA (λ a' → C a' b') (fa b'))

    wedge-elim-βb : ∀ n {A B : Type} (cA : Connected (S n) A) (C : A → B → NTypes n) {a : A} {b : B}
              -> (fa : (b' : B) -> fst (C a b'))
              -> (fb : (a' : A) -> fst (C a' b))
              -> (agree : fa b ≃ fb a)
              -> (\ a' -> wedge-elim n cA C fa fb agree a' b) ≃ fb
    wedge-elim-βb n cA C{a}{b} fa fb agree = 
      λ≃ (\ x -> ConnectedFib.everywhere n 
                 cA
                 (λ a' → Path (wedge-elim n cA C fa fb agree a' b) (fb a') , use-level (increment-level (snd (C a' b))) _ _)
                 (agree ∘ ConnectedFib.everywhereβ n cA (λ a' → C a' b) (fa b))
                 x)
  
