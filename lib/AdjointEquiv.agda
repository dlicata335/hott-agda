{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths 
open import lib.Prods
open import lib.NTypes
open Paths
open import lib.WEq

module lib.AdjointEquiv where

 record IsEquiv {A B : Type} (f : A → B) : Type where
  constructor isequiv
  field
     g : B → A
     α : (x : A) → Path (g (f x)) x
     β : (y : B) → Path (f (g y)) y
     γ : (x : A) →  Path (β (f x)) (ap f (α x)) -- coherence condition necessary for higher spaces
     -- also satifies:
     -- (y : B) →  Path (α (g y)) (ap g (β y));
     -- this is just γ with f<→g and α<→β, so we'll prove this in
     -- the process of defining !-equiv below

 Equiv : Type -> Type -> Type
 Equiv A B = Σ (IsEquiv{A}{B})

 equiv : {A B : Type}
     (f : A → B)
     (g : B → A)
     (α : (x : A) → Path (g (f x)) x)
     (β : (y : B) → Path (f (g y)) y)
     (γ : (x : A) →  Path (β (f x)) (ap f (α x)))
   → Equiv A B
 equiv f g α β γ = f , isequiv g α β γ

 record IsHEquiv {A B : Type} (f : A → B) : Type where
   constructor ishequiv
   field
     g : B → A
     α : (x : A) → Path (g (f x)) x
     β : (y : B) → Path (f (g y)) y

 HEquiv : Type → Type → Type
 HEquiv A B = Σ (IsHEquiv{A}{B})

 hequiv : {A B : Type}
     (f : A → B)
     (g : B → A)
     (α : (x : A) → Path (g (f x)) x)
     (β : (y : B) → Path (f (g y)) y)
     → HEquiv A B
 hequiv f g α β = f , ishequiv g α β

 inverses-natural : ∀ {A B} (f : A → B) (g : B → A) (η : (x : A) → Path (g (f x)) x)
                      {x : A} 
                   → Path (η (g (f x))) (ap (g o f) (η x))
 inverses-natural f g η {x} = 
   (∘-unit-l _ ∘ ap (λ y → y ∘ ap (λ x' → g (f x')) (η x)) (!-inv-l (η x))) ∘ 
   ap (λ a → (! a ∘ η x) ∘ ap (g o f) (η x)) (ap-id (η x)) ∘
   move-right-right-! (η (g (f x))) (ap (λ x' → g (f x')) (η x)) _
     (move-right (ap (λ x' → x') (η x)) (η (g (f x)) ∘ ! (ap (λ x' → g (f x')) (η x))) _
       (apd η (η x) ∘ ! (transport-Path (g o f) (λ x' → x') (η x) (η (g (f x)))))) 

 improve : {A B : Type} → HEquiv A B → Equiv A B
 improve (f , ishequiv g η ξ) = 
   equiv f g 
         η 
         (λ x → ξ x ∘ ap f (η (g x)) ∘ ap (f o g) (! (ξ x)))
         coh where
   abstract -- we might someday need to know this, but for now it's slowing things down too much
            -- at call sites to normalize it
     coh : (x : _) -> ξ (f x) ∘ ap f (η (g (f x))) ∘ ap (f o g) (! (ξ (f x))) ≃ ap f (η x)
     coh =
         (λ x → ξ (f x) ∘ ap f (η (g (f x))) ∘ ap (f o g) (! (ξ (f x)))                            ≃〈 ap (λ a → ξ (f x) ∘ ap f a ∘ ap (f o g) (! (ξ (f x)))) (inverses-natural f g η) 〉 
                ξ (f x) ∘ ap f (ap (g o f) (η x)) ∘ ap (f o g) (! (ξ (f x)))                      ≃〈 ap (λ a → ξ (f x) ∘ a ∘ ap (f o g) (! (ξ (f x)))) (ap-o (f o g) f (η x) ∘ ! (ap-o f (g o f) (η x))) 〉 
                ξ (f x) ∘ ap (f o g) (ap f (η x)) ∘ ap (f o g) (! (ξ (f x)))                      ≃〈 ap (λ a → ξ (f x) ∘ a ∘ ap (f o g) (! (ξ (f x)))) (ap (λ a → ! (ξ (f x)) ∘ ap f (η x) ∘ a) (!-invol (ξ (f (g (f x))))) ∘ ap-by-id (λ x' → ! (ξ x')) (ap f (η x))) 〉 
                ξ (f x) ∘ (! (ξ (f x)) ∘ (ap f (η x)) ∘ ξ (f (g (f x)))) ∘ ap (f o g) (! (ξ (f x))) ≃〈 rassoc-1-3-1 (ξ (f x)) (! (ξ (f x))) (ap f (η x)) (ξ (f (g (f x)))) (ap (f o g) (! (ξ (f x)))) 〉 
                ξ (f x) ∘ ! (ξ (f x)) ∘ (ap f (η x)) ∘ ξ (f (g (f x))) ∘ ap (f o g) (! (ξ (f x)))   ≃〈 !-inv-r-front (ξ (f x)) (ap f (η x) ∘ ξ (f (g (f x))) ∘ ap (f o g) (! (ξ (f x)))) 〉 
                (ap f (η x)) ∘ ξ (f (g (f x))) ∘ ap (f o g) (! (ξ (f x)))                          ≃〈 ap (λ a → ap f (η x) ∘ a ∘ ap (f o g) (! (ξ (f x)))) (inverses-natural g f ξ) 〉 
                (ap f (η x)) ∘ ap (f o g) (ξ ((f x))) ∘ ap (f o g) (! (ξ (f x)))                  ≃〈 ap (λ a → ap f (η x) ∘ ap (f o g) (ξ (f x)) ∘ a) (ap-! (f o g) (ξ (f x))) 〉 
                (ap f (η x)) ∘ ap (f o g) (ξ ((f x))) ∘ ! (ap (f o g) (ξ (f x)))                  ≃〈 ap (λ a → ap f (η x) ∘ a) (!-inv-r (ap (f o g) (ξ (f x)))) 〉 
                (ap f (η x) ∎)) 

 id-equiv : ∀ {A} -> Equiv A A
 id-equiv = ( (\ x -> x) , isequiv (λ x → x) (\ _ -> id) (\ _ -> id) (\ _ -> id))

 !equiv : ∀ {A B} → Equiv A B → Equiv B A
 !equiv (f , isequiv g α β γ) = 
   equiv g f β α 
    (λ y → α (g y)                                                                       ≃〈 ! (∘-assoc (α (g y)) (ap (λ x → g (f x)) (α (g y))) (! (α (g (f (g y)))))) ∘ move-right-right-! (α (g y)) (! (α (g (f (g y))))) _ (move-right-! (α (g y)) (α (g y) ∘ ! (! (α (g (f (g y)))))) _ (! (ap-by-id (λ x → ! (α x)) (α (g y))))) 〉 
           α (g y) ∘ ap (g o f) (α (g y)) ∘ ! (α (g (f (g y))))                          ≃〈 ap (λ a → α (g y) ∘ a ∘ ! (α (g (f (g y))))) (ap (ap g) (! (γ (g y))) ∘ ap-o g f (α (g y))) 〉 
           α (g y) ∘ ap g (β (f (g y))) ∘ ! (α (g (f (g y))))                            ≃〈 ap (λ a → α (g y) ∘ ap g a ∘ ! (α (g (f (g y))))) (inverses-natural g f β) 〉 
           α (g y) ∘ ap g (ap (f o g) (β y)) ∘ ! (α (g (f (g y))))                      ≃〈 ap (λ a → α (g y) ∘ a ∘ ! (α (g (f (g y))))) (ap-o (g o f) g (β y) ∘ ! (ap-o g (f o g) (β y))) 〉 
           α (g y) ∘ ap (g o f) (ap g (β y)) ∘ ! (α (g (f (g y))))                      ≃〈 ap (λ a → α (g y) ∘ a ∘ ! (α (g (f (g y))))) (ap (λ a → ! (α (g y)) ∘ ap g (β y) ∘ a) (!-invol (α (g (f (g y))))) ∘ ap-by-id (λ x → ! (α x)) (ap g (β y))) 〉 
           α (g y) ∘ (! (α (g y)) ∘ (ap g (β y)) ∘ α (g (f (g y)))) ∘ ! (α (g (f (g y)))) ≃〈 rassoc-1-3-1 (α (g y)) (! (α (g y))) (ap g (β y)) (α (g (f (g y)))) (! (α (g (f (g y)))))〉 
           α (g y) ∘ ! (α (g y)) ∘ (ap g (β y)) ∘ α (g (f (g y))) ∘ ! (α (g (f (g y))))   ≃〈 !-inv-r-front _ _ 〉 
           (ap g (β y)) ∘ α (g (f (g y))) ∘ ! (α (g (f (g y))))                          ≃〈 !-inv-r-back (ap g (β y)) (α (g (f (g y)))) 〉 
           (ap g (β y) ∎))

 -- ENH: can probably do this one without changing α or β too
 _∘equiv_ : ∀ {A B C} -> Equiv B C → Equiv A B -> Equiv A C
 _∘equiv_ (f , isequiv g α β γ) (f' , isequiv g' α' β' γ') = 
    improve (hequiv (f o f') (g' o g) (λ x → α' x ∘ ap g' (α (f' x))) (λ y → β y ∘ ap f (β' (g y))))

 infixr 10 _∘equiv_
 
 postulate 
   IsEquiv-HProp : {A B : Type} (f : A → B) → HProp (IsEquiv f)
   
 module EquivsSame where
   -- adjToWeq : {A B : Type} (f : A → B) → IsEquiv f → IsWEq A B f
   -- adjToWeq f (isequiv g α β γ) = λ y → (g y , β y) , (λ y' → pair≃ (α (fst y') ∘ ! (ap g (snd y')))
   --                                                           {!γ (fst y')!})