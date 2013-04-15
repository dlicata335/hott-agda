
{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.NType
open import lib.Prods

module lib.WEq where

  HFiber : {A B : Type} -> (A -> B) -> B -> Type
  HFiber f y = Σ \x -> Path (f x) y
  
  IsWEq : {A B : Type} -> (f : A -> B) -> Type
  IsWEq {A}{B} f = (y : B) -> Contractible (HFiber f y)
  
  WEq : (A B : Type) -> Type
  WEq A B = Σ \f -> IsWEq{A}{B} f

  IsWEq-HProp : {A B : Type} (f : A → B) → HProp (IsWEq f)
  IsWEq-HProp f = unique-HProp (λ w w' → λ≃ (λ y → HProp-unique (Contractible-is-HProp _) _ _))

  transport-HFiber-arg : {A B : Type} -> (f : A -> B) -> {b1 b2 : B}
                             (β : b1 ≃ b2)
                           -> transport (HFiber f) β ≃ \ p → (fst p , β ∘ snd p)
  transport-HFiber-arg f id = λ≃ \ p -> pair≃ id (! (∘-unit-l (snd p)))


{-
  -- same as adjoint equiv: 

  -- can write out the maps explicitly but don't want to do the beta reduction
  -- don't want to do the beta reduction

  module EquivsSame where
   weqToAdj : {A B : Type} (f : A → B) → IsWEq f → IsEquiv f
   weqToAdj f w = isequiv (λ y → fst (fst (w y))) 
                          (λ x → fst≃ (snd (w (f x)) (x , id)))
                          (λ y → snd (fst (w y)))
                          (λ x → ∘-unit-l (ap f (ap fst (snd (w (f x)) (x , id)))) ∘
                                   move-right-right-! (snd (fst (w (f x))))
                                   (ap f (ap fst (snd (w (f x)) (x , id)))) id
                                   (snd≃ (snd (w (f x)) (x , id)) ∘
                                    ! (transport-Path-pre' f (ap fst (snd (w (f x)) (x , id))) (snd (fst (w (f x)))))))

   adjToWeq : {A B : Type} (f : A → B) → IsEquiv f → IsWEq f
   adjToWeq f (isequiv g α β γ) = λ y → (g y , β y) , (λ y' → pair≃ (α (fst y') ∘ ! (ap g (snd y')))
                                                                    (coh y y')) where
            coh : (y : _) (y' : HFiber f y) -> (transport (λ x → Id (f x) y) (α (fst y') ∘ ! (ap g (snd y'))) (β y))
                                               ≃ (snd y')
            coh y y' = transport (λ x → Id (f x) y) (α (fst y') ∘ ! (ap g (snd y'))) (β y) ≃〈 transport-Path-pre' f (α (fst y') ∘ ! (ap g (snd y'))) (β y) 〉 
                       β y ∘ ! (ap f (α (fst y') ∘ ! (ap g (snd y')))) ≃〈 {!IsWEq f!} 〉 
                       β y ∘ ! (ap f (α (fst y')) ∘ ap f (! (ap g (snd y')))) ≃〈 {!!} 〉 
                       β y ∘ ! (ap f (! (ap g (snd y')))) ∘ ! (ap f (α (fst y'))) ≃〈 {!!} 〉 
                       β y ∘ (ap f (! (! (ap g (snd y'))))) ∘ ! (ap f (α (fst y')))  ≃〈 {!!} 〉 
                       β y ∘ (ap f (ap g (snd y'))) ∘ ! (ap f (α (fst y'))) ≃〈 {! γ (fst y') !}〉 
                       β y ∘ (ap f (ap g (snd y'))) ∘ ! (β (f (fst y'))) ≃〈 {!snd y'!} 〉 
                       β y ∘ (ap (f o g) (snd y')) ∘ ! (β (f (fst y'))) ≃〈 {!!} 〉 
                       β y ∘ (! (β y) ∘ (snd y') ∘ β (f (fst y'))) ∘ ! (β (f (fst y'))) ≃〈 {!!} 〉 
                       (snd y' ∎)

   inv1 : {A B : Type} (f : A → B) → (e : IsEquiv f) → weqToAdj f (adjToWeq f e) ≃ e
   inv1 {A} f (isequiv g α β γ) = isequiveq _ (λ≃ (λ x → Σ≃β1 (α x) _)) {!!} where
     isequiveq : ∀ {α'} (γ' : (x : A) →  Path (β (f x)) (ap f (α' x)))
               -> (p : α' ≃ α)
               -> (λ x → ap (ap f) (ap≃ p) ∘ γ' x) ≃ γ
               -> (isequiv g α' β γ') ≃ (isequiv g α β γ) 
     isequiveq γ' id p = ap (isequiv g α β) (λ≃ (λ x → ap≃ p {x} ∘ ! (∘-unit-l (γ' x))))

   inv2 : {A B : Type} (f : A → B) → (e : IsWEq f) → adjToWeq f (weqToAdj f e) ≃ e
   inv2 {A} f w = HProp-unique (IsWEq-HProp f) _ _
-}

