{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open import lib.cubical.Cubical

module misc.JUnique where

  module Lemma (A : Type) (a0 : A) (R : A -> Type) (r0 : R a0) where

    IsIdSystem : Type 
    IsIdSystem = (C : Σ R → Type) (b0 : C (a0 , r0)) → 
                  Σ (λ (PI : (p : Σ R) → C p) →
                       PI (a0 , r0) == b0)

    left : IsIdSystem -> Contractible (Σ R)
    left hasJ = (a0 , r0) , fst (hasJ (Path (a0 , r0)) id)

    right : Contractible (Σ R) -> IsIdSystem 
    right cR C b0 = (λ p → transport C (snd cR p ∘ ! (snd cR (a0 , r0))) b0) , 
                    ap (λ h → transport C h b0) (!-inv-r (snd cR (a0 , r0)))

    rl : (i : IsIdSystem) -> right (left i) == i
    rl i = λ≃ (λ C → λ≃ (λ b0 → pair= (λ≃ (fst (i _ (! (snd (i C b0)) ∘ ap (λ h → transport C h b0) (!-inv-r (snd (left i) (a0 , r0)))))))
                                       (PathOver=.in-PathOver-= (whisker-square id 
                                                                                (! (Π≃β (fst (i (λ z → Path (transport C (snd (left i) z ∘ ! (snd (left i) (a0 , r0))) b0) (fst (i C b0) z)) (! (snd (i C b0)) ∘ ap (λ h → transport C h b0) (!-inv-r (snd (left i) (a0 , r0))))))) ∘ 
                                                                                 ! (snd (i (λ z → Path (transport C (snd (left i) z ∘ ! (snd (left i) (a0 , r0))) b0) (fst (i C b0) z)) (! (snd (i C b0)) ∘ ap (λ h → transport C h b0) (!-inv-r (snd (left i) (a0 , r0)))))))
                                                                                (! (ap-constant b0 (λ≃ (fst (i (λ z → Path (transport C (snd (left i) z ∘ ! (snd (left i) (a0 , r0))) b0) (fst (i C b0) z)) (! (snd (i C b0)) ∘ ap (λ h → transport C h b0) (!-inv-r (snd (left i) (a0 , r0))))))))) id 
                                                                                (coh _ _))))) where
       coh : {A : Type} {a b c : A} (p : a == b) (q : c == b) -> Square p (! q ∘ p) id q
       coh id id = id

    eqv : Equiv IsIdSystem (Contractible (Σ R))
    eqv = improve (hequiv left right rl (λ y → HProp-unique (Contractible-is-HProp _) _ _))

  module LemmaForId (A : Type) (a : A) = Lemma A a (Id{A} a) id

  overall : (A : Type) (a0 : A) -> HProp ((C : (Σ \ a -> Id a0 a) → Type) (b0 : C (a0 , id)) → 
                                          Σ (λ (PI : (p : Σ \ a -> Id a0 a) → C p) →
                                               PI (a0 , id) == b0))
  overall A a = transport HProp (! (ua (LemmaForId.eqv A a))) (Contractible-is-HProp _)

