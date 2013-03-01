-- FIXME move to library


{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude

module homotopy.HStructure where

  record H-Structure (A : Type) (a0 : A) : Type where
   field 
     _⊙_      : A → A → A
     unitl    : ((a : A) → a0 ⊙ a ≃ a)
     unitr    : ((a : A) → a ⊙ a0 ≃ a)
     unitcoh  : unitl a0 ≃ unitr a0 
     isequivl : ((a : A) → IsEquiv (_⊙_ a))

  H-S¹ : H-Structure S¹.S¹ S¹.base
  H-S¹ = record { _⊙_ = mult;
                  unitl = λ _ → id;
                  unitr = S¹.S¹-elim _ id ((((!-inv-r S¹.loop ∘ ap (λ x → S¹.loop ∘ ! x) red) ∘
                                               ap (λ x → x ∘ ! (ap (λ z → mult z S¹.base) S¹.loop))
                                               (ap-id S¹.loop)) ∘
                                              ap (λ x → ap (λ x' → x') S¹.loop ∘ x)
                                              (∘-unit-l (! (ap (λ z → mult z S¹.base) S¹.loop)))) ∘ transport-Path (λ z → mult z S¹.base) (λ z → z) S¹.loop id);
                  unitcoh = id;
                  isequivl = S¹.S¹-elim _ (snd id-equiv) (HProp-unique (IsEquiv-HProp (λ x → x)) _ _) } where
    mutual
     mult : S¹.S¹ -> S¹.S¹ -> S¹.S¹
     mult = S¹.S¹-rec (λ x → x) mult-loop

     mult-hom = (S¹.S¹-elim _ S¹.loop ((!-inv-r-back S¹.loop S¹.loop ∘ ap (λ x → x ∘ S¹.loop ∘ ! x) (ap-id S¹.loop)) ∘ transport-Path (λ x → x) (λ x → x) S¹.loop S¹.loop))

     mult-loop = (λ≃ mult-hom)

    red : (ap (λ z → mult z S¹.base) S¹.loop) ≃ S¹.loop
    red = ((Π≃β mult-hom {S¹.base}) ∘ ap (λ x → ap≃ x {S¹.base}) (S¹.βloop/rec (\ x -> x) (mult-loop))) ∘ ap-o (λ f → f S¹.base) mult S¹.loop
