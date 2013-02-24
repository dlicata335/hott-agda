
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

  {-
  example : H-Structure S¹.S¹ S¹.base
  example = record { _⊙_ = S¹.S¹-rec (λ x → x) (λ≃ (S¹.S¹-elim _ S¹.loop {!!}));
                           unitl = λ _ → id;
                           unitr = S¹.S¹-elim _ id {!FIXME!};
                           unitcoh = id;
                           isequivl = S¹.S¹-elim _ (snd id-equiv) (HProp-unique (IsEquiv-HProp (λ x → x)) _ _) }
  -}