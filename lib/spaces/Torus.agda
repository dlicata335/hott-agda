{-# OPTIONS --type-in-type --without-K #-}

open import lib.BasicTypes 

module lib.spaces.Torus where

  open Paths

  module T where
    private
      data T' : Set where
        Base : T'
    
    T : Set
    T = T'

    base : T
    base = Base

    postulate
      loop₁ : base ≃ base
      loop₂ : base ≃ base
      f : (loop₁ ∘ loop₂) ≃ (loop₂ ∘ loop₁)

    T-rec :  {C : Set}
          -> (a : C)
          -> (p q : a ≃ a)
          -> (f : (p ∘ q) ≃ (q ∘ p))
          -> T -> C
    T-rec a _ _ _ Base = a

    T-elim :  {C : T -> Set}
           -> (a' : C base) 
           -> (p' : subst C loop₁ a' ≃ a') (q' : subst C loop₂ a' ≃ a')
           -> (f' : subst (λ x → subst C x a' ≃ a') f (p' ∘ (resp (subst C loop₁) q') ∘ app≃ (subst-∘ C loop₁ loop₂)) 
                    ≃ q' ∘ (resp (subst C loop₂) p') ∘ app≃ (subst-∘ C loop₂ loop₁))
           -> (x : T) -> C x
    T-elim a _ _ _ Base = a

    postulate
      βloop₁/rec : {C : Set}
        -> (a : C)
        -> (p q : a ≃ a)
        -> (f : (p ∘ q) ≃ (q ∘ p))
        -> resp (T-rec a p q f) loop₁ ≃ p
      
      βloop₂/rec : {C : Set}
        -> (a : C)
        -> (p q : a ≃ a)
        -> (f : (p ∘ q) ≃ (q ∘ p))
        -> resp (T-rec a p q f) loop₂ ≃ q
  
  open T

