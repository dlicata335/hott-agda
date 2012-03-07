{-# OPTIONS --type-in-type --without-K #-}

open import lib.BasicTypes 

module lib.spaces.Circle where

  open Paths

  module S¹ where
    private
      data S¹' : Set where
        Base : S¹'

    S¹ : Set
    S¹ = S¹'

    base : S¹
    base = Base

    postulate
      loop : base ≃ base

    S¹-rec : {C : Set} 
           -> (a : C)
           -> (p : a ≃ a)
           -> S¹ -> C
    S¹-rec a _ Base = a

    S¹-elim :  {C : S¹ -> Set} 
            -> (a : C base) (p : subst C loop a ≃ a)
            -> (x : S¹) -> C x
    S¹-elim a _ Base = a

    postulate 
      βloop/rec : {C : Set} 
           -> (a : C)
           -> (p : a ≃ a)
           -> resp (S¹-rec a p) loop ≃ p

      βloop/elim : {C : S¹ -> Set} 
                 -> (a : C base) (p : subst C loop a ≃ a)
                 -> respd (S¹-elim{C} a p) loop ≃ p

  open S¹

  


