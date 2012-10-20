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
            -> (a : C base) 
               (p : subst C loop a ≃ a)
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
  
    -- Equivalence between (S¹ -> X) and Σe X (\ x → Id x x)

    rec-to-circle-X : {X : Set} -> Σ[ x ∶ X ] (Id x x) -> (S¹ -> X)
    rec-to-circle-X (fst , snd) = S¹-rec fst snd
  
    circle-X-to-rec : {X : Set} -> (S¹ -> X) -> Σ[ x ∶ X ] (Id x x)
    circle-X-to-rec {X} f = f Base , resp f loop
  
    SX-rec-SX-id-base : {X : Set} -> (f : S¹ -> X) -> (b : S¹) -> S¹-rec (f Base) (resp f loop) b ≃ f b
    SX-rec-SX-id-base f Base = Refl

    SX-rec-SX-id : {X : Set} -> (rec-to-circle-X o circle-X-to-rec) ≃ (λ (f : S¹ -> X) → f)
    SX-rec-SX-id {X} = λ≃ (λ f → 
                      λ≃ (SX-rec-SX-id-base f))

    rec-SX-rec-id : {X : Set} -> (circle-X-to-rec o rec-to-circle-X) ≃ (λ (f : Σ[ x ∶ X ] (Id x x)) → f)
    rec-SX-rec-id {X} = λ≃ (λ x → 
      (fst x , resp (S¹-rec (fst x) (snd x)) loop) 
             ≃〈 resp (λ y → fst x , y) (βloop/rec (fst x) (snd x)) 〉
      (fst x , snd x) 
             ≃〈 Refl 〉
      Refl)

    circle-X-rec : {X : Set} -> (S¹ -> X) ≃ (Σ[ x ∶ X ] (Id x x))
    circle-X-rec {X} = ua (isoToAdj (circle-X-to-rec , 
                                     isiso rec-to-circle-X 
                                           (λ y → app≃ rec-SX-rec-id) 
                                           (λ x → app≃ SX-rec-SX-id)))

  open S¹

  


