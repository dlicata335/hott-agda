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
  
    postulate {- HoTT Axiom -}
      loop : Path base base
  
    S¹-rec : {C : Set} 
           -> (c : C)
           -> (α : c ≃ c)
           -> S¹ -> C
    S¹-rec a _ Base = a
  
    S¹-elim :  (C : S¹ -> Set)
            -> (c : C base) 
               (α : Path (transport C loop c) c)
            -> (x : S¹) -> C x
    S¹-elim _ x _ Base = x

    S¹-induction :  (C : S¹ -> Set)
            -> (c : C base) 
               (α : Path (transport C loop c) c)
            -> (x : S¹) -> C x
    S¹-induction = S¹-elim
  
    postulate {- HoTT Axiom -} 
      βloop/rec : {C : Set} 
           -> (c : C)
           -> (α : Path c c)
           -> Path (ap (S¹-rec c α) loop) α
  
      βloop/elim : {C : S¹ -> Set} 
                 -> (c : C base) (α : Path (transport C loop c) c)
                 -> Path (apd (S¹-induction C c α) loop) α

  open S¹

  -- Equivalence between (S¹ -> X) and Σe X (\ x → Id x x)
  module S¹-Lemmas where

    S¹η-rec : {C : Set} 
              (M : S¹ -> C)
              (N : S¹)
            -> M N ≃ (S¹-rec (M base) (ap M loop) N)
    S¹η-rec {C} M N = S¹-elim (λ x → M x ≃ S¹-rec (M base) (ap M loop) x)
                            id 
                            (!-inv-r (ap M loop) 
                             ∘ ap (λ x → ap M loop ∘ x) (∘-unit-l (! (ap M loop)))
                             ∘ ap (λ x → x ∘ id ∘ ! (ap M loop)) (βloop/rec {C} (M base) (ap M loop))
                             ∘ transport-Path M (S¹-rec (M base) (ap M loop)) loop id
                            )
                            N 

    S¹η : {C : S¹ -> Set} 
            (M : (x : S¹) -> C x)
            (N : S¹)
          -> M N ≃ (S¹-elim C (M base) (apd M loop) N)
    S¹η {C} M N = S¹-elim (λ x → M x ≃ S¹-elim C (M base) (apd M loop) x)
                            id 
                            (!-inv-r (apd M loop) 
                             ∘ ap (λ x → apd M loop ∘ x) (∘-unit-l (! (apd M loop)))
                             ∘ ap (λ x → x ∘ id ∘ ! (apd M loop)) (βloop/elim {C} (M base) (apd M loop))
                             ∘ transport-Path-d M (S¹-elim _ (M base) (apd M loop)) loop id)
                            N 

    fromgen : {X : Set} -> Σ[ x ∶ X ] (Id x x) -> (S¹ -> X)
    fromgen (fst , snd) = S¹-rec fst snd
  
    togen : {X : Set} -> (S¹ -> X) -> Σ[ x ∶ X ] (Id x x)
    togen {X} f = f base , ap f loop
  
    fromto : {X : Set} -> (fromgen o togen) ≃ (λ (f : S¹ -> X) → f)
    fromto {X} = λ≃ (λ f → λ≃ (λ x → ! (S¹η-rec f x)))

    tofrom : {X : Set} -> (togen o fromgen) ≃ (λ (f : Σ[ x ∶ X ] (Id x x)) → f)
    tofrom {X} = λ≃ (λ x → 
      (fst x , ap (S¹-rec (fst x) (snd x)) loop) 
             ≃〈 ap (λ y → fst x , y) (βloop/rec (fst x) (snd x)) 〉
      (fst x , snd x) 
             ≃〈 id 〉
      id)

    free : {X : Set} -> (S¹ -> X) ≃ (Σ[ x ∶ X ] (Id x x))
    free {X} = ua (improve (hequiv togen 
                                   fromgen 
                                   (λ x → ap≃ fromto) 
                                   (λ y → ap≃ tofrom)))



  open S¹

  


