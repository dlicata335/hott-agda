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
          -> (f' : (p ∘ q) ≃ (q ∘ p))
          -> T -> C
    T-rec a _ _ _ Base = a

    CommutatorDep : {C : T -> Set}
             (a' : C base) 
             (p' : subst C loop₁ a' ≃ a') 
             (q' : subst C loop₂ a' ≃ a') -> Set
    CommutatorDep {C} a' p' q' = subst (λ x → subst C x a' ≃ a') f 
                           (p' ∘ (resp (subst C loop₁) q') ∘ app≃ (subst-∘ C loop₁ loop₂)) 
                   ≃ q' ∘ (resp (subst C loop₂) p') ∘ app≃ (subst-∘ C loop₂ loop₁)

    T-elim : {C : T -> Set}
             (a' : C base) 
             (p' : subst C loop₁ a' ≃ a') 
             (q' : subst C loop₂ a' ≃ a')
             (f' : CommutatorDep {C} a' p' q') 
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
    
    resp-f : {X : Set}
          -> (p : T -> X)
          -> Id (resp p (loop₁ ∘ loop₂)) (resp p (loop₂ ∘ loop₁)) ≃
             Id (resp p loop₁ ∘ resp p loop₂) (resp p loop₂ ∘ resp p loop₁)
    resp-f p = 
      Id (resp p (loop₁ ∘ loop₂)) (resp p (loop₂ ∘ loop₁)) 
               ≃〈 resp2 (λ x x' → Id x x') 
                        (resp-∘ p loop₁ loop₂) 
                        (resp-∘ p loop₂ loop₁) 〉
      Id (resp p loop₁ ∘ resp p loop₂) (resp p loop₂ ∘ resp p loop₁) ∎

    torus-X-to-rec : {X : Set}
                  -> (T -> X)
                  -> (Σ[ x ∶ X ] (Σ[ l1 ∶ Id x x ] (Σ[ l2 ∶ Id x x ] Id (l2 ∘ l1) (l1 ∘ l2))))
    torus-X-to-rec p = p Base , resp p loop₂ , 
                       (resp p loop₁ , subst (λ x → x) (resp-f p) (resp (resp p) f))
                                        
    
    rec-to-torus-X : {X : Set}
                  -> (Σ[ x ∶ X ] (Σ[ l1 ∶ Id x x ] (Σ[ l2 ∶ Id x x ] Id (l2 ∘ l1) (l1 ∘ l2))))
                  -> (T -> X)
    rec-to-torus-X (fst , fst' , fst0 , snd) = T-rec fst fst0 fst' snd

    torus-X-rec-id-base : {X : Set} -> (t : T -> X) -> (b : T)
                       -> T-rec (t Base) (resp t loop₁) (resp t loop₂)
                                (subst (λ x → x) (Refl ∘ resp2 Id (resp-∘ t loop₁ loop₂) (resp-∘ t loop₂ loop₁))
                                (resp (resp t) f)) b
                        ≃ t b
    torus-X-rec-id-base t Base = Refl

    torus-X-rec-id : {X : Set}
                  -> (rec-to-torus-X o torus-X-to-rec) ≃ (λ (f : T -> X) → f)
    torus-X-rec-id = λ≃ (λ t → 
                     λ≃ (λ x → torus-X-rec-id-base t x))

    rec-torus-X-id : {X : Set}
                  -> (torus-X-to-rec o rec-to-torus-X) ≃ 
                     (λ (f : Σ[ x ∶ X ] (Σ[ l1 ∶ Id x x ] (Σ[ l2 ∶ Id x x ] Id (l2 ∘ l1) (l1 ∘ l2)))) → f)
    rec-torus-X-id = λ≃ (λ x → 
      (torus-X-to-rec o rec-to-torus-X) x 
                      ≃〈 {!!} 〉 
      ( fst x , resp (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂
      , resp (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁
      , subst (λ x' → x')
       (Refl ∘
        resp2 Id
        (resp-∘
         (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
          (snd (snd (snd x))))
         loop₁ loop₂)
        (resp-∘
         (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
          (snd (snd (snd x))))
         loop₂ loop₁))
       (resp
        (resp
         (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
          (snd (snd (snd x)))))
        f))
        ≃〈 {!!} 〉
      ( fst x , resp (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂
      , resp (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁
      , subst (λ x' → x')
        (resp2 Id
        (resp-∘
         (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
          (snd (snd (snd x))))
         loop₁ loop₂)
        (resp-∘
         (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
          (snd (snd (snd x))))
         loop₂ loop₁))
       (resp
        (resp
         (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
          (snd (snd (snd x)))))
        f))
       ≃〈 {!!} 〉
      ( fst x , (fst (snd x))
      , (fst (snd (snd x)))
      , snd (snd (snd x)))
       ≃〈 {!!} 〉
      (x ∎))

    torus-X-rec : {X : Set}
               -> (Σ[ x ∶ X ] (Σ[ l1 ∶ Id x x ] (Σ[ l2 ∶ Id x x ] Id (l2 ∘ l1) (l1 ∘ l2))))
               ≃ (T -> X)
    torus-X-rec = {!!}
  open T

