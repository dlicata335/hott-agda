{-# OPTIONS --type-in-type --without-K #-}

open import lib.BasicTypes 
open import lib.WEq 

module lib.spaces.Torus where

module Torus where
  private
    module T where
     private
       data T' : Set where
         Base : T'
     
     T : Set
     T = T'
  
     base : T
     base = Base
  
     postulate {- HoTT Axiom -}
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
              (p' : transport C loop₁ a' ≃ a') 
              (q' : transport C loop₂ a' ≃ a') -> Set
     CommutatorDep {C} a' p' q' = 
                       transport (λ x → transport C x a' ≃ a') f 
                             (p' ∘ (ap (transport C loop₁) q') ∘ ap≃ (transport-∘ C loop₁ loop₂)) 
                     ≃ q' ∘ (ap (transport C loop₂) p') ∘ ap≃ (transport-∘ C loop₂ loop₁)
  
     T-elim : {C : T -> Set}
              (a' : C base) 
              (p' : transport C loop₁ a' ≃ a') 
              (q' : transport C loop₂ a' ≃ a')
              (f' : CommutatorDep {C} a' p' q') 
           -> (x : T) -> C x
     T-elim a _ _ _ Base = a    
  
     postulate {- HoTT Axiom -}
       βloop₁/rec : {C : Set}
         -> (a : C)
         -> (p q : a ≃ a)
         -> (f : (p ∘ q) ≃ (q ∘ p))
         -> ap (T-rec a p q f) loop₁ ≃ p
       
       βloop₂/rec : {C : Set}
         -> (a : C)
         -> (p q : a ≃ a)
         -> (f : (p ∘ q) ≃ (q ∘ p))
         -> ap (T-rec a p q f) loop₂ ≃ q
  
     ap-f : {X : Set}
           -> (p : T -> X)
           -> Id (ap p (loop₁ ∘ loop₂)) (ap p (loop₂ ∘ loop₁)) ≃
              Id (ap p loop₁ ∘ ap p loop₂) (ap p loop₂ ∘ ap p loop₁)
     ap-f p = 
       Id (ap p (loop₁ ∘ loop₂)) (ap p (loop₂ ∘ loop₁)) 
                ≃〈 ap2 (λ x x' → Id x x') 
                         (ap-∘ p loop₁ loop₂) 
                         (ap-∘ p loop₂ loop₁) 〉
       Id (ap p loop₁ ∘ ap p loop₂) (ap p loop₂ ∘ ap p loop₁) ∎
  
     f-aps : {C : Set}
            -> (a : C)
            -> (p q : a ≃ a)
            -> (f' : (p ∘ q) ≃ (q ∘ p))
            -> Id (ap (T-rec a p q f') (loop₁ ∘ loop₂)) (ap (T-rec a p q f') (loop₂ ∘ loop₁))
             ≃ Id (p ∘ q) (q ∘ p)
     f-aps a p q f' = 
       (Id (ap (T-rec a p q f') (loop₁ ∘ loop₂))
           (ap (T-rec a p q f') (loop₂ ∘ loop₁)))
           ≃〈 ap-f (T-rec a p q f') 〉
       (Id (ap (T-rec a p q f') loop₁ ∘ ap (T-rec a p q f') loop₂)
           (ap (T-rec a p q f') loop₂ ∘ ap (T-rec a p q f') loop₁))
           ≃〈 ap2 (λ x y → Id x y) 
                    (ap2 (λ x x' → x ∘ x') (βloop₁/rec a p q f') (βloop₂/rec a p q f')) 
                    (ap2 (λ x x' → x ∘ x') (βloop₂/rec a p q f') (βloop₁/rec a p q f')) 〉
       (Id (p ∘ q) (q ∘ p)) ∎
     
     postulate {- HoTT Axiom -}
       βf/rec : {C : Set}
         -> (a : C)
         -> (p q : a ≃ a)
         -> (f' : (p ∘ q) ≃ (q ∘ p))
         -> ap (ap (T-rec a p q f')) f ≃ transport (λ x → x) (! (f-aps a p q f')) f'
  
     postulate {- HoTT Axiom -} 
       -- FIXME: prove using dependent elim instead
       Tη : {X : Set} {g : T -> X} -> 
            g ≃ (T-rec (g base) (ap g loop₁) (ap g loop₂) (ap-∘ g loop₂ loop₁ ∘ ap (ap g) f ∘ ! (ap-∘ g loop₁ loop₂))) 

  open T public

  T-rec' : {X : Set}
          -> (Σ[ x ∶ X ] (Σ[ l1 ∶ Id x x ] (Σ[ l2 ∶ Id x x ] Id (l1 ∘ l2) (l2 ∘ l1))))
          -> (T -> X)
  T-rec' (x , l1 , l2 , comm) = T-rec x l1 l2 comm

  postulate 
    ump : ∀ {X} → IsEquiv (T-rec'{X})
    

{-
    rec-to-torus-X-isWEq : ∀ {X} -> WEqBy _ _ (rec-to-torus-X{X})
    rec-to-torus-X-isWEq{X} g = (((g base) , ((ap g loop₁) , ((ap g loop₂) , 
                              ap-∘ g loop₂ loop₁ ∘ ap (ap g) f ∘ ! (ap-∘ g loop₁ loop₂))))
                              , ! Tη) 
                             , 
                             (λ { ((x , l1' , l2' , comm') , p) → 
                                pair≃ 
                                (transport
                                   (λ g' →
                                      Id
                                      {Σe X
                                       (λ x' →
                                          Σe (Id x' x')
                                          (λ l1 → Σe (Id x' x') (λ l2 → Id (l1 ∘ l2) (l2 ∘ l1))))}
                                      (x , l1' , l2' , comm')
                                      (g' base ,
                                       ap g' loop₁ ,
                                       ap g' loop₂ ,
                                       ap-∘ g' loop₂ loop₁ ∘
                                       ap (ap g') f ∘ ! (ap-∘ g' loop₁ loop₂)))
                                   p (pair≃ id (pair≃ (! (βloop₁/rec x l1' l2' comm')) 
                                            (pair≃ (! (βloop₂/rec x l1' l2' comm') ∘ 
                                            (fst
                                               (transport (λ l1 → Σe (Id x x) (λ l2 → Id (l1 ∘ l2) (l2 ∘ l1)))
                                                (! (βloop₁/rec x l1' l2' comm')) (l2' , comm'))
                                               ≃〈 ap fst 
                                                       (transport-Σ (! (βloop₁/rec x l1' l2' comm')) 
                                                                (λ _ → Id x x) 
                                                                (λ γ x' → Id (γ ∘ x') (x' ∘ γ)) 
                                                                (l2' , comm')) 〉
                                            transport (λ _ → Id x x) (! (βloop₁/rec x l1' l2' comm')) l2'
                                               ≃〈 ap (λ g' → g' l2') 
                                                       (transport-constant (! (βloop₁/rec x l1' l2' comm'))) 〉
                                            (l2' ∎))) 
                                   (transport
                                      (λ l2 →
                                         Id (ap (T-rec x l1' l2' comm') loop₁ ∘ l2)
                                         (l2 ∘ ap (T-rec x l1' l2' comm') loop₁))
                                      (! (βloop₂/rec x l1' l2' comm') ∘
                                       (id ∘
                                        ap (λ g' → g' l2')
                                        (transport-constant (! (βloop₁/rec x l1' l2' comm'))))
                                       ∘
                                       ap fst
                                       (transport-Σ (! (βloop₁/rec x l1' l2' comm')) (λ _ → Id x x)
                                        (λ γ x' → Id (γ ∘ x') (x' ∘ γ)) (l2' , comm')))
                                      (snd
                                       (transport (λ l1 → Σe (Id x x) (λ l2 → Id (l1 ∘ l2) (l2 ∘ l1)))
                                        (! (βloop₁/rec x l1' l2' comm')) (l2' , comm')))
                                      ≃〈 {!!} 〉 
                                   transport
                                      (λ l2 →
                                         Id (ap (T-rec x l1' l2' comm') loop₁ ∘ l2)
                                         (l2 ∘ ap (T-rec x l1' l2' comm') loop₁))
                                      (! (βloop₂/rec x l1' l2' comm') ∘
                                       (id ∘
                                        ap (λ g' → g' l2')
                                        (transport-constant (! (βloop₁/rec x l1' l2' comm'))))
                                       ∘
                                       ap fst
                                       (transport-Σ (! (βloop₁/rec x l1' l2' comm')) (λ _ → Id x x)
                                        (λ γ x' → Id (γ ∘ x') (x' ∘ γ)) (l2' , comm')))
                                        (transport (λ γ → Id (fst γ ∘ snd γ) (snd γ ∘ fst γ))
                                              (pair≃ (! (βloop₁/rec x l1' l2' comm')) id)
                                              comm')
                                      ≃〈 {!!} 〉 
                                   transport
                                      (λ l2 →
                                         Id (ap (T-rec x l1' l2' comm') loop₁ ∘ l2)
                                         (l2 ∘ ap (T-rec x l1' l2' comm') loop₁))
                                      (! (βloop₂/rec x l1' l2' comm') ∘
                                       ap (λ g' → g' l2')
                                        (transport-constant (! (βloop₁/rec x l1' l2' comm')))
                                       ∘
                                       ap fst
                                       (transport-Σ (! (βloop₁/rec x l1' l2' comm')) (λ _ → Id x x)
                                        (λ γ x' → Id (γ ∘ x') (x' ∘ γ)) (l2' , comm')))
                                      (transport (λ γ → Id (fst γ ∘ snd γ) (snd γ ∘ fst γ))
                                             (pair≃ (! (βloop₁/rec x l1' l2' comm')) id)
                                             comm')
                                      ≃〈 {!!} 〉
                                   (ap-∘ (T-rec x l1' l2' comm') loop₂ loop₁ ∘
                                      ap (ap (T-rec x l1' l2' comm')) f ∘
                                      ! (ap-∘ (T-rec x l1' l2' comm') loop₁ loop₂)
                                      ∎))))))
                                 {!!}})
-}

{-
    torus-X-to-rec : {X : Set}
                  -> (T -> X)
                  -> (Σ[ x ∶ X ] (Σ[ l1 ∶ Id x x ] (Σ[ l2 ∶ Id x x ] Id (l2 ∘ l1) (l1 ∘ l2))))
    torus-X-to-rec p = p Base , ap p loop₂ , 
                       (ap p loop₁ , transport (λ x → x) (ap-f p) (ap (ap p) f))
                                        
    
    rec-to-torus-X : {X : Set}
                  -> (Σ[ x ∶ X ] (Σ[ l1 ∶ Id x x ] (Σ[ l2 ∶ Id x x ] Id (l2 ∘ l1) (l1 ∘ l2))))
                  -> (T -> X)
    rec-to-torus-X (fst , fst' , fst0 , snd) = T-rec fst fst0 fst' snd

    torus-X-rec-id-base : {X : Set} -> (t : T -> X) -> (b : T)
                       -> T-rec (t Base) (ap t loop₁) (ap t loop₂)
                                (transport (λ x → x) (id ∘ ap2 Id (ap-∘ t loop₁ loop₂) (ap-∘ t loop₂ loop₁))
                                (ap (ap t) f)) b
                        ≃ t b
    torus-X-rec-id-base t Base = id

    torus-X-rec-id : {X : Set}
                  -> (rec-to-torus-X o torus-X-to-rec) ≃ (λ (f : T -> X) → f)
    torus-X-rec-id = λ≃ (λ t → 
                     λ≃ (λ x → torus-X-rec-id-base t x))

    rec-torus-X-id : {X : Set}
                  -> (torus-X-to-rec o rec-to-torus-X) ≃ 
                     (λ (f : Σ[ x ∶ X ] (Σ[ l1 ∶ Id x x ] (Σ[ l2 ∶ Id x x ] Id (l2 ∘ l1) (l1 ∘ l2)))) → f)
    rec-torus-X-id = λ≃ (λ x → 
      (torus-X-to-rec o rec-to-torus-X) x 
                      ≃〈 id 〉 
      ( fst x , ap (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂
      , ap (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁
      , transport (λ x' → x')
       (id ∘
        ap2 Id
        (ap-∘
         (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
          (snd (snd (snd x))))
         loop₁ loop₂)
        (ap-∘
         (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
          (snd (snd (snd x))))
         loop₂ loop₁))
       (ap
        (ap
         (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
          (snd (snd (snd x)))))
        f))
        ≃〈 ap (λ p →
                      fst x ,
                      ap
                      (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                       (snd (snd (snd x))))
                      loop₂
                      ,
                      ap
                      (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                       (snd (snd (snd x))))
                      loop₁
                      , transport (λ x' → x') p (ap
                                               (ap
                                                (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                                                 (snd (snd (snd x)))))
                                               f))
                     (∘-unit-l (ap2 Id
                                   (ap-∘
                                    (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                                     (snd (snd (snd x))))
                                    loop₁ loop₂)
                                   (ap-∘
                                    (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                                     (snd (snd (snd x))))
                                    loop₂ loop₁))) 〉
      ( fst x , ap (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂
      , ap (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁
      , transport (λ x' → x')
        (ap2 Id
        (ap-∘
         (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
          (snd (snd (snd x))))
         loop₁ loop₂)
        (ap-∘
         (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
          (snd (snd (snd x))))
         loop₂ loop₁))
       (ap
        (ap
         (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
          (snd (snd (snd x)))))
        f))
       ≃〈 ap (λ p →
                     fst x ,
                     ap
                     (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                      (snd (snd (snd x))))
                     loop₂
                     ,
                     ap
                     (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                      (snd (snd (snd x))))
                     loop₁
                     ,
                     transport (λ x' → x')
                     (ap2 Id
                      (ap-∘
                       (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                        (snd (snd (snd x))))
                       loop₁ loop₂)
                      (ap-∘
                       (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                        (snd (snd (snd x))))
                       loop₂ loop₁))
                     p) 
                  (βf/rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) 〉
      ( fst x , ap (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂
      , ap (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁
      , transport (λ x' → x')
        (ap2 Id
        (ap-∘
         (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
          (snd (snd (snd x))))
         loop₁ loop₂)
        (ap-∘
         (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
          (snd (snd (snd x))))
         loop₂ loop₁))
        (transport (λ x' → x') 
               (! (f-aps (fst x) 
                           (fst (snd (snd x))) 
                           (fst (snd x)) 
                           (snd (snd (snd x))))) 
                           (snd (snd (snd x)))))
       ≃〈 ap (λ p →
                     fst x ,
                     ap
                     (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                      (snd (snd (snd x))))
                     loop₂
                     ,
                     ap
                     (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                      (snd (snd (snd x))))
                     loop₁
                     , p (snd (snd (snd x)))) (sym (transport-∘ (λ x' → x') 
                                                   (ap2 Id
                                                    (ap-∘
                                                    (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                                                           (snd (snd (snd x))))
                                                           loop₁ loop₂)
                                                    (ap-∘
                                                           (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                                                           (snd (snd (snd x))))
                                                           loop₂ loop₁)) (!
                                                                 (f-aps (fst x) (fst (snd (snd x))) (fst (snd x))
                                                                          (snd (snd (snd x))))))) 〉
      ( fst x , ap (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂
      , ap (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁
      , transport (λ x' → x')
        (ap2 Id (ap-∘ (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁ loop₂)
                  (ap-∘ (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂ loop₁)
        ∘ (! (f-aps (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))))) 
        (snd (snd (snd x))))
        ≃〈 ap (λ p →
                      fst x ,
                      ap
                      (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                       (snd (snd (snd x))))
                      loop₂
                      ,
                      ap
                      (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                       (snd (snd (snd x))))
                      loop₁
                      ,
                      transport (λ x' → x')
                      (ap2 Id
                       (ap-∘
                        (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                         (snd (snd (snd x))))
                        loop₁ loop₂)
                       (ap-∘
                        (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                         (snd (snd (snd x))))
                        loop₂ loop₁)
                       ∘ ! p)
                      (snd (snd (snd x)))) 
                     (ap2 (λ x' x0 → x' ∘ x0) (∘-unit-l (ap2 Id
                                                             (ap2 _∘_
                                                              (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                                                               (snd (snd (snd x))))
                                                              (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                                                               (snd (snd (snd x)))))
                                                             (ap2 _∘_
                                                              (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                                                               (snd (snd (snd x))))
                                                              (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                                                               (snd (snd (snd x))))))) 
                                                (∘-unit-l (ap2 Id
                                                             (ap-∘
                                                              (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                                                               (snd (snd (snd x))))
                                                              loop₁ loop₂)
                                                             (ap-∘
                                                              (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                                                               (snd (snd (snd x))))
                                                              loop₂ loop₁)))) 〉
      ( fst x , ap (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂
      , ap (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁
      , transport (λ x' → x')
        (ap2 Id (ap-∘ (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁ loop₂)
                  (ap-∘ (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂ loop₁)
        ∘ !
            ( ap2 Id
              (ap2 _∘_
               (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))
               (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x)))))
              (ap2 _∘_
               (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))
               (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x)))))
             ∘
             ap2 Id
             (ap-∘
              (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
               (snd (snd (snd x))))
              loop₁ loop₂)
             (ap-∘
              (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
               (snd (snd (snd x))))
              loop₂ loop₁)))
        (snd (snd (snd x))))
        ≃〈 ap (λ p →
                      fst x ,
                      ap
                      (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                       (snd (snd (snd x))))
                      loop₂
                      ,
                      ap
                      (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                       (snd (snd (snd x))))
                      loop₁
                      ,
                      transport (λ x' → x')
                      (ap2 Id
                       (ap-∘
                        (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                         (snd (snd (snd x))))
                        loop₁ loop₂)
                       (ap-∘
                        (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                         (snd (snd (snd x))))
                        loop₂ loop₁)
                       ∘ p)
                      (snd (snd (snd x)))) 
           (!-∘ (ap2 Id
                   (ap2 _∘_
                    (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                     (snd (snd (snd x))))
                    (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                     (snd (snd (snd x)))))
                   (ap2 _∘_
                    (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                     (snd (snd (snd x))))
                    (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                     (snd (snd (snd x)))))) 
                (ap2 Id
                   (ap-∘
                    (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                     (snd (snd (snd x))))
                    loop₁ loop₂)
                   (ap-∘
                    (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                     (snd (snd (snd x))))
                    loop₂ loop₁))) 〉
      ( fst x , ap (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂
      , ap (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁
      , transport (λ x' → x')
        (ap2 Id (ap-∘ (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁ loop₂)
                  (ap-∘ (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂ loop₁)
        ∘ ! (ap2 Id
             (ap-∘
              (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
               (snd (snd (snd x))))
              loop₁ loop₂)
             (ap-∘
              (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
               (snd (snd (snd x))))
              loop₂ loop₁))
        ∘ ! (ap2 Id
              (ap2 _∘_
               (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))
               (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x)))))
              (ap2 _∘_
               (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))
               (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x)))))))
        (snd (snd (snd x))))
       ≃〈 id 〉
      ( fst x , ap (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂
      , ap (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁
      , transport (λ x' → x')
        (ap2 Id (ap-∘ (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁ loop₂)
                  (ap-∘ (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂ loop₁)
        ∘ ! (ap2 Id
             (ap-∘
              (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
               (snd (snd (snd x))))
              loop₁ loop₂)
             (ap-∘
              (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
               (snd (snd (snd x))))
              loop₂ loop₁))
        ∘ ! (ap2 Id
              (ap2 _∘_
               (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))
               (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x)))))
              (ap2 _∘_
               (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))
               (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x)))))))
        (snd (snd (snd x))))
        ≃〈 ap (λ p →
                      fst x ,
                      ap
                      (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                       (snd (snd (snd x))))
                      loop₂
                      ,
                      ap
                      (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                       (snd (snd (snd x))))
                      loop₁
                      , transport (λ x' → x') p (snd (snd (snd x)))) 
                (∘-assoc (ap2 Id
                            (ap-∘
                             (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                              (snd (snd (snd x))))
                             loop₁ loop₂)
                            (ap-∘
                             (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                              (snd (snd (snd x))))
                             loop₂ loop₁)) 
                         (!
                            (ap2 Id
                             (ap-∘
                              (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                               (snd (snd (snd x))))
                              loop₁ loop₂)
                             (ap-∘
                              (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                               (snd (snd (snd x))))
                              loop₂ loop₁))) 
                         (!
                            (ap2 Id
                             (ap2 _∘_
                              (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                               (snd (snd (snd x))))
                              (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                               (snd (snd (snd x)))))
                             (ap2 _∘_
                              (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                               (snd (snd (snd x))))
                              (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                               (snd (snd (snd x)))))))) 〉
      ( fst x , ap (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂
      , ap (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁
      , transport (λ x' → x')
        ((ap2 Id (ap-∘ (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁ loop₂)
                  (ap-∘ (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂ loop₁)
        ∘ ! (ap2 Id
             (ap-∘
              (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
               (snd (snd (snd x))))
              loop₁ loop₂)
             (ap-∘
              (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
               (snd (snd (snd x))))
              loop₂ loop₁)))
        ∘ ! (ap2 Id
              (ap2 _∘_
               (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))
               (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x)))))
              (ap2 _∘_
               (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))
               (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x)))))))
        (snd (snd (snd x))))
        ≃〈 ap (λ p →
                      fst x ,
                      ap
                      (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                       (snd (snd (snd x))))
                      loop₂
                      ,
                      ap
                      (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                       (snd (snd (snd x))))
                      loop₁
                      ,
                      transport (λ x' → x')
                      (p ∘
                       !
                       (ap2 Id
                        (ap2 _∘_
                         (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                          (snd (snd (snd x))))
                         (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                          (snd (snd (snd x)))))
                        (ap2 _∘_
                         (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                          (snd (snd (snd x))))
                         (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                          (snd (snd (snd x)))))))
                      (snd (snd (snd x)))) 
                (!-inv-r (ap2 Id
                           (ap-∘
                            (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                             (snd (snd (snd x))))
                            loop₁ loop₂)
                           (ap-∘
                            (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                             (snd (snd (snd x))))
                            loop₂ loop₁))) 〉
      ( fst x , ap (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂
      , ap (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁
      , transport (λ x' → x')
        (id ∘ ! (ap2 Id
              (ap2 _∘_
               (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))
               (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x)))))
              (ap2 _∘_
               (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))
               (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x)))))))
         (snd (snd (snd x))))
       ≃〈 ap (λ p →
                     fst x ,
                     ap
                     (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                      (snd (snd (snd x))))
                     loop₂
                     ,
                     ap
                     (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                      (snd (snd (snd x))))
                     loop₁
                     , transport (λ x' → x') p (snd (snd (snd x)))) (∘-unit-l 
               (!
                  (ap2 Id
                   (ap2 _∘_
                    (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                     (snd (snd (snd x))))
                    (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                     (snd (snd (snd x)))))
                   (ap2 _∘_
                    (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                     (snd (snd (snd x))))
                    (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                     (snd (snd (snd x)))))))) 〉
       ( fst x , ap (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂
      , ap (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁
      , transport (λ x' → x')
        (! (ap2 Id
              (ap2 _∘_
               (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))
               (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x)))))
              (ap2 _∘_
               (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))
               (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x)))))))
         (snd (snd (snd x))))
        ≃〈 {!!} 〉
      ( fst x , ap (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂
      , ap (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁
      , transport (λ x' → x')
        (! (ap2 Id
              (ap (λ x' → x' ∘ (fst (snd x))) 
                (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))
               ∘
               ap (λ y → ap
                             (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                              (snd (snd (snd x))))
                             loop₁ ∘ y)
                (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))) 
              (ap (λ x' → x' ∘ fst (snd (snd x))) 
                (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))
               ∘
               ap (λ y → ap
                             (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                              (snd (snd (snd x))))
                             loop₂ ∘ y)
                (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x)))))))
         (snd (snd (snd x))))
         ≃〈 {!!} 〉
      ( fst x , (fst (snd x))
      , (fst (snd (snd x)))
      , snd (snd (snd x)))
       ≃〈 id 〉
      (x ∎))

    torus-X-rec : {X : Set}
               -> (T -> X) ≃ (Σ[ x ∶ X ] (Σ[ l1 ∶ Id x x ] (Σ[ l2 ∶ Id x x ] Id (l2 ∘ l1) (l1 ∘ l2))))
    torus-X-rec = ua (isoToAdj (torus-X-to-rec , isiso rec-to-torus-X 
                                                       (λ y → ap≃ rec-torus-X-id) 
                                                       (λ x → ap≃ torus-X-rec-id)))
    -}
