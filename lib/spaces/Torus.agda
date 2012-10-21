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
    
      
  

    resp-f : {A X : Set}
          -> {M : A}
          -> (g : A -> X)
          -> (p q : Id M M)
          -> Id (resp g (p ∘ q)) (resp g (q ∘ p)) ≃
             Id (resp g p ∘ resp g q) (resp g q ∘ resp g p)
    resp-f g p q = 
      Id (resp g (p ∘ q)) (resp g (q ∘ p)) 
         ≃〈 resp2 (λ x x' → Id x x') 
                  (resp-∘ g p q) 
                  (resp-∘ g q p) 〉 
      (Id (resp g p ∘ resp g q) (resp g q ∘ resp g p) ∎)


    f-resps : {C : Set}
           -> (a : C)
           -> (p q : a ≃ a)
           -> (f' : (p ∘ q) ≃ (q ∘ p))
           -> Id (resp (T-rec a p q f') (loop₁ ∘ loop₂)) (resp (T-rec a p q f') (loop₂ ∘ loop₁))
            ≃ Id (p ∘ q) (q ∘ p)
    f-resps a p q f' = 
      (Id (resp (T-rec a p q f') (loop₁ ∘ loop₂))
          (resp (T-rec a p q f') (loop₂ ∘ loop₁)))
          ≃〈 resp-f (T-rec a p q f') loop₁ loop₂ 〉
      (Id (resp (T-rec a p q f') loop₁ ∘ resp (T-rec a p q f') loop₂)
          (resp (T-rec a p q f') loop₂ ∘ resp (T-rec a p q f') loop₁))
          ≃〈 resp2 (λ x y → Id x y) 
                   (resp2 (λ x x' → x ∘ x') (βloop₁/rec a p q f') (βloop₂/rec a p q f')) 
                   (resp2 (λ x x' → x ∘ x') (βloop₂/rec a p q f') (βloop₁/rec a p q f')) 〉
      (Id (p ∘ q) (q ∘ p)) ∎

    postulate
      etaf/rec : {C X : Set}
        -> (a : C)
        -> (p q : a ≃ a)
        -> (comm : (p ∘ q) ≃ (q ∘ p))
        -> (g : C → X)
        -> (g o (T-rec a p q comm)) ≃ T-rec (g a) (resp g p) (resp g q) 
                                            (subst (λ x → x) (resp-f g p q) (resp (resp g) comm))
  
      βf/rec : {C : Set}
        -> (a : C)
        -> (p q : a ≃ a)
        -> (f' : (p ∘ q) ≃ (q ∘ p))
        -> resp (resp (T-rec a p q f')) f ≃ subst (λ x → x) (! (f-resps a p q f')) f'

    torus-X-to-rec : {X : Set}
                  -> (T -> X)
                  -> (Σ[ x ∶ X ] (Σ[ l1 ∶ Id x x ] (Σ[ l2 ∶ Id x x ] Id (l2 ∘ l1) (l1 ∘ l2))))
    torus-X-to-rec p = p Base , resp p loop₂ , 
                       (resp p loop₁ , subst (λ x → x) (resp-f p loop₁ loop₂) (resp (resp p) f))
                                        
    
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
                      ≃〈 Refl 〉 
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
        ≃〈 resp (λ p →
                      fst x ,
                      resp
                      (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                       (snd (snd (snd x))))
                      loop₂
                      ,
                      resp
                      (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                       (snd (snd (snd x))))
                      loop₁
                      , subst (λ x' → x') p (resp
                                               (resp
                                                (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                                                 (snd (snd (snd x)))))
                                               f))
                     (∘-unit-l (resp2 Id
                                   (resp-∘
                                    (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                                     (snd (snd (snd x))))
                                    loop₁ loop₂)
                                   (resp-∘
                                    (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                                     (snd (snd (snd x))))
                                    loop₂ loop₁))) 〉
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
       ≃〈 resp (λ p →
                     fst x ,
                     resp
                     (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                      (snd (snd (snd x))))
                     loop₂
                     ,
                     resp
                     (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                      (snd (snd (snd x))))
                     loop₁
                     ,
                     subst (λ x' → x')
                     (resp2 Id
                      (resp-∘
                       (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                        (snd (snd (snd x))))
                       loop₁ loop₂)
                      (resp-∘
                       (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                        (snd (snd (snd x))))
                       loop₂ loop₁))
                     p) 
                  (βf/rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) 〉
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
        (subst (λ x' → x') 
               (! (f-resps (fst x) 
                           (fst (snd (snd x))) 
                           (fst (snd x)) 
                           (snd (snd (snd x))))) 
                           (snd (snd (snd x)))))
       ≃〈 resp (λ p →
                     fst x ,
                     resp
                     (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                      (snd (snd (snd x))))
                     loop₂
                     ,
                     resp
                     (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                      (snd (snd (snd x))))
                     loop₁
                     , p (snd (snd (snd x)))) (sym (subst-∘ (λ x' → x') 
                                                   (resp2 Id
                                                    (resp-∘
                                                    (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                                                           (snd (snd (snd x))))
                                                           loop₁ loop₂)
                                                    (resp-∘
                                                           (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                                                           (snd (snd (snd x))))
                                                           loop₂ loop₁)) (!
                                                                 (f-resps (fst x) (fst (snd (snd x))) (fst (snd x))
                                                                          (snd (snd (snd x))))))) 〉
      ( fst x , resp (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂
      , resp (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁
      , subst (λ x' → x')
        (resp2 Id (resp-∘ (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁ loop₂)
                  (resp-∘ (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂ loop₁)
        ∘ (! (f-resps (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))))) 
        (snd (snd (snd x))))
        ≃〈 resp (λ p →
                      fst x ,
                      resp
                      (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                       (snd (snd (snd x))))
                      loop₂
                      ,
                      resp
                      (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                       (snd (snd (snd x))))
                      loop₁
                      ,
                      subst (λ x' → x')
                      (resp2 Id
                       (resp-∘
                        (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                         (snd (snd (snd x))))
                        loop₁ loop₂)
                       (resp-∘
                        (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                         (snd (snd (snd x))))
                        loop₂ loop₁)
                       ∘ ! p)
                      (snd (snd (snd x)))) 
                     (resp2 (λ x' x0 → x' ∘ x0) (∘-unit-l (resp2 Id
                                                             (resp2 _∘_
                                                              (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                                                               (snd (snd (snd x))))
                                                              (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                                                               (snd (snd (snd x)))))
                                                             (resp2 _∘_
                                                              (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                                                               (snd (snd (snd x))))
                                                              (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                                                               (snd (snd (snd x))))))) 
                                                (∘-unit-l (resp2 Id
                                                             (resp-∘
                                                              (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                                                               (snd (snd (snd x))))
                                                              loop₁ loop₂)
                                                             (resp-∘
                                                              (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                                                               (snd (snd (snd x))))
                                                              loop₂ loop₁)))) 〉
      ( fst x , resp (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂
      , resp (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁
      , subst (λ x' → x')
        (resp2 Id (resp-∘ (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁ loop₂)
                  (resp-∘ (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂ loop₁)
        ∘ !
            ( resp2 Id
              (resp2 _∘_
               (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))
               (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x)))))
              (resp2 _∘_
               (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))
               (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x)))))
             ∘
             resp2 Id
             (resp-∘
              (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
               (snd (snd (snd x))))
              loop₁ loop₂)
             (resp-∘
              (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
               (snd (snd (snd x))))
              loop₂ loop₁)))
        (snd (snd (snd x))))
        ≃〈 resp (λ p →
                      fst x ,
                      resp
                      (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                       (snd (snd (snd x))))
                      loop₂
                      ,
                      resp
                      (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                       (snd (snd (snd x))))
                      loop₁
                      ,
                      subst (λ x' → x')
                      (resp2 Id
                       (resp-∘
                        (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                         (snd (snd (snd x))))
                        loop₁ loop₂)
                       (resp-∘
                        (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                         (snd (snd (snd x))))
                        loop₂ loop₁)
                       ∘ p)
                      (snd (snd (snd x)))) 
           (!-∘ (resp2 Id
                   (resp2 _∘_
                    (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                     (snd (snd (snd x))))
                    (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                     (snd (snd (snd x)))))
                   (resp2 _∘_
                    (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                     (snd (snd (snd x))))
                    (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                     (snd (snd (snd x)))))) 
                (resp2 Id
                   (resp-∘
                    (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                     (snd (snd (snd x))))
                    loop₁ loop₂)
                   (resp-∘
                    (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                     (snd (snd (snd x))))
                    loop₂ loop₁))) 〉
      ( fst x , resp (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂
      , resp (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁
      , subst (λ x' → x')
        (resp2 Id (resp-∘ (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁ loop₂)
                  (resp-∘ (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂ loop₁)
        ∘ ! (resp2 Id
             (resp-∘
              (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
               (snd (snd (snd x))))
              loop₁ loop₂)
             (resp-∘
              (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
               (snd (snd (snd x))))
              loop₂ loop₁))
        ∘ ! (resp2 Id
              (resp2 _∘_
               (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))
               (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x)))))
              (resp2 _∘_
               (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))
               (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x)))))))
        (snd (snd (snd x))))
       ≃〈 Refl 〉
      ( fst x , resp (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂
      , resp (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁
      , subst (λ x' → x')
        (resp2 Id (resp-∘ (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁ loop₂)
                  (resp-∘ (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂ loop₁)
        ∘ ! (resp2 Id
             (resp-∘
              (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
               (snd (snd (snd x))))
              loop₁ loop₂)
             (resp-∘
              (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
               (snd (snd (snd x))))
              loop₂ loop₁))
        ∘ ! (resp2 Id
              (resp2 _∘_
               (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))
               (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x)))))
              (resp2 _∘_
               (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))
               (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x)))))))
        (snd (snd (snd x))))
        ≃〈 resp (λ p →
                      fst x ,
                      resp
                      (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                       (snd (snd (snd x))))
                      loop₂
                      ,
                      resp
                      (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                       (snd (snd (snd x))))
                      loop₁
                      , subst (λ x' → x') p (snd (snd (snd x)))) 
                (∘-assoc (resp2 Id
                            (resp-∘
                             (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                              (snd (snd (snd x))))
                             loop₁ loop₂)
                            (resp-∘
                             (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                              (snd (snd (snd x))))
                             loop₂ loop₁)) 
                         (!
                            (resp2 Id
                             (resp-∘
                              (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                               (snd (snd (snd x))))
                              loop₁ loop₂)
                             (resp-∘
                              (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                               (snd (snd (snd x))))
                              loop₂ loop₁))) 
                         (!
                            (resp2 Id
                             (resp2 _∘_
                              (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                               (snd (snd (snd x))))
                              (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                               (snd (snd (snd x)))))
                             (resp2 _∘_
                              (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                               (snd (snd (snd x))))
                              (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                               (snd (snd (snd x)))))))) 〉
      ( fst x , resp (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂
      , resp (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁
      , subst (λ x' → x')
        ((resp2 Id (resp-∘ (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁ loop₂)
                  (resp-∘ (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂ loop₁)
        ∘ ! (resp2 Id
             (resp-∘
              (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
               (snd (snd (snd x))))
              loop₁ loop₂)
             (resp-∘
              (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
               (snd (snd (snd x))))
              loop₂ loop₁)))
        ∘ ! (resp2 Id
              (resp2 _∘_
               (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))
               (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x)))))
              (resp2 _∘_
               (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))
               (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x)))))))
        (snd (snd (snd x))))
        ≃〈 resp (λ p →
                      fst x ,
                      resp
                      (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                       (snd (snd (snd x))))
                      loop₂
                      ,
                      resp
                      (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                       (snd (snd (snd x))))
                      loop₁
                      ,
                      subst (λ x' → x')
                      (p ∘
                       !
                       (resp2 Id
                        (resp2 _∘_
                         (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                          (snd (snd (snd x))))
                         (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                          (snd (snd (snd x)))))
                        (resp2 _∘_
                         (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                          (snd (snd (snd x))))
                         (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                          (snd (snd (snd x)))))))
                      (snd (snd (snd x)))) 
                (!-inv-r (resp2 Id
                           (resp-∘
                            (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                             (snd (snd (snd x))))
                            loop₁ loop₂)
                           (resp-∘
                            (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                             (snd (snd (snd x))))
                            loop₂ loop₁))) 〉
      ( fst x , resp (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂
      , resp (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁
      , subst (λ x' → x')
        (Refl ∘ ! (resp2 Id
              (resp2 _∘_
               (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))
               (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x)))))
              (resp2 _∘_
               (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))
               (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x)))))))
         (snd (snd (snd x))))
       ≃〈 resp (λ p →
                     fst x ,
                     resp
                     (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                      (snd (snd (snd x))))
                     loop₂
                     ,
                     resp
                     (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                      (snd (snd (snd x))))
                     loop₁
                     , subst (λ x' → x') p (snd (snd (snd x)))) (∘-unit-l 
               (!
                  (resp2 Id
                   (resp2 _∘_
                    (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                     (snd (snd (snd x))))
                    (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                     (snd (snd (snd x)))))
                   (resp2 _∘_
                    (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                     (snd (snd (snd x))))
                    (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                     (snd (snd (snd x)))))))) 〉
       ( fst x , resp (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂
      , resp (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁
      , subst (λ x' → x')
        (! (resp2 Id
              (resp2 _∘_
               (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))
               (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x)))))
              (resp2 _∘_
               (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))
               (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x)))))))
         (snd (snd (snd x))))
        ≃〈 resp
              (λ p →
                 fst x ,
                 resp
                 (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                  (snd (snd (snd x))))
                 loop₂
                 ,
                 resp
                 (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                  (snd (snd (snd x))))
                 loop₁
                 , subst (λ x' → x') p (snd (snd (snd x))))
              (resp2 (λ x' x0 → resp2 Id x' x0) 
                     (resp2-resps-1 _∘_ 
                                    (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                                           (snd (snd (snd x)))) 
                                    {!!}) 
                     (resp2-resps-1 _∘_ 
                                    (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                                       (snd (snd (snd x)))) 
                                    {!!})) 〉
      ( fst x , resp (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₂
      , resp (T-rec (fst x) (fst (snd (snd x))) (fst (snd x)) (snd (snd (snd x)))) loop₁
      , subst (λ x' → x')
        (! (resp2 Id
              (resp (λ x' → x' ∘ (fst (snd x))) 
                (βloop₁/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))
               ∘
               resp (λ y → resp
                             (T-rec (fst x) (fst (snd (snd x))) (fst (snd x))
                              (snd (snd (snd x))))
                             loop₁ ∘ y)
                (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))) 
              (resp (λ x' → x' ∘ fst (snd (snd x))) 
                (βloop₂/rec (fst x) (fst (snd (snd x))) (fst (snd x))
                (snd (snd (snd x))))
               ∘
               resp (λ y → resp
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
       ≃〈 Refl 〉
      (x ∎))

    torus-X-rec : {X : Set}
               -> (T -> X) ≃ (Σ[ x ∶ X ] (Σ[ l1 ∶ Id x x ] (Σ[ l2 ∶ Id x x ] Id (l2 ∘ l1) (l1 ∘ l2))))
    torus-X-rec = ua (isoToAdj (torus-X-to-rec , isiso rec-to-torus-X 
                                                       (λ y → app≃ rec-torus-X-id) 
                                                       (λ x → app≃ torus-X-rec-id)))
 
  open T

