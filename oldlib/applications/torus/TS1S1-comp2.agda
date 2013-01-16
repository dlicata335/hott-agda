{-# OPTIONS --type-in-type --without-K #-}
open import lib.Prelude
open Paths
open S¹
open T
open NDPair
open import applications.torus.TS1S1-functions

module applications.torus.TS1S1-comp2 where
  

  circles-base-loop : subst (λ s₂ → torus-to-circles (circles-to-torus' S¹.base s₂) ≃ (S¹.base , s₂)) 
                            loop Refl 
                    ≃ Refl
  circles-base-loop = 
    subst
      (λ s₂ →
         torus-to-circles (circles-to-torus' S¹.base s₂) ≃ (S¹.base , s₂))
      loop Refl
      ≃〈 subst-Id (λ s₂ → torus-to-circles (circles-to-torus' S¹.base s₂)) 
                   (λ x → S¹.base , x) 
                   loop Refl 〉
    resp (λ x → S¹.base , x) loop ∘ Refl ∘ 
    (! (resp (λ s₂ → torus-to-circles (circles-to-torus' S¹.base s₂)) loop))
      ≃〈 resp (λ y → resp (λ x → S¹.base , x) loop ∘ y) 
               (∘-unit-l (!
                            (resp (λ s₂ → torus-to-circles (circles-to-torus' S¹.base s₂))
                             loop))) 〉
    resp (λ x → S¹.base , x) loop ∘ (! (resp (λ s₂ → torus-to-circles (circles-to-torus' S¹.base s₂)) loop))
      ≃〈 resp (λ y → resp (λ x → S¹.base , x) loop ∘ ! y) 
               (resp-o torus-to-circles (circles-to-torus' S¹.base) loop) 〉
    resp (λ x → S¹.base , x) loop ∘ (! (resp torus-to-circles (resp (circles-to-torus' S¹.base) loop)))
      ≃〈 resp
            (λ y → resp (λ x → S¹.base , x) loop ∘ ! (resp torus-to-circles y))
            (βloop/rec T.base loop₂) 〉
    resp (λ x → S¹.base , x) loop ∘ (! (resp torus-to-circles loop₂)) 
      ≃〈 resp (λ y → resp (λ x → S¹.base , x) loop ∘ ! y) 
               (βloop₂/rec (S¹.base , S¹.base) 
                           (nondep-pair≃ loop Refl) 
                           (nondep-pair≃ Refl loop) 
                           S¹-f) 〉
    resp (λ x → S¹.base , x) loop ∘ (! (nondep-pair≃ (Refl{_}{S¹.base}) loop))
      ≃〈 resp (λ x → x ∘ ! (nondep-pair≃ Refl loop)) 
               (resp-×-snd (λ x → x) S¹.base loop) 〉
    nondep-pair≃ (resp (λ _ → S¹.base) loop) (resp (λ x → x) loop) ∘ (! (nondep-pair≃ Refl loop))
      ≃〈 resp (λ y → nondep-pair≃ y (resp (λ x → x) loop) ∘ ! (nondep-pair≃ Refl loop)) 
              (resp-constant S¹.base loop) 〉
    nondep-pair≃ Refl (resp (λ x → x) loop) ∘ (! (nondep-pair≃ Refl loop))
      ≃〈 resp (λ y → nondep-pair≃ Refl y ∘ ! (nondep-pair≃ Refl loop)) 
              (resp-id loop) 〉
    nondep-pair≃ Refl loop ∘ ! (nondep-pair≃ Refl loop)
      ≃〈 !-inv-r (nondep-pair≃ Refl loop) 〉
    Refl ∎

-- Another version of the proof, but takes advantage of the underlying representation of nondep-pair≃.
-- The above version instead uses a general relationship between resp and nondep-pair≃.
{-
      ≃〈 resp (λ y → resp (λ x → S¹.base , x) loop ∘ ! y) 
              (resp2-resps-2 _,_ Refl loop) 〉
    resp (λ x → S¹.base , x) loop ∘ (! (resp (λ y → S¹.base , y) loop ∘ resp (λ x → x , S¹.base) Refl))
      ≃〈 Refl 〉
    resp (λ x → S¹.base , x) loop ∘ (! (resp (λ x → S¹.base , x) loop ∘ Refl))
      ≃〈 resp (λ y → resp (λ x → S¹.base , x) loop ∘ ! y) 
               (∘-unit-r (resp (λ x → S¹.base , x) loop)) 〉
    resp (λ x → S¹.base , x) loop ∘ (! (resp (λ x → S¹.base , x) loop ))
      ≃〈 !-inv-r (resp (λ x → S¹.base , x) loop) 〉
    Refl ∎
-}

  circles-base : (s₂ : S¹) -> torus-to-circles (circles-to-torus' S¹.base s₂) ≃ (S¹.base , s₂) 
  circles-base = (S¹-elim
                     {λ s₂ →
                       torus-to-circles (circles-to-torus' S¹.base s₂) ≃ (S¹.base , s₂)}
                     Refl 
                     circles-base-loop)  

  circles-loop-base : subst (λ s₁ → (s₂ : S¹) → torus-to-circles (circles-to-torus' s₁ s₂) ≃ (s₁ , s₂))
                      loop circles-base S¹.base ≃ circles-base S¹.base
  circles-loop-base = 
    subst
      (λ s₁ →
         (s₂ : S¹) → torus-to-circles (circles-to-torus' s₁ s₂) ≃ (s₁ , s₂))
      loop circles-base S¹.base
      ≃〈 resp (λ y → y S¹.base) 
               (subst-Π2 S¹ (λ s₁ s₂ → torus-to-circles (circles-to-torus' s₁ s₂) ≃ (s₁ , s₂)) loop 
               circles-base) 〉
    (λ s₂ → subst (λ s₁ → torus-to-circles (circles-to-torus' s₁ s₂) ≃ (s₁ , s₂)) loop (circles-base s₂)) 
      S¹.base
      ≃〈 Refl 〉
    subst (λ s₁ → torus-to-circles (circles-to-torus' s₁ S¹.base) ≃ (s₁ , S¹.base)) loop (circles-base S¹.base)
      ≃〈 Refl 〉
    subst (λ s₁ → torus-to-circles (circles-to-torus' s₁ S¹.base) ≃ (s₁ , S¹.base)) loop Refl
      ≃〈 subst-Id (λ s₁ → torus-to-circles (circles-to-torus' s₁ S¹.base)) 
                   (λ s₁ → s₁ , S¹.base) 
                   loop Refl 〉
    resp (λ s₁ → s₁ , S¹.base) loop ∘ Refl ∘ 
    ! (resp (λ s₁ → torus-to-circles (circles-to-torus' s₁ S¹.base)) loop) 
      ≃〈 resp (λ x → resp (λ s₁ → s₁ , S¹.base) loop ∘ x) 
               (∘-unit-l (!
                            (resp (λ s₁ → torus-to-circles (circles-to-torus' s₁ S¹.base))
                             loop))) 〉
    resp (λ s₁ → s₁ , S¹.base) loop ∘
    ! (resp (λ s₁ → torus-to-circles (circles-to-torus' s₁ S¹.base)) loop)
      ≃〈 resp (λ x → resp (λ s₁ → s₁ , S¹.base) loop ∘ ! x) 
              (resp-o torus-to-circles (λ s₁ → circles-to-torus' s₁ S¹.base) loop) 〉
    resp (λ s₁ → s₁ , S¹.base) loop ∘
    ! (resp torus-to-circles (resp (λ s₁ → circles-to-torus' s₁ S¹.base) loop))
      ≃〈 resp
            (λ x →
               resp (λ s₁ → s₁ , S¹.base) loop ∘ ! (resp torus-to-circles x))
            (resp-app-1-nd {δ = loop} {F = circles-to-torus'} {M = S¹.base}) 〉
    resp (λ s₁ → s₁ , S¹.base) loop ∘
    ! (resp torus-to-circles (app≃ (resp circles-to-torus' loop) {S¹.base}))
      ≃〈 resp
            (λ x →
               resp (λ s₁ → s₁ , S¹.base) loop ∘
               ! (resp torus-to-circles (app≃ x {S¹.base})))
            (βloop/rec (S¹-rec T.base loop₂) (λ≃ circles-fst-loop)) 〉
    resp (λ s₁ → s₁ , S¹.base) loop ∘
    ! (resp torus-to-circles (app≃ (λ≃ circles-fst-loop) {S¹.base}))
      ≃〈 resp
            (λ x →
               resp (λ s₁ → s₁ , S¹.base) loop ∘ ! (resp torus-to-circles x))
            (Π≃β circles-fst-loop {N = S¹.base}) 〉
    resp (λ s₁ → s₁ , S¹.base) loop ∘
    ! (resp torus-to-circles (circles-fst-loop S¹.base))
      ≃〈 Refl 〉
    resp (λ s₁ → s₁ , S¹.base) loop ∘ ! (resp torus-to-circles loop₁)
      ≃〈 resp (λ x → resp (λ s₁ → s₁ , S¹.base) loop ∘ ! x) 
               (βloop₁/rec (S¹.base , S¹.base) 
                           (nondep-pair≃ loop Refl) 
                           (nondep-pair≃ Refl loop) 
                           S¹-f) 〉
    resp (λ s₁ → s₁ , S¹.base) loop ∘ ! (nondep-pair≃ loop Refl)
      ≃〈 resp (λ x → x ∘ ! (nondep-pair≃ loop Refl)) 
               (resp-×-fst (λ x → x) S¹.base loop) 〉
    nondep-pair≃ (resp (λ x → x) loop) (resp (λ _ → S¹.base) loop) ∘ ! (nondep-pair≃ loop Refl)
      ≃〈 resp
            (λ x →
               nondep-pair≃ (resp (λ x' → x') loop) x ∘
               ! (nondep-pair≃ loop Refl))
            (resp-constant S¹.base loop) 〉
    nondep-pair≃ (resp (λ x → x) loop) Refl ∘ ! (nondep-pair≃ loop Refl)
      ≃〈 resp (λ x → nondep-pair≃ x Refl ∘ ! (nondep-pair≃ loop Refl)) 
               (resp-id loop) 〉
    nondep-pair≃ loop Refl ∘ ! (nondep-pair≃ loop Refl)
      ≃〈 !-inv-r (nondep-pair≃ loop Refl) 〉
    Refl ∎

  circles-loop-loop : subst (λ x → ((subst (λ s₁ → (s₂ : S¹) → torus-to-circles (circles-to-torus' s₁ s₂) 
                                                               ≃ (s₁ , s₂))
                                         loop 
                                         circles-base) x)
                                   ≃ (circles-base x))
                            loop 
                            circles-loop-base 
                      ≃ circles-loop-base
  circles-loop-loop = 
    subst (λ x → ((subst (λ s₁ → (s₂ : S¹) → torus-to-circles (circles-to-torus' s₁ s₂) ≃ (s₁ , s₂))
                         loop circles-base) x)
                 ≃ (circles-base x))
          loop 
          circles-loop-base 
      ≃〈 subst-Id-d (subst
                        (λ s₁ →
                           (s₂ : S¹) → torus-to-circles (circles-to-torus' s₁ s₂) ≃ (s₁ , s₂))
                        loop circles-base) 
                     circles-base 
                     loop 
                     circles-loop-base 〉
    respd circles-base loop ∘
    resp (subst (λ s₂ → torus-to-circles (circles-to-torus' S¹.base s₂) ≃ (S¹.base , s₂)) loop) 
         circles-loop-base ∘
    ! (respd  (subst (λ s₁ → (s₂ : S¹) → torus-to-circles (circles-to-torus' s₁ s₂) 
                      ≃ (s₁ , s₂)) loop circles-base) loop)
      ≃〈 resp
            (λ x →
               x ∘
               resp
               (subst
                (λ s₂ →
                   torus-to-circles (circles-to-torus' S¹.base s₂) ≃ (S¹.base , s₂))
                loop)
               circles-loop-base
               ∘
               !
               (respd
                (subst
                 (λ s₁ →
                    (s₂ : S¹) → torus-to-circles (circles-to-torus' s₁ s₂) ≃ (s₁ , s₂))
                 loop circles-base)
                loop))
            (βloop/elim {λ s₂ →
                       torus-to-circles (circles-to-torus' S¹.base s₂) ≃ (S¹.base , s₂)} 
              (Refl{_}{S¹.base , S¹.base}) circles-base-loop) 〉
    circles-base-loop ∘
    resp (subst (λ s₂ → torus-to-circles (circles-to-torus' S¹.base s₂) ≃ (S¹.base , s₂)) loop) 
         circles-loop-base ∘
    ! (respd  (subst (λ s₁ → (s₂ : S¹) → torus-to-circles (circles-to-torus' s₁ s₂) 
                      ≃ (s₁ , s₂)) loop circles-base) loop)
      ≃〈 Refl 〉 -- η-expansion
    circles-base-loop ∘
    resp (λ x → subst (λ s₂ → torus-to-circles (circles-to-torus' S¹.base s₂) ≃ (S¹.base , s₂))
                      loop x)
         circles-loop-base ∘
    ! (respd (λ x → subst (λ s₁ → (s₂ : S¹) → torus-to-circles (circles-to-torus' s₁ s₂) ≃ (s₁ , s₂))
                          loop circles-base x) loop)
      ≃〈 {!!} 〉
    circles-base-loop ∘
    resp (λ x → resp (λ s₂ → S¹.base , {!!}) loop ∘ 
                x ∘ 
                ! (resp (λ s₂ → torus-to-circles (circles-to-torus' S¹.base s₂)) loop)) 
         circles-loop-base ∘
    ! (respd (λ x → subst (λ s₁ → (s₂ : S¹) → torus-to-circles (circles-to-torus' s₁ s₂) ≃ (s₁ , s₂))
                          loop circles-base x) loop)
      ≃〈 {!!} 〉
    circles-loop-base ∎

  circles-loop : (x : S¹) -> subst (λ s₁ → (s₂ : S¹) → torus-to-circles (circles-to-torus' s₁ s₂) ≃ (s₁ , s₂))
                 loop circles-base x ≃ circles-base x
  circles-loop = S¹-elim
                   {λ x →
                      subst
                      (λ s₁ →
                         (s₂ : S¹) → torus-to-circles (circles-to-torus' s₁ s₂) ≃ (s₁ , s₂))
                      loop circles-base x
                      ≃ circles-base x}
                   circles-loop-base 
                   circles-loop-loop

  circles-torus-circles' : (s₁ s₂ : S¹) -> (torus-to-circles (circles-to-torus' s₁ s₂)) ≃ (s₁ , s₂)
  circles-torus-circles' = S¹-elim
                             {λ s₁ →
                                (s₂ : S¹) → torus-to-circles (circles-to-torus' s₁ s₂) ≃ (s₁ , s₂)}
                             circles-base
                             (λ≃ circles-loop)

  circles-torus-circles : (s : S¹ × S¹) -> (torus-to-circles (circles-to-torus s)) ≃ s
  circles-torus-circles s = circles-torus-circles' (fst s) (snd s)