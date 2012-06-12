{-# OPTIONS --type-in-type --without-K #-}
open import lib.Prelude
open Paths
open S¹
open T
open NDPair

module applications.TS1S1 where
  
  S¹-f : nondep-pair≃ loop Refl ∘ nondep-pair≃ Refl loop ≃ nondep-pair≃ Refl loop ∘ nondep-pair≃ loop Refl
  S¹-f = nondep-pair≃ loop Refl ∘ nondep-pair≃ Refl loop 
                      ≃〈 ∘-× loop Refl Refl loop 〉
         nondep-pair≃ (loop ∘ Refl) (Refl ∘ loop)      
                      ≃〈 resp (λ x → nondep-pair≃ x (Refl ∘ loop)) 
                               (∘-unit-r loop) 〉
         nondep-pair≃ loop (Refl ∘ loop)               
                      ≃〈 resp (λ x → nondep-pair≃ loop x) 
                               (∘-unit-l loop) 〉
         nondep-pair≃ loop loop                        
                      ≃〈 resp (λ x → nondep-pair≃ x loop) 
                               (sym (∘-unit-l loop)) 〉
         nondep-pair≃ (Refl ∘ loop) loop               
                      ≃〈 resp (λ x → nondep-pair≃ (Refl ∘ loop) x) 
                               (sym (∘-unit-r loop)) 〉
         nondep-pair≃ (Refl ∘ loop) (loop ∘ Refl)      
                      ≃〈 sym (∘-× Refl loop loop Refl) 〉
         nondep-pair≃ Refl loop ∘ nondep-pair≃ loop Refl ∎

  -- Mapping from Torus to Two Circles
  torus-to-circles : T -> S¹ × S¹
  torus-to-circles = T-rec a' p' q' f'
    where a' = S¹.base , S¹.base
          p' = nondep-pair≃ loop Refl
          q' = nondep-pair≃ Refl loop
          f' = S¹-f 

  circles-fst-loop : (x : S¹) -> S¹-rec T.base loop₂ x ≃ S¹-rec T.base loop₂ x
  circles-fst-loop = 
       (S¹-elim {λ x → S¹-rec T.base loop₂ x ≃ S¹-rec T.base loop₂ x}
                loop₁
                (subst (λ x → S¹-rec T.base loop₂ x ≃ S¹-rec T.base loop₂ x) loop loop₁
                       ≃〈 subst-Id (S¹-rec T.base loop₂) 
                                    (S¹-rec T.base loop₂) 
                                    loop 
                                    loop₁ 〉
                 resp (S¹-rec T.base loop₂) loop ∘ loop₁ ∘ ! (resp (S¹-rec T.base loop₂) loop)
                       ≃〈 resp (λ x → x ∘ loop₁ ∘ ! (resp (S¹-rec T.base loop₂) loop)) 
                                (βloop/rec T.base loop₂)〉
                 loop₂ ∘ loop₁ ∘ ! (resp (S¹-rec T.base loop₂) loop) 
                       ≃〈 resp (λ x → loop₂ ∘ loop₁ ∘ ! x) 
                                (βloop/rec T.base loop₂) 〉
                 loop₂ ∘ loop₁ ∘ ! loop₂   ≃〈 ∘-assoc loop₂ loop₁ (! loop₂) 〉
                 (loop₂ ∘ loop₁) ∘ ! loop₂ ≃〈 resp (λ x → x ∘ ! loop₂) (sym f) 〉
                 (loop₁ ∘ loop₂) ∘ ! loop₂ ≃〈 sym (∘-assoc loop₁ loop₂ (! loop₂)) 〉
                 loop₁ ∘ loop₂ ∘ ! loop₂   ≃〈 resp (λ x → loop₁ ∘ x) (!-inv-r loop₂) 〉
                 loop₁ ∘ Refl              ≃〈 ∘-unit-r loop₁ 〉 (loop₁ ∎)))


  -- Mapping from Two Circles to Torus
  circles-to-torus' : S¹ -> S¹ -> T
  circles-to-torus' = 
    S¹-rec 
      (S¹-rec T.base loop₂)
      (λ≃ circles-fst-loop)

  -- The uncurried version of the above
  circles-to-torus : S¹ × S¹ -> T
  circles-to-torus = uncurry circles-to-torus' 

  -- Lemmas for proving the torus identity
  subst-loop₁ : subst (λ t' → circles-to-torus (torus-to-circles t') ≃ t') loop₁ Refl ≃ Refl
  subst-loop₁ = 
    subst (λ t' → circles-to-torus (torus-to-circles t') ≃ t') loop₁ Refl
          ≃〈 subst-Id (λ t' → circles-to-torus (torus-to-circles t')) 
                       (λ x → x) 
                       loop₁ 
                       Refl 〉
    resp (λ x → x) loop₁ ∘ Refl ∘ ! (resp (λ t' → circles-to-torus (torus-to-circles t')) loop₁)
          ≃〈 resp (λ y → resp (λ x → x) loop₁ ∘ y) 
                   (∘-unit-l (! (resp (λ t' → circles-to-torus (torus-to-circles t')) loop₁))) 〉
    resp (λ x → x) loop₁ ∘ ! (resp (λ t' → circles-to-torus (torus-to-circles t')) loop₁)
          ≃〈 resp (λ y → y ∘ ! (resp (λ t' → circles-to-torus (torus-to-circles t')) loop₁)) 
                   (resp-id loop₁) 〉
    loop₁ ∘ ! (resp (λ t' → circles-to-torus (torus-to-circles t')) loop₁)
          ≃〈 resp (λ y → loop₁ ∘ ! y) 
                   (resp-o circles-to-torus torus-to-circles loop₁) 〉
    loop₁ ∘ ! (resp circles-to-torus (resp torus-to-circles loop₁)) 
          ≃〈 resp (λ x → loop₁ ∘ ! (resp circles-to-torus x)) 
                   (βloop₁/rec (S¹.base , S¹.base) 
                               (nondep-pair≃ loop Refl) 
                               (nondep-pair≃ Refl loop) S¹-f) 〉
    loop₁ ∘ ! (resp circles-to-torus (nondep-pair≃ loop (Refl{_}{S¹.base})))
       ≃〈 resp (λ x → loop₁ ∘ ! x) (resp-uncurry circles-to-torus' loop (Refl{_}{S¹.base})) 〉 
    loop₁ ∘ ! (resp2 circles-to-torus' loop (Refl{_}{S¹.base})) 
          ≃〈 resp (λ x → loop₁ ∘ ! x) (resp2-resps-1 circles-to-torus' loop (Refl{_}{S¹.base})) 〉 
    loop₁ ∘ ! (resp (\ x -> circles-to-torus' x S¹.base) loop 
             ∘ resp (circles-to-torus' S¹.base) (Refl{_}{S¹.base})) ≃〈 Refl 〉 
    loop₁ ∘ ! (resp (\ x -> circles-to-torus' x S¹.base) loop 
             ∘ Refl) 
          ≃〈 resp (λ x → loop₁ ∘ ! x) 
                   (∘-unit-r (resp (λ x → circles-to-torus' x S¹.base) loop)) 〉 
    loop₁ ∘ ! (resp (\ x -> (circles-to-torus' x) S¹.base) loop) 
          ≃〈 resp (\ x -> loop₁ ∘ ! x) 
                   (resp-app-1-nd {δ = loop} {F = circles-to-torus'}{M = S¹.base}) 〉 
    loop₁ ∘ ! (app≃ (resp circles-to-torus' loop) {S¹.base}) 
          ≃〈 resp (λ x → loop₁ ∘ ! (app≃ x {S¹.base})) 
                   (βloop/rec (S¹-rec T.base loop₂) 
                              (λ≃ circles-fst-loop)) 〉
    loop₁ ∘ ! (app≃ (λ≃ circles-fst-loop) {S¹.base}) 
          ≃〈 resp (λ x → loop₁ ∘ ! x) 
                   (Π≃β circles-fst-loop {S¹.base}) 〉
    loop₁ ∘ ! (circles-fst-loop S¹.base) ≃〈 Refl 〉
    loop₁ ∘ ! loop₁ ≃〈 !-inv-r loop₁ 〉
    (Refl{_}{T.base}) ∎

  subst-loop₂ : subst (λ t' → circles-to-torus (torus-to-circles t') ≃ t') loop₂ Refl ≃ Refl
  subst-loop₂ =
    subst (λ t' → circles-to-torus (torus-to-circles t') ≃ t') loop₂ Refl
          ≃〈 subst-Id (λ t' → circles-to-torus (torus-to-circles t')) 
                       (λ x → x) 
                       loop₂ 
                       Refl 〉
    resp (λ x → x) loop₂ ∘ Refl ∘ ! (resp (λ t' → circles-to-torus (torus-to-circles t')) loop₂)
          ≃〈 resp (λ y → resp (λ x → x) loop₂ ∘ y) 
                   (∘-unit-l (! (resp (λ t' → circles-to-torus (torus-to-circles t')) loop₂))) 〉 
    resp (λ x → x) loop₂ ∘ ! (resp (λ t' → circles-to-torus (torus-to-circles t')) loop₂)
          ≃〈 resp
                (λ y → y ∘ ! (resp (λ t' → circles-to-torus (torus-to-circles t')) loop₂))
                (resp-id loop₂) 〉
    loop₂ ∘ ! (resp (λ t' → circles-to-torus (torus-to-circles t')) loop₂)
          ≃〈 resp (λ y → loop₂ ∘ ! y)
                   (resp-o circles-to-torus 
                           torus-to-circles 
                           loop₂) 〉 
    loop₂ ∘ ! (resp circles-to-torus (resp torus-to-circles loop₂)) 
          ≃〈 resp (λ x → loop₂ ∘ ! (resp circles-to-torus x)) 
                   (βloop₂/rec (S¹.base , S¹.base) 
                               (nondep-pair≃ loop Refl) 
                               (nondep-pair≃ Refl loop) 
                               S¹-f) 〉
    loop₂ ∘ ! (resp circles-to-torus (nondep-pair≃ (Refl{_}{S¹.base}) loop)) 
          ≃〈 resp (λ x → loop₂ ∘ ! x) 
                   (resp-uncurry circles-to-torus' (Refl{_}{S¹.base}) loop) 〉
    loop₂ ∘ ! (resp2 circles-to-torus' (Refl{_}{S¹.base}) loop) 
          ≃〈 resp (λ x → loop₂ ∘ ! x) 
                   (resp2-resps-2 circles-to-torus' (Refl{_}{S¹.base}) loop) 〉
    loop₂ ∘ ! (resp (circles-to-torus' S¹.base) loop ∘ 
               resp (λ x → circles-to-torus' x S¹.base) (Refl{_}{S¹.base})) ≃〈 Refl 〉
    loop₂ ∘ ! (resp (circles-to-torus' S¹.base) loop) ≃〈 Refl 〉
    loop₂ ∘ ! (resp (S¹-rec T.base loop₂) loop) 
          ≃〈 resp (λ x → loop₂ ∘ ! x) 
                   (βloop/rec T.base loop₂) 〉
    loop₂ ∘ ! loop₂ ≃〈 !-inv-r loop₂ 〉
    Refl{_}{T.base} ∎

    
{-
  subst-loops-commute : CommutatorDep {(λ t' → circles-to-torus (torus-to-circles t') ≃ t')} 
                        Refl subst-loop₁ subst-loop₂
  subst-loops-commute = 
    subst
      (λ x →
         subst (λ t' → circles-to-torus (torus-to-circles t') ≃ t') x Refl ≃
         Refl)
      f
      (subst-loop₁ ∘
       resp
       (subst (λ t' → circles-to-torus (torus-to-circles t') ≃ t') loop₁)
       subst-loop₂
       ∘
       app≃
       (subst-∘ (λ t' → circles-to-torus (torus-to-circles t') ≃ t') loop₁ loop₂))
      ≃〈 {!!} 〉 
     {!!}
  -}
  torus-circles-torus : (t : T) -> (circles-to-torus (torus-to-circles t)) ≃ t
  torus-circles-torus = T-elim {λ t' → circles-to-torus (torus-to-circles t') ≃ t'} 
                               Refl
                               subst-loop₁ 
                               subst-loop₂
                               {!!} --subst-loops-commute

  circles-torus-circles' : (s₁ s₂ : S¹) -> (torus-to-circles (circles-to-torus' s₁ s₂)) ≃ (s₁ , s₂)
  circles-torus-circles' = S¹-elim
                             {λ s₁ →
                                (s₂ : S¹) → torus-to-circles (circles-to-torus' s₁ s₂) ≃ (s₁ , s₂)}
                             (S¹-elim
                                {λ s₂ →
                                   torus-to-circles (circles-to-torus' S¹.base s₂) ≃ (S¹.base , s₂)}
                                Refl {!!}) 
                             {!!}

  circles-torus-circles : (s : S¹ × S¹) -> (torus-to-circles (circles-to-torus s)) ≃ s
  circles-torus-circles s = circles-torus-circles' (fst s) (snd s)