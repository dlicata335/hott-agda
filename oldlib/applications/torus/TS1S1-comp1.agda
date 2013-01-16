{-# OPTIONS --type-in-type --without-K #-}
open import lib.Prelude
open Paths
open S¹
open T
open NDPair
open import applications.torus.TS1S1-functions

module applications.torus.TS1S1-comp1 where
  
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
     {!subst-loop₂ ∘ ? ∘ ?!}
-}
  torus-circles-torus : (t : T) -> (circles-to-torus (torus-to-circles t)) ≃ t
  torus-circles-torus = T-elim {λ t' → circles-to-torus (torus-to-circles t') ≃ t'} 
                               Refl
                               subst-loop₁ 
                               subst-loop₂
                               {!!} --subst-loops-commute

