
{-# OPTIONS --type-in-type --without-K #-}
open import lib.Prelude

open S¹
open Torus using (T; T-rec ; T-elim)
module homotopy.TS1S1 where

  module T = Torus
  
  S¹-f : pair×≃ loop id ∘ pair×≃ id loop ≃ pair×≃ id loop ∘ pair×≃ loop id
  S¹-f = pair×≃ loop id ∘ pair×≃ id loop 
                      ≃〈 ∘-× loop id id loop 〉
         pair×≃ (loop ∘ id) (id ∘ loop)      
                      ≃〈 ap (λ x → pair×≃ x (id ∘ loop)) 
                               (∘-unit-r loop) 〉
         pair×≃ loop (id ∘ loop)               
                      ≃〈 ap (λ x → pair×≃ loop x) 
                               (∘-unit-l loop) 〉
         pair×≃ loop loop                        
                      ≃〈 ap (λ x → pair×≃ x loop) 
                               (! (∘-unit-l loop)) 〉
         pair×≃ (id ∘ loop) loop               
                      ≃〈 ap (λ x → pair×≃ (id ∘ loop) x) 
                               (! (∘-unit-r loop)) 〉
         pair×≃ (id ∘ loop) (loop ∘ id)      
                      ≃〈 ! (∘-× id loop loop id) 〉
         pair×≃ id loop ∘ pair×≃ loop id ∎

  -- Mapping from Torus to Two Circles
  torus-to-circles : T -> S¹ × S¹
  torus-to-circles = T-rec a' p' q' f'
    where a' = S¹.base , S¹.base
          p' = pair×≃ loop id
          q' = pair×≃ id loop
          f' = S¹-f 

  circles-fst-loop : (x : S¹) -> S¹-rec T.base T.loop₂ x ≃ S¹-rec T.base T.loop₂ x
  circles-fst-loop = 
       (S¹-elim (λ x → S¹-rec T.base T.loop₂ x ≃ S¹-rec T.base T.loop₂ x)
                T.loop₁
                (transport (λ x → S¹-rec T.base T.loop₂ x ≃ S¹-rec T.base T.loop₂ x) loop T.loop₁
                       ≃〈 transport-Path (S¹-rec T.base T.loop₂) 
                                        (S¹-rec T.base T.loop₂) 
                                        loop 
                                        T.loop₁ 〉
                 ap (S¹-rec T.base T.loop₂) loop ∘ T.loop₁ ∘ ! (ap (S¹-rec T.base T.loop₂) loop)
                       ≃〈 ap (λ x → x ∘ T.loop₁ ∘ ! (ap (S¹-rec T.base T.loop₂) loop)) 
                                (βloop/rec T.base T.loop₂)〉
                 T.loop₂ ∘ T.loop₁ ∘ ! (ap (S¹-rec T.base T.loop₂) loop) 
                       ≃〈 ap (λ x → T.loop₂ ∘ T.loop₁ ∘ ! x) 
                                (βloop/rec T.base T.loop₂) 〉
                 T.loop₂ ∘ T.loop₁ ∘ ! T.loop₂   ≃〈 ∘-assoc T.loop₂ T.loop₁ (! T.loop₂) 〉
                 (T.loop₂ ∘ T.loop₁) ∘ ! T.loop₂ ≃〈 ap (λ x → x ∘ ! T.loop₂) (! T.f) 〉
                 (T.loop₁ ∘ T.loop₂) ∘ ! T.loop₂ ≃〈 ! (∘-assoc T.loop₁ T.loop₂ (! T.loop₂)) 〉
                 T.loop₁ ∘ T.loop₂ ∘ ! T.loop₂   ≃〈 ap (λ x → T.loop₁ ∘ x) (!-inv-r T.loop₂) 〉
                 T.loop₁ ∘ id               ≃〈 ∘-unit-r T.loop₁ 〉 (T.loop₁ ∎)))


  -- Mapping from Two Circles to Torus
  circles-to-torus' : S¹ -> S¹ -> T
  circles-to-torus' = 
    S¹-rec 
      (S¹-rec T.base T.loop₂)
      (λ≃ circles-fst-loop)

  -- The uncurried version of the above
  circles-to-torus : S¹ × S¹ -> T
  circles-to-torus = uncurry circles-to-torus' 

  -- Lemmas for proving the torus identity
  transport-loop₁ : transport (λ t' → circles-to-torus (torus-to-circles t') ≃ t') T.loop₁ id ≃ id
  transport-loop₁ = 
    transport (λ t' → circles-to-torus (torus-to-circles t') ≃ t') T.loop₁ id
          ≃〈 transport-Path (λ t' → circles-to-torus (torus-to-circles t')) 
                            (λ x → x) 
                            T.loop₁ 
                            id 〉
    ap (λ x → x) T.loop₁ ∘ id ∘ ! (ap (λ t' → circles-to-torus (torus-to-circles t')) T.loop₁)
          ≃〈 ap (λ y → ap (λ x → x) T.loop₁ ∘ y) 
                   (∘-unit-l (! (ap (λ t' → circles-to-torus (torus-to-circles t')) T.loop₁))) 〉
    ap (λ x → x) T.loop₁ ∘ ! (ap (λ t' → circles-to-torus (torus-to-circles t')) T.loop₁)
          ≃〈 ap (λ y → y ∘ ! (ap (λ t' → circles-to-torus (torus-to-circles t')) T.loop₁)) 
                   (ap-id T.loop₁) 〉
    T.loop₁ ∘ ! (ap (λ t' → circles-to-torus (torus-to-circles t')) T.loop₁)
          ≃〈 ap (λ y → T.loop₁ ∘ ! y) 
                   (ap-o circles-to-torus torus-to-circles T.loop₁) 〉
    T.loop₁ ∘ ! (ap circles-to-torus (ap torus-to-circles T.loop₁)) 
          ≃〈 ap (λ x → T.loop₁ ∘ ! (ap circles-to-torus x)) 
                   (T.βloop₁/rec (S¹.base , S¹.base) 
                               (pair×≃ loop id) 
                               (pair×≃ id loop) S¹-f) 〉
    T.loop₁ ∘ ! (ap circles-to-torus (pair×≃ loop (id{_}{S¹.base})))
       ≃〈 ap (λ x → T.loop₁ ∘ ! x) (ap-uncurry circles-to-torus' loop (id{_}{S¹.base})) 〉 
    T.loop₁ ∘ ! (ap2 circles-to-torus' loop (id{_}{S¹.base})) 
          ≃〈 ap (λ x → T.loop₁ ∘ ! x) (ap2-aps-1 circles-to-torus' loop (id{_}{S¹.base})) 〉 
    T.loop₁ ∘ ! (ap (\ x -> circles-to-torus' x S¹.base) loop 
             ∘ ap (circles-to-torus' S¹.base) (id{_}{S¹.base})) ≃〈 id 〉 
    T.loop₁ ∘ ! (ap (\ x -> circles-to-torus' x S¹.base) loop 
             ∘ id) 
          ≃〈 ap (λ x → T.loop₁ ∘ ! x) 
                   (∘-unit-r (ap (λ x → circles-to-torus' x S¹.base) loop)) 〉 
    T.loop₁ ∘ ! (ap (\ x -> (circles-to-torus' x) S¹.base) loop) 
          ≃〈 ap (\ x -> T.loop₁ ∘ ! x) 
                   (ap-app-1-nd (circles-to-torus') loop S¹.base) 〉 
    T.loop₁ ∘ ! (ap≃ (ap circles-to-torus' loop) {S¹.base}) 
          ≃〈 ap (λ x → T.loop₁ ∘ ! (ap≃ x {S¹.base})) 
                   (βloop/rec (S¹-rec T.base T.loop₂) 
                              (λ≃ circles-fst-loop)) 〉
    T.loop₁ ∘ ! (ap≃ (λ≃ circles-fst-loop) {S¹.base}) 
          ≃〈 ap (λ x → T.loop₁ ∘ ! x) 
                   (Π≃β circles-fst-loop {S¹.base}) 〉
    T.loop₁ ∘ ! (circles-fst-loop S¹.base) ≃〈 id 〉
    T.loop₁ ∘ ! T.loop₁ ≃〈 !-inv-r T.loop₁ 〉
    (id{_}{T.base}) ∎

  transport-loop₂ : transport (λ t' → circles-to-torus (torus-to-circles t') ≃ t') T.loop₂ id ≃ id
  transport-loop₂ =
    transport (λ t' → circles-to-torus (torus-to-circles t') ≃ t') T.loop₂ id
          ≃〈 transport-Path (λ t' → circles-to-torus (torus-to-circles t')) 
                       (λ x → x) 
                       T.loop₂ 
                       id 〉
    ap (λ x → x) T.loop₂ ∘ id ∘ ! (ap (λ t' → circles-to-torus (torus-to-circles t')) T.loop₂)
          ≃〈 ap (λ y → ap (λ x → x) T.loop₂ ∘ y) 
                   (∘-unit-l (! (ap (λ t' → circles-to-torus (torus-to-circles t')) T.loop₂))) 〉 
    ap (λ x → x) T.loop₂ ∘ ! (ap (λ t' → circles-to-torus (torus-to-circles t')) T.loop₂)
          ≃〈 ap
                (λ y → y ∘ ! (ap (λ t' → circles-to-torus (torus-to-circles t')) T.loop₂))
                (ap-id T.loop₂) 〉
    T.loop₂ ∘ ! (ap (λ t' → circles-to-torus (torus-to-circles t')) T.loop₂)
          ≃〈 ap (λ y → T.loop₂ ∘ ! y)
                   (ap-o circles-to-torus 
                           torus-to-circles 
                           T.loop₂) 〉 
    T.loop₂ ∘ ! (ap circles-to-torus (ap torus-to-circles T.loop₂)) 
          ≃〈 ap (λ x → T.loop₂ ∘ ! (ap circles-to-torus x)) 
                   (T.βloop₂/rec (S¹.base , S¹.base) 
                               (pair×≃ loop id) 
                               (pair×≃ id loop) 
                               S¹-f) 〉
    T.loop₂ ∘ ! (ap circles-to-torus (pair×≃ (id{_}{S¹.base}) loop)) 
          ≃〈 ap (λ x → T.loop₂ ∘ ! x) 
                   (ap-uncurry circles-to-torus' (id{_}{S¹.base}) loop) 〉
    T.loop₂ ∘ ! (ap2 circles-to-torus' (id{_}{S¹.base}) loop) 
          ≃〈 ap (λ x → T.loop₂ ∘ ! x) 
                   (ap2-aps-2 circles-to-torus' (id{_}{S¹.base}) loop) 〉
    T.loop₂ ∘ ! (ap (circles-to-torus' S¹.base) loop ∘ 
               ap (λ x → circles-to-torus' x S¹.base) (id{_}{S¹.base})) ≃〈 id 〉
    T.loop₂ ∘ ! (ap (circles-to-torus' S¹.base) loop) ≃〈 id 〉
    T.loop₂ ∘ ! (ap (S¹-rec T.base T.loop₂) loop) 
          ≃〈 ap (λ x → T.loop₂ ∘ ! x) 
                   (βloop/rec T.base T.loop₂) 〉
    T.loop₂ ∘ ! T.loop₂ ≃〈 !-inv-r T.loop₂ 〉
    id{_}{T.base} ∎
    
  transport-loops-commute : T.CommutatorDep {(λ t' → circles-to-torus (torus-to-circles t') ≃ t')}
                                            id transport-loop₁ transport-loop₂
  transport-loops-commute = 
                  -- transport (λ x → transport C x a' ≃ a') f 
                  --           (p' ∘ (ap (transport C loop₁) q') ∘ ap≃ (transport-∘ C loop₁ loop₂)) 
                  --   ≃ q' ∘ (ap (transport C loop₂) p') ∘ ap≃ (transport-∘ C loop₂ loop₁)
    transport
      (λ x →
         transport (λ t' → circles-to-torus (torus-to-circles t') ≃ t') x id ≃
         id)
      T.f
      (transport-loop₁ ∘
       ap
       (transport (λ t' → circles-to-torus (torus-to-circles t') ≃ t') T.loop₁)
       transport-loop₂
       ∘
       ap≃
       (transport-∘ (λ t' → circles-to-torus (torus-to-circles t') ≃ t') T.loop₁ T.loop₂))
      ≃〈 {!!} 〉 
     (transport-loop₂ ∘
        ap (transport (λ t' → circles-to-torus (torus-to-circles t') ≃ t') T.loop₂) transport-loop₁
        ∘
        ap≃ (transport-∘ (λ t' → circles-to-torus (torus-to-circles t') ≃ t') T.loop₂ T.loop₁)) ∎

  torus-circles-torus : (t : T) -> (circles-to-torus (torus-to-circles t)) ≃ t
  torus-circles-torus = T-elim {λ t' → circles-to-torus (torus-to-circles t') ≃ t'} 
                               id
                               transport-loop₁ 
                               transport-loop₂
                               {!!} --transport-loops-commute

  