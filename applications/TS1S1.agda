{-# OPTIONS --type-in-type --without-K #-}
open import lib.Prelude
open Paths
open S¹
open T
open NonDep

module applications.TS1S1 where
       
  torus-to-circles : T -> S¹ × S¹
  torus-to-circles = T-rec a' p' q' f'
    where a' = S¹.base , S¹.base
          p' = nondep-pair≃ loop Refl
          q' = nondep-pair≃ Refl loop
          f' = 
            nondep-pair≃ loop Refl ∘ nondep-pair≃ Refl loop ≃〈 ∘-× loop Refl Refl loop 〉 
            nondep-pair≃ (loop ∘ Refl) (Refl ∘ loop)      ≃〈 resp (λ x → nondep-pair≃ x (Refl ∘ loop)) (∘-unit-r loop) 〉 
            nondep-pair≃ loop (Refl ∘ loop)               ≃〈 resp (λ x → nondep-pair≃ loop x) (∘-unit-l loop) 〉 
            nondep-pair≃ loop loop                        ≃〈 resp (λ x → nondep-pair≃ x loop) (sym (∘-unit-l loop)) 〉 
            nondep-pair≃ (Refl ∘ loop) loop               ≃〈 resp (λ x → nondep-pair≃ (Refl ∘ loop) x) (sym (∘-unit-r loop)) 〉 
            nondep-pair≃ (Refl ∘ loop) (loop ∘ Refl)      ≃〈 sym (∘-× Refl loop loop Refl) 〉 
            nondep-pair≃ Refl loop ∘ nondep-pair≃ loop Refl ∎

  circles-to-torus : S¹ -> S¹ -> T
  circles-to-torus = 
    S¹-rec 
      (S¹-rec T.base loop₂)
      (λ≃ (S¹-elim {λ x → S¹-rec T.base loop₂ x ≃ S¹-rec T.base loop₂ x} 
                   loop₁
                   (subst (λ x → S¹-rec T.base loop₂ x ≃ S¹-rec T.base loop₂ x) loop loop₁
                      ≃〈 subst-Id (S¹-rec T.base loop₂) (S¹-rec T.base loop₂) 
                                   loop loop₁ 〉 

                    resp (S¹-rec T.base loop₂) loop ∘ loop₁ ∘ ! (resp (S¹-rec T.base loop₂) loop)
                      ≃〈 resp (λ x → x ∘ loop₁ ∘ ! (resp (S¹-rec T.base loop₂) loop)) 
                               (βloop/rec T.base loop₂) 〉 

                    loop₂ ∘ loop₁ ∘ ! (resp (S¹-rec T.base loop₂) loop) 
                      ≃〈 resp (λ x → loop₂ ∘ loop₁ ∘ ! x) (βloop/rec T.base loop₂) 〉
  
                    loop₂ ∘ loop₁ ∘ ! loop₂   ≃〈 ∘-assoc loop₂ loop₁ (! loop₂) 〉
                    (loop₂ ∘ loop₁) ∘ ! loop₂ ≃〈 resp (λ x → x ∘ ! loop₂) (sym f) 〉
                    (loop₁ ∘ loop₂) ∘ ! loop₂ ≃〈 sym (∘-assoc loop₁ loop₂ (! loop₂)) 〉 
                    loop₁ ∘ loop₂ ∘ ! loop₂   ≃〈 resp (λ x → loop₁ ∘ x) (!-inv-r loop₂) 〉
                    loop₁ ∘ Refl              ≃〈 ∘-unit-r loop₁ 〉 
                    loop₁ ∎)))
             