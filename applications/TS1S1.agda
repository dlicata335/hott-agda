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
      (λ≃ {!!})
      
      
      
