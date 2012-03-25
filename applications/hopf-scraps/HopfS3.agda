-- accidentally did the Hopf thing for S3:
-- characterize π4(S3) ?

{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open import applications.HigherHomotopyAbelian 
open Paths

module applications.hopf-scraps.HopfS3 where

  open S³1

  module A1 = applications.HigherHomotopyAbelian S³ base
  module A2 = applications.HigherHomotopyAbelian (base ≃ base) Refl

  module S² = S²1
  open S² using (S²)
  
  module Four where
    ichange : Id{Id {Id {Id base base} Refl Refl} Refl Refl} 
               (resp∘ (loop ∘ loop) (loop ∘ loop)) 
               (resp∘ loop loop ∘ resp∘ loop loop)
    ichange = ichange-type loop loop loop loop
  
    loop4 = ((loop ∘ loop) ∘ (loop ∘ loop))
  
    nontriv-loop4 : loop4 ≃ loop4
    nontriv-loop4 = loop4 ≃〈 A2.same (loop ∘ loop) (loop ∘ loop) 〉
                    resp∘ (loop ∘ loop) (loop ∘ loop) ≃〈 ichange 〉 
                    resp∘ loop loop ∘ resp∘ loop loop ≃〈 resp2 _∘_ (! (A2.same loop loop)) (! (A2.same loop loop))  〉
                    loop4 ∎

  resp∘-inv-r : (a : Refl{_}{base} ≃ Refl{_}{base})
                -> resp∘ a (! a) ≃ Refl 
  resp∘-inv-r a = !-inv-r a ∘ ! (A1.same a (! a))

  resp∘-inv-l : (a : Refl{_}{base} ≃ Refl{_}{base})
                -> resp∘ (! a) a ≃ Refl 
  resp∘-inv-l a = !-inv-l a ∘ ! (A1.same (! a) a)

  nontriv : Id{Id {Id {Id base base} Refl Refl} Refl Refl} Refl Refl
  nontriv = Refl ≃〈 ! (resp2 resp∘ (!-inv-r loop) (!-inv-r loop)) 〉
            resp∘ (loop ∘ ! loop) (loop ∘ ! loop) ≃〈 ichange-type (! loop) loop (! loop) loop 〉 
            resp∘ loop loop ∘ resp∘ (! loop) (! loop) ≃〈 ! (resp2 (λ x y → x ∘ y) (A2.same loop loop) (A2.same (! loop) (! loop))) 〉 
            (loop ∘ loop) ∘ ! loop ∘ ! loop ≃〈 resp (λ x → (loop ∘ loop) ∘ x) (! (!-∘ loop loop)) 〉 
            (loop ∘ loop) ∘ ! (loop ∘ loop) ≃〈 !-inv-r (loop ∘ loop) 〉 
            (Refl ∎)
  
  hopf-map : S³ -> S²
  hopf-map = S³-rec S².base {!nontriv!}
  