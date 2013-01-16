{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open import homotopy.HigherHomotopyAbelian 
open Paths

module homotopy.Hopf where

  module S² = S²1
  open S²1

  module A1 = homotopy.HigherHomotopyAbelian S² base

  module Four where
    ichange : Path {Path {Path base base} id id}
                (ap∘ (loop ∘ loop) (loop ∘ loop))
                (ap∘ loop loop ∘ ap∘ loop loop)
    ichange = ichange-type loop loop loop loop

    loop4 = ((loop ∘ loop) ∘ (loop ∘ loop))
  
    nontriv-loop4 : loop4 ≃ loop4
    nontriv-loop4 = loop4 ≃〈 A1.same (loop ∘ loop) (loop ∘ loop) 〉
                    ap∘ (loop ∘ loop) (loop ∘ loop) ≃〈 ichange 〉 
                    ap∘ loop loop ∘ ap∘ loop loop ≃〈 ap2 _∘_ (! (A1.same loop loop)) (! (A1.same loop loop))  〉
                    loop4 ∎

  ap∘-inv-r : (a : id{_}{base} ≃ id{_}{base})
                -> ap∘ a (! a) ≃ id 
  ap∘-inv-r a = !-inv-r a ∘ ! (A1.same a (! a))

  ap∘-inv-l : (a : id{_}{base} ≃ id{_}{base})
                -> ap∘ (! a) a ≃ id 
  ap∘-inv-l a = !-inv-l a ∘ ! (A1.same (! a) a)

  nontriv : Path {Path {Path base base} id id} id id
  nontriv = id ≃〈 ! (ap2 ap∘ (!-inv-r loop) (!-inv-r loop)) 〉
            ap∘ (loop ∘ ! loop) (loop ∘ ! loop) ≃〈 ichange-type (! loop) loop (! loop) loop 〉 
            ap∘ loop loop ∘ ap∘ (! loop) (! loop) ≃〈 ! (ap2 (λ x y → x ∘ y) (A1.same loop loop) (A1.same (! loop) (! loop))) 〉 
            (loop ∘ loop) ∘ ! loop ∘ ! loop ≃〈 ap (λ x → (loop ∘ loop) ∘ x) (! (!-∘ loop loop)) 〉 
            (loop ∘ loop) ∘ ! (loop ∘ loop) ≃〈 !-inv-r (loop ∘ loop) 〉 
            (id ∎)

  module S³ = S³1
  open S³ using (S³)

  hopf-map : S³ -> S²
  hopf-map = S³.S³-rec S².base nontriv
  