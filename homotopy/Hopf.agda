{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open import homotopy.HigherHomotopyAbelian 
open import homotopy.Pi1S1 
open Paths

module homotopy.Hopf where

  private 
    module S² = S²1

  open S²1
  open S¹ using (S¹ ; S¹-elim)

  S¹-loops : (x : S¹) → x ≃ x
  S¹-loops = 
      (S¹-elim (λ x → Path x x) 
                  S¹.loop 
                  ((ap (λ x → x) S¹.loop ∘ S¹.loop ∘ ! (ap (λ x → x) S¹.loop) ≃〈 ap (λ y → y ∘ S¹.loop ∘ ! (ap (λ x → x) S¹.loop)) (ap-id S¹.loop) 〉
                   (S¹.loop ∘ S¹.loop ∘ ! (ap (λ x → x) S¹.loop)) ≃〈 ap (λ y → S¹.loop ∘ S¹.loop ∘ ! y) (ap-id S¹.loop) 〉 
                   (S¹.loop ∘ S¹.loop ∘ ! S¹.loop) ≃〈 ap (λ x → S¹.loop ∘ x) (!-inv-r S¹.loop) 〉 
                   S¹.loop ∎)
                   ∘ transport-Path (λ x → x) (λ x → x) S¹.loop S¹.loop))

  H : S² → Type
  H = S²-fibration S¹ S¹-loops

  S¹-is-Gpd : HGpd S¹
  S¹-is-Gpd = istrunc hset-path where
    hset-path : (x y : _) → HSet (Path{S¹} x y)
    hset-path x y = transport HSet (! (ua (improve Path-S¹-is-Int))) Int.HSet-Int

  H-is-1-truncated : (x : S²) → HGpd (H x)
  H-is-1-truncated = S²-elim (λ x → HGpd (H x)) S¹-is-Gpd
                             (fst (use-trunc (use-trunc (IsTrunc-Path { -1 } _ (IsTrunc-is-HProp {tl 1} S¹) _ _) _ _)))

  module A = homotopy.HigherHomotopyAbelian S² S².base

  module Four where
    ichange : Path {Path {Path base base} id id}
                (ap∘ (loop ∘ loop) (loop ∘ loop))
                (ap∘ loop loop ∘ ap∘ loop loop)
    ichange = ichange-type loop loop loop loop
  
    loop4 = ((loop ∘ loop) ∘ (loop ∘ loop))
  
    nontriv-loop4 : loop4 ≃ loop4
    nontriv-loop4 = loop4 ≃〈 A.same (loop ∘ loop) (loop ∘ loop) 〉
                    ap∘ (loop ∘ loop) (loop ∘ loop) ≃〈 ichange 〉 
                    ap∘ loop loop ∘ ap∘ loop loop ≃〈 ap∘ (! (A.same loop loop)) (! (A.same loop loop))  〉
                    loop4 ∎
  
  hopf-cell : Path {Path {Path{S²} base base} id id} id id
  hopf-cell = id ≃〈 ! (ap2 ap∘ (!-inv-r loop) (!-inv-r loop)) 〉
              ap∘ (loop ∘ ! loop) (loop ∘ ! loop) ≃〈 ichange-type (! loop) loop (! loop) loop 〉 
              ap∘ loop loop ∘ ap∘ (! loop) (! loop) ≃〈 ! (ap2 (λ x y → x ∘ y) (A.same loop loop) (A.same (! loop) (! loop))) 〉 
              (loop ∘ loop) ∘ ! loop ∘ ! loop ≃〈 ap (λ x → (loop ∘ loop) ∘ x) (! (!-∘ loop loop)) 〉 
              (loop ∘ loop) ∘ ! (loop ∘ loop) ≃〈 !-inv-r (loop ∘ loop) 〉 
              (id ∎)

  module S³ = S³1
  open S³ using (S³)

  hopf-map : S³ -> S²
  hopf-map = S³.S³-rec S².base hopf-cell
  