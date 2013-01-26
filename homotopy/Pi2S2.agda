

{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open import homotopy.Hopf
import homotopy.Pi1S1
import homotopy.Pi2S2-retract
open import homotopy.Pi2S2-encdec
open import homotopy.Pi2S2-inverses
open Paths
open Int

module homotopy.Pi2S2 where

  open Truncation

  private 
    module S² = S²1
  open S² using (S² ; S²-rec ; S²-elim)
  open S¹ using (S¹ ; S¹-rec ; S¹-elim)

  τ₁Ω[S²]-is-S¹ : Path (τ₁ (Path{S²} S².base S².base)) S¹
  τ₁Ω[S²]-is-S¹ = ua (improve (hequiv encode decode' decode-encode encode-decode'))

  π₂S²-is-Z : Path (τ₀ (Path{Path{S²} S².base S².base} id id)) Int
  π₂S²-is-Z = (τ₀ (Path{Path{S²} S².base S².base} id id))                     ≃〈 ua (improve (hequiv TruncPath.decode' TruncPath.encode' (λ _ → ap≃ TruncPath.encode-decode') (λ _ → ap≃ TruncPath.decode-encode'))) 〉 
              Path{τ₁ (Path{S²} S².base S².base)} [ id ] [ id ]               ≃〈 Path-equiv τ₁Ω[S²]-is-S¹ {[ id ]} {[ id ]} 〉
              Path{S¹} (coe τ₁Ω[S²]-is-S¹ [ id ]) (coe τ₁Ω[S²]-is-S¹  [ id ]) ≃〈 ap (λ x → Path {S¹} x x) (ap≃ (type≃β _)) 〉 
              Path{S¹} S¹.base S¹.base                                       ≃〈 ua (improve homotopy.Pi1S1.Ω₁[S¹]-is-Int) 〉 
              Int ∎
