{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open import homotopy.HigherHomotopyAbelian 
open import homotopy.Pi1S1 
open Paths

module homotopy.HopfTotal where
  open Truncation

  private 
    module S² = S²1
    module S³ = S³1
  open S³ using (S³ ; S³-rec)
  open S² using (S² ; S²-rec ; S²-elim)
  open S¹ using (S¹ ; S¹-rec ; S¹-elim)

  -- we know that H = (τ₁ o Path S².base)

  left : (Σ (τ₁ o Path S².base)) → S³
  left (x , p) = {!!}
  