{-# OPTIONS --type-in-type #-}

open import lib.Prelude
open import homotopy.KGn
open import homotopy.Pi1S1
open import homotopy.HStructure
open import homotopy.Pi2HSusp
open import homotopy.PiLessOfConnected
open Int
open Truncation
open LoopSpace
open Suspension

module homotopy.PiNSNSusp where

  open NSphereSusp

  module BS = B (S¹.S¹) S¹.base (S^-Connected 0) S¹-is-Gpd H-S¹

  π1[Sn] : ∀ n -> tl 1 <tl tlp n -> π One (S^ n) (base^ n) ≃ Unit
  π1[Sn] One (ltSR (ltSR (ltSR ()))) 
  π1[Sn] (S n) lt = π1Connected≃Unit (tlp (S n)) (S^ (S n)) (base^ (S n)) {!S^-Connected (pos2nat n)!} (Inl (>pos->1 n (S n) ltS))

  πk[Sn]-less : ∀ k n → tlp k <tl tlp n → π k (S^ n) (base^ n) ≃ Unit
  πk[Sn]-less = {!!}

  πn[Sn]-is-Int : ∀ n → π n (S^ n) (base^ n) ≃ Int
  πn[Sn]-is-Int One = π₁[S¹]-is-Int
  πn[Sn]-is-Int (S One) = {!homotopy.Pi2HSusp.path S¹.S¹ S¹.base S¹-is-Gpd (S^-Connected 0) H-S¹ !} -- need to fix pi2: unnecessary truncation?
  πn[Sn]-is-Int (S (S n)) = πn[Sn]-is-Int (S n) ∘ ! (BS.Untruncated.Stable.stable (S n) (S n) (n<=2*n-2 (S n) (>pos->1 n (S n) ltS)))

    -- consequences of stablity for k <= 2n - 2 
    -- n = 1: k <= 0
    -- n = 2: k <= 2 : pi_1(S^2) = pi_2(S^3) and pi_2(S^2) = pi_3(S^3) 
    -- n = 3: k <= 4 : pi_1(S^3) = pi_2(S^4) and pi_2(S^3) = pi_3(S^4) and pi_3(S^3) = pi_4(s^4) and pi_4(S^3) = pi_5(S^4)
    -- n = 4: k <= 6 : pi_1(S^4) = pi_2(S^5) and pi_2(S^4) = pi_3(S^5) and pi_3(S^4) = pi_4(s^5) and pi_4(S^4) = pi_5(s^5) and pi_5(S^4) = pi_6(s^5) and pi_6(S^4) = pi_7(S^5)
    
    -- so: 
    -- k<n : pi_1(S^2) = pi_2(S^3) = pi_3(S^4) = pi_4(s^5) = ...
    --       pi_1(S^3) = pi_2(S^4) = pi_3(S^5) = ...
    --       pi_1(S^4) = pi_2(S^5) 
    -- k=n : pi_2(S^2) = pi_3(S^3) = pi_4(s^4) = pi_5(s^5) = ...
    -- k>n : pi_4(S^3) = pi_5(S^4) = pi_6(s^5) = ... 
    --       pi_6(S^4) = pi_7(S^5)

    -- to start the diagonals, can prove:
    -- pi_1(S^2)
    -- pi_1(S^3)
    -- pi_1(S^4)
    -- pi_2(S^2)
    -- pi_4(S^3)
    -- pi_6(S^4)
