{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
import homotopy.FreudenthalIteratedSuspension1
open import homotopy.Pi1S1
open import homotopy.HStructure
open import homotopy.Pi2HSusp
open import homotopy.PiLessOfConnected
open Int
open Truncation
open LoopSpace
open Suspension

module homotopy.PiSNSusp where

  open NSphereSusp

  H-S¹ : H-Structure S¹.S¹ S¹.base
  H-S¹ = record { _⊙_ = mult;
                  unitl = λ _ → id;
                  unitr = S¹.S¹-elim _ id ((((!-inv-r S¹.loop ∘ ap (λ x → S¹.loop ∘ ! x) red) ∘
                                               ap (λ x → x ∘ ! (ap (λ z → mult z S¹.base) S¹.loop))
                                               (ap-id S¹.loop)) ∘
                                              ap (λ x → ap (λ x' → x') S¹.loop ∘ x)
                                              (∘-unit-l (! (ap (λ z → mult z S¹.base) S¹.loop)))) ∘ transport-Path (λ z → mult z S¹.base) (λ z → z) S¹.loop id);
                  unitcoh = id;
                  isequivl = S¹.S¹-elim _ (snd id-equiv) (HProp-unique (IsEquiv-HProp (λ x → x)) _ _) } where
    mutual
     mult : S¹.S¹ -> S¹.S¹ -> S¹.S¹
     mult = S¹.S¹-rec (λ x → x) mult-loop

     mult-hom = (S¹.S¹-elim _ S¹.loop ((!-inv-r-back S¹.loop S¹.loop ∘ ap (λ x → x ∘ S¹.loop ∘ ! x) (ap-id S¹.loop)) ∘ transport-Path (λ x → x) (λ x → x) S¹.loop S¹.loop))

     mult-loop = (λ≃ mult-hom)

    red : (ap (λ z → mult z S¹.base) S¹.loop) ≃ S¹.loop
    red = ((Π≃β mult-hom {S¹.base}) ∘ ap (λ x → ap≃ x {S¹.base}) (S¹.βloop/rec (\ x -> x) (mult-loop))) ∘ ap-o (λ f → f S¹.base) mult S¹.loop


  module SS = homotopy.FreudenthalIteratedSuspension1 (S¹.S¹) S¹.base (S^-Connected 0) S¹-is-Gpd H-S¹

  π1[Sn+1] : (n : Positive) -> π One (S^ (n +1)) (base^ (n +1)) ≃ Unit
  π1[Sn+1] n = π1Connected≃Unit (tlp n) (S^ (S n)) (base^ (S n)) (SS.Susp'^-Connected'' n) (1<=pos n)

  πk[Sn]-less : ∀ k n → tlp k <tl tlp n → π k (S^ n) (base^ n) ≃ Unit
  πk[Sn]-less One One (ltSR (ltSR (ltSR ())))
  πk[Sn]-less One (S n) lt = π1[Sn+1] n
  πk[Sn]-less (S k) One lt with pos-not-<=0 k (Inl (lt-unS lt))
  ... | () 
  πk[Sn]-less (S k) (S n) lt = π (k +1) (S^ (n +1)) (base^ (n +1)) ≃〈 ! (SS.Stable.stable k n (k<=n->k<=2n-2 k n (Inl (lt-unS lt)))) 〉
                               π k (S^ n) (base^ n) ≃〈 πk[Sn]-less k n (lt-unS lt) 〉
                               Unit ∎ 

  πn[Sn]-is-Int : ∀ n → π n (S^ n) (base^ n) ≃ Int
  πn[Sn]-is-Int One = π₁[S¹]-is-Int
  πn[Sn]-is-Int (S One) = π₁[S¹]-is-Int ∘ π2Susp S¹.S¹ S¹.base S¹-is-Gpd (S^-Connected 0) H-S¹ 
  πn[Sn]-is-Int (S (S n)) = πn[Sn]-is-Int (S n) ∘ ! (SS.Stable.stable (S n) (S n) (k<=n->k<=2n-2 (S n) (S n) (Inr (id , >pos->1 n (S n) ltS))))

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
