{-# OPTIONS --type-in-type #-}

open import lib.Prelude
open import homotopy.Freudenthal
open Int
open Truncation
open LoopSpace
open Suspension

module homotopy.PiNSNSusp where

  module StableSphere (n : Positive) (k : Positive) 
                      (c : (tlp k <=tl plus2 (-2ptl n) (-2ptl n)))
                      -- i.e. k <= 2n - 2 
         where

    open NSphereSusp

    nS^ : ∀ n → Connected (S (-2ptl n)) (S^ n)
    nS^ One = S^-Connected 0
    nS^ (S One) = S^-Connected 1
    nS^ (S (S n')) = FIXME where -- {!S^-Connected (pos2nat (S n'))!} -- right where
                           postulate FIXME : _
      -- transport (λ x → Connected (S (tl (pos2nat n'))) (Susp (S^ x))) 
      --                         (pos2nat-+1np n')
      --                         {!(S^-Connected (pos2nat (S n')))!}

    module F = FreudenthalEquiv (-2ptl n) (tlp k) (-2<pos-2 n) c (S^ n) (base^ n) (nS^ n) 

    stable : π k (S^ n) (base^ n) ≃ π (k +1) (S^ (n +1)) (base^ (n +1))
    stable = ! (π (k +1) (S^ (n +1)) (base^ (n +1)) ≃〈 id 〉
                τ₀ (Loop (k +1) (S^ (n +1)) (base^ (n +1))) ≃〈 ap τ₀ (LoopSpace.LoopPath.path k) 〉
                τ₀ (Loop k (Path {(S^ (n +1))} (base^ (n +1)) (base^ (n +1))) id) ≃〈 ! (LoopSpace.Loop-Trunc0 k) 〉
                Loop k (Trunc (tlp k) (Path {(S^ (n +1))} (base^ (n +1)) (base^ (n +1)))) [ id ] ≃〈 id 〉
                Loop k (Trunc (tlp k) (Path {Susp^ (pos2nat n) S¹.S¹} (base^ (n +1)) (base^ (n +1)))) [ id ] ≃〈 FIXME 〉
                Loop k (Trunc (tlp k) (Path {Susp^ (S (n -1pn)) S¹.S¹} No No)) [ id ] ≃〈 ap-Loop≃ k (! F.path) (ap≃ (type≃β! F.eqv)) 〉
                Loop k (Trunc (tlp k) (S^ n)) [ base^ n ] ≃〈 LoopSpace.Loop-Trunc0 k 〉 
                τ₀ (Loop k (S^ n) (base^ n)) ≃〈 id 〉 
                π k (S^ n) (base^ n) ∎) where
        postulate FIXME : _

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
