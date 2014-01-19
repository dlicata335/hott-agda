{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open Truncation
open Int
open LoopSpace
open Suspension
open import homotopy.Freudenthal
open import homotopy.HStructure
open import homotopy.PiLessOfConnected
open import homotopy.Pi2HSusp
open import homotopy.KG1

-- stability consequences of Freudenthal for iterated suspensions
-- starting with a 1-type

module homotopy.FreudenthalIteratedSuspension1 (A : Type) 
                                               (a0 : A)
                                               (A-Connected : Connected (S (S -2)) A)
                                               where

      Susp'^ : Positive → Type
      Susp'^ n = (Susp^ (n -1pn) A)
  
      Susp'^-Connected : ∀ (i : Nat) → Connected (tl i) (Susp'^ (i +1np))
      Susp'^-Connected n = transport
                        (λ x → NType -2 (Trunc (tl n) (Susp^ x A)))
                        (! (+1-1-cancel n)) (Susp^-Connected0 n A-Connected)
  
      Susp'^-Connected' : (n : Positive) → Connected (S (-2ptl n)) (Susp'^ n)
      Susp'^-Connected' One = Susp'^-Connected 0
      Susp'^-Connected' (S One) = Susp'^-Connected 1
      Susp'^-Connected' (S (S n')) = coe (ap (λ x → NType -2 (Trunc (S (tl (pos2nat n'))) (Susp^ x A))) (ap pos2nat (pos2nat-+1np n')))
                                     (Susp'^-Connected (pos2nat (S n'))) 
  

      Susp'^-Connected'' : (n : Positive) → Connected (tlp n) (Susp'^ (n +1))
      Susp'^-Connected'' n = coe (ap (λ x → NType -2 (Trunc x (Susp^ (pos2nat n) A))) (tl-pos2nat-tlp n ∘ ! (-2ptl-S (S n)))) 
                          (Susp'^-Connected' (n +1))
  
      base'^ : ∀ n → Susp'^ n
      base'^ n = point^ (n -1pn) a0

      module Stable (k : Positive)
                    (n : Positive) 
                    (c : (tlp k <=tl 2* n -2))
           where
  
       module F = FreudenthalEquiv (-2ptl n) (tlp k) (-2<pos-2 n) c (Susp'^ n) (base'^ n) (Susp'^-Connected' n) 
       -- F.path : (Trunc (tlp k) (B n)) ≃
       --          (Trunc (tlp k) (Path {Susp (B n)} (No {B n}) (No {B n})))
       
       stable : π k (Susp'^ n) (base'^ n) ≃ π (k +1) (Susp'^ (n +1)) (base'^ (n +1))
       stable = ! (π (k +1) (Susp'^ (n +1)) (base'^ (n +1)) ≃〈 id 〉
                   τ₀ (Loop (k +1) (Susp'^ (n +1)) (base'^ (n +1)))                                    ≃〈 ap τ₀ (LoopSpace.LoopPath.path k) 〉
                   τ₀ (Loop k (Path {(Susp'^ (n +1))} (base'^ (n +1)) (base'^ (n +1))) id)             ≃〈 ! (LoopSpace.Loop-Trunc0 k) 〉
                   Loop k (Trunc (tlp k) (Loop One (Susp'^ (n +1)) (base'^ (n +1)))) [ id ]           ≃〈 id 〉
                   Loop k (Trunc (tlp k) (Loop One (Susp^ (pos2nat n) A) (base'^ (n +1)))) [ id ] ≃〈 ap-Loop≃ k (ap (Trunc (tlp k)) (ap-Loop≃ One (ap (λ x → Susp^ x A) (pos2nat-is-S n)) (transport-Susp^-number (pos2nat-is-S n) a0 ∘ ! (ap≃ (transport-ap-assoc (λ x → Susp^ x A) (pos2nat-is-S n)))))) ((ap [_] (ap-Loop≃-id One (ap (λ x → Susp^ x A) (pos2nat-is-S n)) (transport-Susp^-number (pos2nat-is-S n) a0 ∘ ! (ap≃ (transport-ap-assoc (λ x → Susp^ x A) (pos2nat-is-S n))))) ∘ ap≃ (transport-Trunc {tlp k} (λ A' → A') (ap-Loop≃ One (ap (λ x → Susp^ x A) (pos2nat-is-S n)) (transport-Susp^-number (pos2nat-is-S n) a0 ∘ ! (ap≃ (transport-ap-assoc (λ x → Susp^ x A) (pos2nat-is-S n)))))) {[ id ]}) ∘ ap≃ (! (transport-ap-assoc (Trunc (tlp k)) (ap-Loop≃ One (ap (λ x → Susp^ x A) (pos2nat-is-S n)) (transport-Susp^-number (pos2nat-is-S n) a0 ∘ ! (ap≃ (transport-ap-assoc (λ x → Susp^ x A) (pos2nat-is-S n))))))){[ id ]}) 〉
                   Loop k (Trunc (tlp k) (Loop One (Susp (Susp'^ n)) No)) [ id ]                      ≃〈 ap-Loop≃ k (! F.path) (ap≃ (type≃β! F.eqv)) 〉 
                   Loop k (Trunc (tlp k) (Susp'^ n)) [ base'^ n ]                                     ≃〈 Loop-Trunc0 k 〉
                   τ₀ (Loop k (Susp'^ n) (base'^ n)) ≃〈 id 〉 
                   π k (Susp'^ n) (base'^ n) ∎)

