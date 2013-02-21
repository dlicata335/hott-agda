
{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open Truncation
open Int
open LoopSpace
open Suspension
open import homotopy.Freudenthal

module homotopy.KGn where

  Abelian : Type -> Type
  Abelian A = (x : A) (p q : Path x x) → p ∘ q ≃ q ∘ p

  -- like K_G,1 for abelian G
  IsK1 : Type -> Type
  IsK1 A = A × 
           Connected (S (S -2)) A × 
           HGpd A ×
           Abelian A

  module B (A : Type) (isK1 : IsK1 A) where

    a0 : A
    a0 = fst isK1

    A-Connected : Connected (S (S -2)) A
    A-Connected = fst (snd isK1)

    -- Bn = KGn 
    B : Positive → Type
    B n = Trunc (tlp n) (Susp^ (n -1pn) A)

    B-Connected : ∀ (i : Nat) → Connected (tl i) (B (i +1np))
    B-Connected n = transport
                      (λ x → NType -2 (Trunc (tl n) (Trunc (tlp (n +1np)) (Susp^ x A))))
                      (! (+1-1-cancel n)) (connected-Trunc _ _ _ (Susp^-Connected0 n A-Connected))

    base^ : ∀ n → B n
    base^ n = [ point^ (n -1pn) a0 ]

    module Stable (n : Positive)
                  (k : Positive) 
                  (c : (tlp k <=tl plus2 (-2ptl n) (-2ptl n)))
                  -- i.e. k <= 2n - 2 
           where
  
      nB : ∀ n → Connected (S (-2ptl n)) (B n)
      nB One = B-Connected 0
      nB (S One) = B-Connected 1
      nB (S (S n')) = {!B-Connected (pos2nat (S n'))!} where -- {!S^-Connected (pos2nat (S n'))!} -- right where
                             postulate FIXME : _
        -- transport (λ x → Connected (S (tl (pos2nat n'))) (Susp (S^ x))) 
        --                         (pos2nat-+1np n')
        --                         {!(S^-Connected (pos2nat (S n')))!}
  
      module F = FreudenthalEquiv (-2ptl n) (tlp k) (-2<pos-2 n) c (B n) (base^ n) (nB n) 
  
      stable : π k (B n) (base^ n) ≃ π (k +1) (B (n +1)) (base^ (n +1))
      stable = ! (π (k +1) (B (n +1)) (base^ (n +1)) ≃〈 id 〉
                  τ₀ (Loop (k +1) (B (n +1)) (base^ (n +1))) ≃〈 ap τ₀ (LoopSpace.LoopPath.path k) 〉
                  τ₀ (Loop k (Path {(B (n +1))} (base^ (n +1)) (base^ (n +1))) id) ≃〈 ! (LoopSpace.Loop-Trunc0 k) 〉
                  Loop k (Trunc (tlp k) (Path {(B (n +1))} (base^ (n +1)) (base^ (n +1)))) [ id ] ≃〈 id 〉
                  Loop k (Trunc (tlp k) (Path {Trunc (tlp (n +1)) (Susp^ (pos2nat n) A)} (base^ (n +1)) (base^ (n +1)))) [ id ] ≃〈 {!!} 〉
                  Loop k (Trunc (tlp k) (Trunc (tlp n) (Path {(Susp^ (pos2nat n) A)} (point^ (pos2nat n) a0) (point^ (pos2nat n) a0)))) [ [ id ] ] ≃〈 {!unfold susp!} 〉
                  Loop k (Trunc (tlp k) (Trunc (tlp n) (Path {Susp (B n)} No No))) [ [ id ] ] ≃〈 {!swap !} 〉
                  Loop k (Trunc (tlp n) (Trunc (tlp k) (Path {Susp (B n)} No No))) [ [ id ] ] ≃〈 ap-Loop≃ k (ap (Trunc (tlp n)) (! F.path)) {!(! F.path)!} 〉
                  Loop k (Trunc (tlp n) (Trunc (tlp k) (B n))) [ [ base^ n ] ]  ≃〈 {! swap inside and cancel double Trunc n!} 〉
                  Loop k (Trunc (tlp k) (B n)) [ base^ n ] ≃〈 LoopSpace.Loop-Trunc0 k 〉 
                  τ₀ (Loop k (B n) (base^ n)) ≃〈 id 〉 
                  π k (B n) (base^ n) ∎) where
          postulate FIXME : _

    -- spectrum:
    --   Path (B n+1) No No ≃ B n
    -- set k = n, and cancel redundant truncations

    -- need pi_1(B n) = 1, for n > 2
    --   get below diagonal by above
    -- need pi_1(B 1) = pi_1(A) check (definitional)
    -- need pi_2(B 2) = pi_1(A) tricky?
    --   get diagonal by above
    -- need pi_k(B_n) for k > n easy: above truncation

    
