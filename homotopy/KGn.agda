
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

module homotopy.KGn where

  module B (A : Type) 
           (a0 : A)
           (A-Connected : Connected (S (S -2)) A)
           (A-level : NType (tl 1) A)
           (H-A : H-Structure A a0) where

    module Untruncated where          
      Σ^ : Positive → Type
      Σ^ n = (Susp^ (n -1pn) A)
  
      Σ^-Connected : ∀ (i : Nat) → Connected (tl i) (Σ^ (i +1np))
      Σ^-Connected n = transport
                        (λ x → NType -2 (Trunc (tl n) (Susp^ x A)))
                        (! (+1-1-cancel n)) (Susp^-Connected0 n A-Connected)
  
      Σ^-Connected' : (n : Positive) → Connected (S (-2ptl n)) (Σ^ n)
      Σ^-Connected' One = Σ^-Connected 0
      Σ^-Connected' (S One) = Σ^-Connected 1
      Σ^-Connected' (S (S n')) = coe (ap (λ x → NType -2 (Trunc (S (tl (pos2nat n'))) (Susp^ x A))) (ap pos2nat (pos2nat-+1np n')))
                                     (Σ^-Connected (pos2nat (S n'))) 
  
      Σ^-Connected'' : (n : Positive) → Connected (tlp n) (Σ^ (n +1))
      Σ^-Connected'' n = coe (ap (λ x → NType -2 (Trunc x (Susp^ (pos2nat n) A))) (tl-pos2nat-tlp n ∘ ! (-2ptl-S (S n)))) 
                          (Σ^-Connected' (n +1))
  
      Σbase^ : ∀ n → Σ^ n
      Σbase^ n = point^ (n -1pn) a0

      module Stable (k : Positive)
                    (n : Positive) 
                    (c : (tlp k <=tl 2* n -2))
           where
  
       transport-Susp^-number : ∀ {m n} (α : m ≃ n) {A}(a : A)
                              -> (transport (\x -> Susp^ x A) α (point^ m a)) ≃ (point^ n a)
       transport-Susp^-number id _ = id

       module F = FreudenthalEquiv (-2ptl n) (tlp k) (-2<pos-2 n) c (Σ^ n) (Σbase^ n) (Σ^-Connected' n) 
       -- F.path : (Trunc (tlp k) (B n)) ≃
       --          (Trunc (tlp k) (Path {Susp (B n)} (No {B n}) (No {B n})))
       
       stable : π k (Σ^ n) (Σbase^ n) ≃ π (k +1) (Σ^ (n +1)) (Σbase^ (n +1))
       stable = ! (π (k +1) (Σ^ (n +1)) (Σbase^ (n +1)) ≃〈 id 〉
                   τ₀ (Loop (k +1) (Σ^ (n +1)) (Σbase^ (n +1)))                                    ≃〈 ap τ₀ (LoopSpace.LoopPath.path k) 〉
                   τ₀ (Loop k (Path {(Σ^ (n +1))} (Σbase^ (n +1)) (Σbase^ (n +1))) id)             ≃〈 ! (LoopSpace.Loop-Trunc0 k) 〉
                   Loop k (Trunc (tlp k) (Loop One (Σ^ (n +1)) (Σbase^ (n +1)))) [ id ]           ≃〈 id 〉
                   Loop k (Trunc (tlp k) (Loop One (Susp^ (pos2nat n) A) (Σbase^ (n +1)))) [ id ] ≃〈 ap-Loop≃ k (ap (Trunc (tlp k)) (ap-Loop≃ One (ap (λ x → Susp^ x A) (pos2nat-is-S n)) (transport-Susp^-number (pos2nat-is-S n) a0 ∘ ! (ap≃ (transport-ap-assoc (λ x → Susp^ x A) (pos2nat-is-S n)))))) ((ap [_] (ap-Loop≃-id One (ap (λ x → Susp^ x A) (pos2nat-is-S n)) (transport-Susp^-number (pos2nat-is-S n) a0 ∘ ! (ap≃ (transport-ap-assoc (λ x → Susp^ x A) (pos2nat-is-S n))))) ∘ ap≃ (transport-Trunc {tlp k} (λ A' → A') (ap-Loop≃ One (ap (λ x → Susp^ x A) (pos2nat-is-S n)) (transport-Susp^-number (pos2nat-is-S n) a0 ∘ ! (ap≃ (transport-ap-assoc (λ x → Susp^ x A) (pos2nat-is-S n)))))) {[ id ]}) ∘ ap≃ (! (transport-ap-assoc (Trunc (tlp k)) (ap-Loop≃ One (ap (λ x → Susp^ x A) (pos2nat-is-S n)) (transport-Susp^-number (pos2nat-is-S n) a0 ∘ ! (ap≃ (transport-ap-assoc (λ x → Susp^ x A) (pos2nat-is-S n))))))){[ id ]}) 〉
                   Loop k (Trunc (tlp k) (Loop One (Susp (Σ^ n)) No)) [ id ]                      ≃〈 ap-Loop≃ k (! F.path) (ap≃ (type≃β! F.eqv)) 〉 
                   Loop k (Trunc (tlp k) (Σ^ n)) [ Σbase^ n ]                                     ≃〈 Loop-Trunc0 k 〉
                   τ₀ (Loop k (Σ^ n) (Σbase^ n)) ≃〈 id 〉 
                   π k (Σ^ n) (Σbase^ n) ∎)


    module Truncated where
  
      open Untruncated hiding (module Stable)
    
      -- Bn = KGn when A is KG1
      B : Positive → Type
      B n = Trunc (tlp n) (Σ^ n)

      B-Connected : ∀ (i : Nat) → Connected (tl i) (B (i +1np))
      B-Connected n = connected-Trunc _ _ _ (Σ^-Connected n)
  
      B-Connected'' : (n : Positive) → Connected (tlp n) (B (n +1))
      B-Connected'' n = coe (ap (NType -2) (ap2 Trunc (tl-pos2nat-tlp n) (ap B (pos2nat-+1np n)))) (B-Connected (pos2nat n))
  
      base^ : ∀ n → B n
      base^ n = [ Σbase^ n ]

      module Stable (k : Positive)
                    (n : Positive) 
                    (indexing : Either (tlp k <tl tlp n) ((tlp k ≃ tlp n) × (tl 1 <tl tlp n)))
             where

        lte : tlp k <=tl tlp n
        lte with indexing 
        ... | Inl lt = Inl lt
        ... | Inr (eq , _) = Inr eq


        k<= : tlp k <=tl 2* n -2
        k<= with indexing
        ...    | Inl lt = <=trans (Inl lt) (n<=2*n-2 n (>pos->1 k n lt))  
        ...    | Inr (eq , lt) = <=trans (Inr eq) (n<=2*n-2 n lt)
          
        stable : π k (B n) (base^ n) ≃ π (k +1) (B (n +1)) (base^ (n +1))
        stable = π k (B n) (base^ n) ≃〈 π<=Trunc k n lte (Σbase^ n) 〉 
                 π k (Σ^ n) (Σbase^ n) ≃〈 Untruncated.Stable.stable k n k<= 〉 
                 π (k +1) (Σ^ (n +1)) (Σbase^ (n +1)) ≃〈 ! (π<=Trunc (k +1) (n +1) (<=SCong lte) (Σbase^ (n +1))) 〉 
                 π (k +1) (B (n +1)) (base^ (n +1)) ∎ 

    -- spectrum:
    --   Path (B n+1) No No ≃ B n
    -- set k = n, and cancel redundant truncations

    open Truncated

    module BelowDiagonal where

      π1 : (n : Positive) → (π One (B (n +1)) (base^ (n +1))) ≃ Unit
      π1 n = π1Connected≃Unit (tlp n) _ (base^ (n +1)) (B-Connected'' n) (1<=pos n)

      πk : (k n : Positive) → (tlp k <tl tlp n) → π k (B n) (base^ n) ≃ Unit
      πk One One (ltSR (ltSR (ltSR ())))
      πk One (S n) lt = π1 n
      πk (S k) One lt with pos-not-<=0 k (Inl (lt-unS lt))
      ... | () 
      πk (S k) (S n) lt = π (k +1) (B (n +1)) (base^ (n +1)) ≃〈 ! (Stable.stable k n (Inl (lt-unS lt))) 〉
                          π k (B n) (base^ n) ≃〈 πk k n (lt-unS lt) 〉
                          Unit ∎ 

    module OnDiagonal where
    
      π1 : π One (B One) (base^ One)  ≃  π One A a0
      π1 = τ₀ (Path {Trunc (tl 1) A} [ a0 ] [ a0 ]) ≃〈 ap τ₀ (ap-Loop≃ One (UnTrunc.path _ _ A-level) (ap≃ (type≃β (UnTrunc.eqv _ _ A-level)))) 〉
           τ₀ (Path {A} a0 a0) ∎

      Two : Positive 
      Two = S One

      π2 : π Two (B Two) (base^ Two) ≃ π One A a0
      π2 = path A a0 A-level A-Connected H-A

      πn : (n : Positive) → π n (B n) (base^ n) ≃ π One A a0
      πn One = π1
      πn (S One) = π2
      πn (S (S n)) = πn (S n) ∘ ! (Stable.stable (S n) (S n) (Inr (id , >pos->1 n (S n) ltS))) 

    module AboveDiagonal where

      πabove : (k n : Positive) → tlp n <tl tlp k → π k (B n) (base^ n)  ≃  Unit
      πabove k n lt = Contractible≃Unit (use-level { -2} (Trunc-level-better (Loop-level-> (tlp n) k Trunc-level lt))) 


  module Explicit (G : AbelianGroup) where

    module KG1 = K1 (fst G)

    module KGn = B (KG1.KG1) KG1.base KG1.Pi0.KG1-Connected KG1.level (H-on-KG1.H-KG1 G)
    module KGnT = KGn.Truncated

    KG : Positive -> Type
    KG One = KG1.KG1
    KG (S n) = KGnT.B (S n)

    KGbase : ∀ n → KG n
    KGbase One = KG1.base
    KGbase (S n) = KGnT.base^ (S n)

    πn-KGn-is-G : ∀ n → π n (KG n) (KGbase n) ≃ (Group.El (fst G))
    πn-KGn-is-G One = KG1.Pi1.π1[KGn]-is-G
    πn-KGn-is-G (S n) = KG1.Pi1.π1[KGn]-is-G ∘ KGn.OnDiagonal.πn (S n)

    πk-KGn-trivial : ∀ k n → Either (tlp k <tl tlp n) (tlp n <tl tlp k) 
                   → π k (KG n) (KGbase n) ≃ Unit
    πk-KGn-trivial k One (Inl k<n) with pos-not-<=0 k (lt-unS-right k<n)
    ... | ()
    πk-KGn-trivial k (S n) (Inl k<n) = KGn.BelowDiagonal.πk k (S n) k<n
    πk-KGn-trivial k One (Inr n<k) = Contractible≃Unit (use-level { -2} (Trunc-level-better (Loop-level-> (tlp One) k KG1.level n<k)))
    πk-KGn-trivial k (S n) (Inr n<k) = KGn.AboveDiagonal.πabove k (S n) n<k
