
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

module homotopy.KGn where

  -- FIXME move to libraty

  2*_-2 : Positive -> TLevel
  2* n -2 = plus2 (-2ptl n) (-2ptl n)

  <trans : ∀ {n m p} → n <tl m → m <tl p → n <tl p
  <trans ltS q = lt-subtract-left q
  <trans (ltSR y) q = <trans y (lt-subtract-left q)

  <=trans : ∀ {n m p} → n <=tl m → m <=tl p → n <=tl p
  <=trans (Inl x) (Inl y) = Inl (<trans x y)
  <=trans (Inl x) (Inr y) = Inl (transport (λ x' → _ <tl x') y x)
  <=trans (Inr x) (Inl y) = Inl (transport (λ x' → x' <tl _) (! x) y)
  <=trans (Inr x) (Inr y) = Inr (y ∘ x)

  pos2nat-is-S : ∀ n → (pos2nat n) ≃ S (n -1pn)
  pos2nat-is-S One = id
  pos2nat-is-S (S n) = id

  n-1<n : ∀ n → tl (n -1pn) <tl tl (pos2nat n)
  n-1<n n = transport (λ x → tl (n -1pn) <tl tl x) (! (pos2nat-is-S n)) ltS

  -2ptl-S-1pn : ∀ n → (-2ptl (S n)) ≃ (tl (n -1pn))
  -2ptl-S-1pn One = id
  -2ptl-S-1pn (S n) = id

  -2ptl-S : ∀ n' →  -2ptl (S n') ≃ (S (-2ptl n'))
  -2ptl-S One = id
  -2ptl-S (S n) = ap S (! (-2ptl-S-1pn n)) ∘ ap tl (pos2nat-is-S n)

  plus2-monotone-2 : ∀ n m m' -> m <tl m' -> plus2 n m <tl plus2 n m'
  plus2-monotone-2 -2 m m' lt = lt
  plus2-monotone-2 (S y) m m' lt = ltSCong (plus2-monotone-2 y m m' lt)
  
  pos-1< : ∀ n → tl (n -1pn) <tl tl (pos2nat n)
  pos-1< One = ltS
  pos-1< (S n) = ltS

  n-1<=2n-2 : ∀ n → (tl (n -1pn)) <=tl 2* n -2
  n-1<=2n-2 One = Inr id
  n-1<=2n-2 (S One) = Inl ltS
  n-1<=2n-2 (S (S n')) = <=trans (<=SCong (n-1<=2n-2 (S n'))) 
                                 (<=trans (Inr (ap (λ x → plus2 x (-2ptl (S n'))) (! (-2ptl-S (S n')))))
                                           (Inl (plus2-monotone-2 (tl (pos2nat n')) _ _ (transport (λ x → x <tl tl (pos2nat n')) (! (-2ptl-S-1pn n')) (pos-1< n')))))

  tl-pos2nat-tlp : ∀ n → tl (pos2nat n) ≃ (tlp n)
  tl-pos2nat-tlp One = id
  tl-pos2nat-tlp (S n) = ap S (tl-pos2nat-tlp n)

  lt-unS-right' : ∀ {n m} → n <tl (S m) → Either (n <tl m) (n ≃ m)
  lt-unS-right' ltS = Inr id
  lt-unS-right' (ltSR y) = Inl y

  lt-1pn-right : ∀ k n → k <tl tlp n → k <=tl (tl (n -1pn))
  lt-1pn-right k One lt = lt-unS-right' lt
  lt-1pn-right k (S n) lt = transport (λ x → k <=tl x) (! (tl-pos2nat-tlp n)) (lt-unS-right' lt)

  2*S-2 : ∀ n → S (2* n -2) <tl 2* (S n) -2
  2*S-2 One = ltS
  2*S-2 (S n) = transport (λ x → x <tl plus2 (tl (pos2nat n)) (tl (pos2nat n))) 
                          (ap (λ x → plus2 x (-2ptl (S n))) (-2ptl-S (S n)))
                          (plus2-monotone-2 (tl (pos2nat n)) (-2ptl (S n)) (tl (pos2nat n)) (transport (λ x → x <tl tl (pos2nat n)) (! (-2ptl-S-1pn n)) (n-1<n n)))

  <=-to-+ : ∀ {n m} -> tlp n <=tl tlp m -> Σ \ k -> tlp (n +pn k) ≃ tlp m
  <=-to-+ {n}{m} (Inr p) = 0 , p ∘ ap tlp (+pn-rh-Z n)
  <=-to-+ {One} {One} (Inl (ltSR (ltSR (ltSR ()))))
  <=-to-+ {S n} {One} (Inl lt) with pos-not-<=0 n (Inl (lt-unS lt))
  ... | () 
  <=-to-+ {n} {S n'} (Inl lt) with lt-unS-right lt
  ... | Inr eq = S Z , (ap S (! eq) ∘ ap (S o tlp) (+pn-rh-Z n)) ∘ ap tlp (+pn-rh-S n Z)
  ... | Inl lt' with <=-to-+ {n}{n'} (Inl lt') 
  ...              | (n'' , eq''') = S n'' , ap S eq''' ∘ ap tlp (+pn-rh-S n n'')

  >pos->1 : ∀ k n -> tlp k <tl tlp n -> tl 1 <tl tlp n 
  >pos->1 k' One lt' with pos-not-<=0 k' (lt-unS-right' lt')
  ... | ()
  >pos->1 One (S n') lt' = lt'
  >pos->1 (S n') (S n0) lt'' = ltSR (>pos->1 n' n0 (lt-unS lt''))

  n<=2*n-2 : ∀ n → tl 1 <tl tlp n → tlp n <=tl 2* n -2
  n<=2*n-2 One (ltSR (ltSR y)) = Inl (ltSR y)
  n<=2*n-2 (S n) lt with (lt-unS-right lt) 
  ... | Inl lt' = <=trans (<=SCong (n<=2*n-2 n lt')) (Inl (2*S-2 n))
  ... | Inr eq  = transport (λ x → S x <=tl plus2 (-2ptl (S n)) (-2ptl (S n))) (! eq)
                    (arith n eq) where
    arith : ∀ n -> tlp n ≃ (tl 1) → (tl 2) <=tl 2* (S n) -2
    arith One eq' = Inr id
    arith (S n) eq' with pos-not-<=0 n (<=-unS (Inr eq'))
    ... | ()

  min-1nat : (m : Nat) → mintl (S -2) (tl m) ≃ (S -2)
  min-1nat Z = id
  min-1nat (S y) = id

  min0nat : (m : Nat) → mintl (tl 0) (tl m) ≃ (tl 0)
  min0nat Z = id
  min0nat (S y) = ap S (min-1nat y)

  π<=Trunc : ∀ k n (lt : tlp k <=tl tlp n) {A} (a0 : A) 
             -> π k (Trunc (tlp n) A) [ a0 ] ≃ π k A a0
  π<=Trunc k n lt {A} a0 with <=-to-+{k}{n} lt 
  ... | (m , eq) =  π k (Trunc (tlp n) A) [ a0 ] ≃〈 id 〉 
                    τ₀ (Loop k (Trunc (tlp n) A) [ a0 ]) ≃〈 ap τ₀ (ap-Loop-Trunc-tlevel≃ k (! eq)) 〉 
                    τ₀ (Loop k (Trunc (tlp (k +pn m)) A) [ a0 ]) ≃〈 ap τ₀ (Loop-Trunc k m) 〉 
                    τ₀ (Trunc (tl m) (Loop k A  a0))             ≃〈 FuseTrunc.path (tl 0) (tl m) (Loop k A a0) 〉 
                    (Trunc (mintl (tl 0) (tl m)) (Loop k A  a0)) ≃〈 ap (λ x → Trunc x (Loop k A a0)) (min0nat m) 〉 
                    (π k A a0) ∎

  


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
                   τ₀ (Loop (k +1) (Σ^ (n +1)) (Σbase^ (n +1))) ≃〈 ap τ₀ (LoopSpace.LoopPath.path k) 〉
                   τ₀ (Loop k (Path {(Σ^ (n +1))} (Σbase^ (n +1)) (Σbase^ (n +1))) id) ≃〈 ! (LoopSpace.Loop-Trunc0 k) 〉
                   Loop k (Trunc (tlp k) (Loop One (Σ^ (n +1)) (Σbase^ (n +1)))) [ id ] ≃〈 id 〉
                   Loop k (Trunc (tlp k) (Loop One (Susp^ (pos2nat n) A) (Σbase^ (n +1)))) [ id ] 
                     ≃〈 ap-Loop≃ k (ap (Trunc (tlp k)) (ap-Loop≃ One (ap (λ x → Susp^ x A) (pos2nat-is-S n)) (transport-Susp^-number (pos2nat-is-S n) a0 ∘ ! (ap≃ (transport-ap-assoc (λ x → Susp^ x A) (pos2nat-is-S n)))))) 
                                       (({!!} ∘
                                           ap≃
                                           (transport-Trunc {tlp k} (λ A' → A')
                                            (ap-Loop≃ One (ap (λ x → Susp^ x A) (pos2nat-is-S n))
                                             (transport-Susp^-number (pos2nat-is-S n) a0 ∘
                                              ! (ap≃ (transport-ap-assoc (λ x → Susp^ x A) (pos2nat-is-S n))))))
                                           {[ id ]}) ∘
                                          ap≃
                                          (!
                                           (transport-ap-assoc (Trunc (tlp k))
                                            (ap-Loop≃ One (ap (λ x → Susp^ x A) (pos2nat-is-S n))
                                             (transport-Susp^-number (pos2nat-is-S n) a0 ∘
                                              !
                                              (ap≃ (transport-ap-assoc (λ x → Susp^ x A) (pos2nat-is-S n))))))){[ id ]}) 〉
                   Loop k (Trunc (tlp k) (Loop One (Susp (Σ^ n)) No)) [ id ] ≃〈 ap-Loop≃ k (! F.path) (ap≃ (type≃β! F.eqv)) 〉 
                   Loop k (Trunc (tlp k) (Σ^ n)) [ Σbase^ n ]  ≃〈 Loop-Trunc0 k 〉
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
   
        
      
      