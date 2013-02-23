
{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open Truncation
open Int
open LoopSpace
open Suspension
open import homotopy.Freudenthal
open import homotopy.PiLessOfConnected

module homotopy.KGn where

  Abelian : Type -> Type
  Abelian A = (x : A) (p q : Path x x) → p ∘ q ≃ q ∘ p

  record H-Structure (A : Type) (a0 : A) : Type where
   field 
     _⊙_     : A → A → A
    unitl    : ((a : A) → a ⊙ a0 ≃ a)
    unitr    : ((a : A) → a ⊙ a0 ≃ a)
    isequivl : ((a : A) → IsEquiv (_⊙_ a))

  -- like K_G,1 for abelian G
  IsK1 : Type -> Type
  IsK1 A = Σ \ (a0 : A) →  
           Connected (S (S -2)) A × 
           NType (tl 1) A ×
--           Abelian A ×
           H-Structure A a0

  module B (A : Type) (isK1 : IsK1 A) where

    a0 : A
    a0 = fst isK1

    A-level : NType (tl 1) A
    A-level = fst (snd (snd isK1))

    A-Connected : Connected (S (S -2)) A
    A-Connected = fst (snd isK1)

    A-H : H-Structure A a0
    A-H = snd (snd (snd isK1))

    -- Bn = KGn 
    B : Positive → Type
    B n = Trunc (tlp n) (Susp^ (n -1pn) A)

{-
    B-Connected : ∀ (i : Nat) → Connected (tl i) (B (i +1np))
    B-Connected n = transport
                      (λ x → NType -2 (Trunc (tl n) (Trunc (tlp (n +1np)) (Susp^ x A))))
                      (! (+1-1-cancel n)) (connected-Trunc _ _ _ (Susp^-Connected0 n A-Connected))

    B-Connected' : (n : Positive) → Connected (S (-2ptl n)) (B n)
    B-Connected' One = B-Connected 0
    B-Connected' (S One) = B-Connected 1
    B-Connected' (S (S n')) = {!B-Connected (pos2nat (S n'))!} where -- {!S^-Connected (pos2nat (S n'))!} -- right where
                             postulate FIXME : _
        -- transport (λ x → Connected (S (tl (pos2nat n'))) (Susp (S^ x))) 
        --                         (pos2nat-+1np n')
        --                         {!(S^-Connected (pos2nat (S n')))!}

    B-Connected'' : (n : Positive) → Connected (tlp n) (B (n +1))
    B-Connected'' n = {!B-Connected' (n +1)!}
-}  

    base^ : ∀ n → B n
    base^ n = [ point^ (n -1pn) a0 ]

{-
    module Stable (k : Positive)
                  (n : Positive) 
                  (c : (tlp k <=tl plus2 (-2ptl n) (-2ptl n)))
                  -- i.e. k <= 2n - 2 
           where
  
      module F = FreudenthalEquiv (-2ptl n) (tlp k) (-2<pos-2 n) c (B n) (base^ n) (B-Connected' n) 
  
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


    module BelowDiagonal where

      π1 : (n : Positive) → (π One (B (n +1)) (base^ (n +1))) ≃ Unit
      π1 n = π1Connected≃Unit (tlp n) _ (base^ (n +1)) (B-Connected'' n) (1<=pos n)

      -- TODO: index math

      πk : ∀ k n → (tlp k <tl tlp n) → π k (B n) (base^ n) ≃ Unit
      πk One One (ltSR (ltSR (ltSR ())))
      πk One (S n) lt = π1 n
      πk (S k) One lt with pos-not-<0 k (Inl (lt-unS lt))
      ... | () 
      πk (S k) (S n) lt = π (k +1) (B (n +1)) (base^ (n +1)) ≃〈 ! (Stable.stable k n (arith k n (lt-unS lt))) 〉
                          π k (B n) (base^ n) ≃〈 πk k n (lt-unS lt) 〉
                          Unit ∎ where
         -- k < n  implies  k <= 2n-2 for positive k n
         -- k <= n-1
         -- n-1 <= 2n-2 plus transitivity
         arith : ∀ k n → tlp k <tl tlp n → tlp k <=tl plus2 (-2ptl n) (-2ptl n)
         arith k n = {!n!}

         n-1<=2n-2 : ∀ n → (tl (n -1pn)) <=tl plus2 (-2ptl n) (-2ptl n)
         n-1<=2n-2 One = Inr id
         n-1<=2n-2 (S One) = Inl ltS
         n-1<=2n-2 (S (S n')) = transport (λ x → S (tl (pos2nat n')) <=tl x) {!!}
                                  (<=SCong (n-1<=2n-2 (S n')))
         -- (S (plus2 (-2ptl (S n')) (-2ptl (S n'))))
         -- = 1 + (2 + (-2 + 1 + n') + (-2 + 1 + n'))
         -- = 1 + (2 + (n' - 1) + (n' - 1))
         -- = 1 + 2n'
         --
         -- (plus2 (tl (pos2nat n')) (tl (pos2nat n')))
         -- = 2n' + 2
-}
    module OnDiagonal where
    
      π1 : π One (B One) (base^ One)  ≃  π One A a0
      π1 = τ₀ (Path {Trunc (tl 1) A} [ a0 ] [ a0 ]) ≃〈 ap τ₀ (ap-Loop≃ One (UnTrunc.path _ _ A-level) (ap≃ (type≃β (UnTrunc.eqv _ _ (fst (snd (snd isK1))))))) 〉
           τ₀ (Path {A} a0 a0) ∎
    
      -- tricky?  pi_2(B 2) = pi_1(A) 
      module π2 where 

        Two = One +1

        B2 = B Two
        base2 = base^ Two
  
        P : B2 → Type
        P x = τ₁ (Path {B2} base2 x)

        open H-Structure A-H

        Codes : B2 → NTypes (tlp One)
        Codes = Trunc-rec (NTypes-level (tlp One))
                          (Susp-rec (A , A-level) 
                                    (A , A-level)
                                    (λ a → coe (ΣSubsetPath (λ _ → (NType-is-HProp _)))
                                               (ua (_⊙_ a , isequivl a)))) 

        encode0 : ∀ {x} → (Path {B2} base2 x) -> fst (Codes x)
        encode0 α = transport (fst o Codes) α a0

        encode : ∀ {x} → P x -> fst (Codes x)
        encode {x} = Trunc-rec (snd (Codes x)) encode0 

        in-Ω2≃ : ∀ {A} {a a' : A} {α : a ≃ a'} 
                   -> Path α α ≃ Path{Path a a} id id
        in-Ω2≃ {α = id} = id

        decode' : A → (τ₁ (Path{B2} base2 base2))
        decode' a = [ ap [_] (! (mer a0) ∘ mer a) ]

        {- works
        encode-decode' : (a : A) → encode{base2}(decode' a) ≃ a
        encode-decode' a = encode {base2} (decode' a) ≃〈 {!!} 〉 
                           encode {base2} [ ap [_] (! (mer a0) ∘ mer a) ] ≃〈 id 〉 
                           encode {base2} [ ap [_] (! (mer a0) ∘ mer a) ] ≃〈 id 〉 
                           transport (fst o Codes) (ap [_] (! (mer a0) ∘ mer a)) a0 ≃〈 {!!} 〉 
                           coe (ap (fst o Codes) (ap [_] (! (mer a0) ∘ mer a))) a0 ≃〈 {!!} 〉 
                           coe (ap (fst o Codes o [_]) (! (mer a0) ∘ mer a)) a0 ≃〈 {!!} 〉 
                           coe (! (ap (fst o Codes o [_]) (mer a0) ∘ ap (fst o Codes o [_]) (mer a))) a0 ≃〈 {!!} 〉 
                           coe (! (ap (fst o Codes o [_]) (mer a0)))
                               (coe (ap (fst o Codes o [_]) (mer a)) a0) ≃〈 {!!} 〉 
                           coe (! (ap (fst o Codes o [_]) (mer a0)))
                               (coe (ua (_⊙_ a , isequivl a)) a0) ≃〈 {!!} 〉 
                           coe (! (ap (fst o Codes o [_]) (mer a0)))
                               (a ⊙ a0) ≃〈 {!!} 〉 
                           coe (! (ua (_⊙_ a0 , isequivl a0)))
                               a ≃〈 {!!} 〉 
                           coe (! (ua id-equiv))
                               a ≃〈 {!!} 〉 
                           a ∎
        -}

        -- need 
        --      mer (a ⊙ a') ≃ mer a ⊙ mer a'
        -- follows: mer a0 ≃ id

        decode : ∀ {x} → fst (Codes x) → P x 
        decode {x} = Trunc-elim (λ x' → fst (Codes x') → P x') (λ _ → Πlevel (λ _ → increment-level Trunc-level)) 
                                (Susp-elim _ 
                                           decode'
                                           (λ a → [ ap [_] (mer a) ])
                                           (λ a → {!!}))
                                x where
               STS : (a a' : A) → 
                        transport (\ z -> P [ z ]) (mer a) (decode' a') ≃
                        [ ap [_] (mer ((transport (\ z -> fst (Codes [ z ]))) (mer a) a')) ]
               STS a a' = transport (\ z -> P [ z ]) (mer a) (decode' a') ≃〈 {!!} 〉
                          [ ap [_] (mer a) ∘ ap [_] (! (mer a0) ∘ mer a') ] ≃〈 {!!} 〉
                          [ ap [_] (mer a ∘ ! (mer a0) ∘ mer a') ] ≃〈 {!!} 〉
                          [ ap [_] (mer (a ⊙ a')) ] ≃〈 {!!} 〉 
                          [ ap [_] (mer ((transport (\ z -> fst (Codes [ z ]))) (mer a) a')) ] ∎
{-
        main-lemma-eqv : Equiv (τ₁ (Path{B2} base2 base2)) A
        main-lemma-eqv = (improve (hequiv {!!} {!!} {!!} {!!}))

        main-lemma : (τ₁ (Path{B2} base2 base2)) ≃ A
        main-lemma = ua main-lemma-eqv

        path : (π Two B2 base2) ≃ π One A a0 
        path = (π Two B2 base2) ≃〈 id 〉
               (τ₀ (Loop Two B2 base2)) ≃〈 {!!} 〉
               (Loop One (τ₁ (Path{B2} base2 base2)) [ id ]) ≃〈 {!!} 〉
               (Loop One A a0) ≃〈 ! (UnTrunc.path (tl 0) (Loop One A a0) (use-level A-level _ _)) 〉
               π One A a0 ∎
               -- improve (hequiv {!(encode {base2})!} decode' {!!} {!!})
-}

      -- TODO: prove everything else on the diagonal by Freudenthal

    module AboveDiagonal where

      πabove : ∀ k n → tlp n <tl tlp k → π k (B n) (base^ n)  ≃  Unit
      πabove k n lt = Contractible≃Unit (use-level { -2} (Trunc-level-better (Loop-level-> (tlp n) k Trunc-level lt)))
   
        
      
      