{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open Truncation
open Int
open Paths
open LoopSpace

module homotopy.PiKSNLess where

  module S = NSphere1
  open S using (S^ ; S-rec; S-elim)
       
  -- πk(S^ n) = τ0(Ω^k S^ n) = Ω^k-1(τ^k-1 (Ω(S^n))) 
  -- so STS τ^k-1 (Ω(S^n)) = 1
  -- so STS τ^k (Ω(S^n+1)) = 1 for k < n

  module Proof (k : TLevel) (n : Positive) 
               (lt : ∀ A t → HProp (Loop n (Trunc k A) t))
         where

    P : (S^ (S n)) → Type
    P y = Trunc k (Path{S^ (S n)} S.base y)

    F : (S^ (S n)) → Type
    F _ = Unit

    encode : {y : S^ (S n)} → P y -> F y
    encode α = <>

    decode : {y : S^ (S n)} → F y -> P y
    decode {y} <> = S-elim (λ y' → Trunc k (Path S.base y')) 
                           [ id ] 
                           (coe
                              (! (LoopOverS≃ n (S.loop (S n)) (λ y' → Trunc k (Path S.base y')) [ id ]))
                              (HProp-unique (lt _ _) _ _) -- need Id{Loop n (Trunc k _) _} _ _ 

                              {- why it doesn't work for arbitrary k
                              (apt n (ap^ (S n) (λ y' → Trunc k (Path S.base y')) (S.loop (S n))) [ id ] ≃〈 {!!} 〉 
                              (apt n (λt n (Trunc-elim (λ tβ → Loop n (Trunc k (Path S.base _)) tβ) 
                                           (λ _ → IsKTrunc-Loop n k Trunc-is) 
                                           (λ β → ap^ n [_]
                                                  (rebase n (∘-unit-l β) (ap^ n (λ x → x ∘ β) (loopSN1 n (S.loop (S n))))))))
                                     [ id ]) ≃〈 LoopSType.β n _ _ 〉 
                              (ap^ n [_] (rebase n (∘-unit-l id) (ap^ n (λ x → x ∘ id) (loopSN1 n (S.loop (S n)))))) ≃〈 {!!} 〉 
                              (ap^ n [_] (ap^ n (λ x → x) (loopSN1 n (S.loop (S n))))) ≃〈 {!!} 〉 
                              (ap^ n [_] (loopSN1 n (S.loop (S n)))) ≃〈 {!seems false!} 〉 
                              (id^ n ∎))
                              -}
                              )
                           y
  
    encode-decode : {y : S^ (S n)} (c : F y) → encode{y} (decode c) ≃ c
    encode-decode <> = id

    decode-encode : {y : S^ (S n)} (p : P y) → decode{y} (encode p) ≃ p
    decode-encode = Trunc-elim _ 
                               (λ x → path-preserves-IsTrunc Trunc-is) 
                               (path-induction (λ y' α → decode {y'} (encode [ α ]) ≃ [ α ]) id)
    

  data _<t_ : TLevel -> TLevel -> Type where
    lt-2 : ∀ {m} → -2 <t (S m)
    ltS  : ∀ {n m} → n <t m → (S n) <t (S m)

  lt->hprop : ∀ n k {A t} → k <t (tlp n) → HProp (Loop n (Trunc k A) t)
  lt->hprop One .-2 lt-2 = increment-IsTrunc (path-preserves-IsTrunc Trunc-is)
  lt->hprop One .(S -2) (ltS lt-2) = {!!}
  lt->hprop One .(S (S -2)) (ltS (ltS lt-2)) = {!!}
  lt->hprop One .(S (S (S n))) (ltS (ltS (ltS {n} ())))
  lt->hprop (S n) k lt = {!!}

  module Proof2 (k : TLevel) (n : Positive) 
                (lt : ∀ A t → HProp (Loop n (Trunc k A) t)) where

    P : (S^ (S n)) → Type
    P y = Trunc k (Path{S^ (S n)} S.base y)

    decode : (y : S^ (S n)) → P y
    decode = S-elim (λ y' → Trunc k (Path S.base y')) 
                    [ id ] 
                    (coe (! (LoopOverS≃ n (S.loop (S n)) (λ y' → Trunc k (Path S.base y')) [ id ]))
                         (HProp-unique (lt _ _) _ _)) -- need Id{Loop n (Trunc k _) _} _ _ 

    decode-encode : {y : S^ (S n)} (p : P y) → decode y ≃ p
    decode-encode = Trunc-elim _ (λ x → path-preserves-IsTrunc Trunc-is) 
                                 (path-induction (λ y' α → decode y' ≃ [ α ]) id)
    
    contra : Contractible (Trunc k (Path{S^ (S n)} S.base S.base))
    contra = decode S.base , decode-encode {S.base}

    {- why it doesn't work for arbitrary k
    (apt n (ap^ (S n) (λ y' → Trunc k (Path S.base y')) (S.loop (S n))) [ id ] ≃〈 {!!} 〉 
    (apt n (λt n (Trunc-elim (λ tβ → Loop n (Trunc k (Path S.base _)) tβ) 
                 (λ _ → IsKTrunc-Loop n k Trunc-is) 
                 (λ β → ap^ n [_]
                        (rebase n (∘-unit-l β) (ap^ n (λ x → x ∘ β) (loopSN1 n (S.loop (S n))))))))
           [ id ]) ≃〈 LoopSType.β n _ _ 〉 
    (ap^ n [_] (rebase n (∘-unit-l id) (ap^ n (λ x → x ∘ id) (loopSN1 n (S.loop (S n)))))) ≃〈 {!!} 〉 
    (ap^ n [_] (ap^ n (λ x → x) (loopSN1 n (S.loop (S n))))) ≃〈 {!!} 〉 
    (ap^ n [_] (loopSN1 n (S.loop (S n)))) ≃〈 {!seems false!} 〉 
    (id^ n ∎))
    -}
