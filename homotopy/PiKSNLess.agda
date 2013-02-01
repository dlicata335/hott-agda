{-# OPTIONS --type-in-type #-}

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

  -- done out in encode/decode style
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

  -- drop the units
  module Proof2 (k : TLevel) (n : Positive) (lt : k <tl (tlp n)) where

    P : (S^ (S n)) → Type
    P y = Trunc k (Path{S^ (S n)} S.base y)

    center : (y : S^ (S n)) → P y
    center = S-elim (λ y' → Trunc k (Path S.base y')) 
                    [ id ] 
                    (coe (! (LoopOverS≃ n (S.loop (S n)) (λ y' → Trunc k (Path S.base y')) [ id ]))
                         (HProp-unique (HProp-Loop-in-Trunc< k n lt) _ _)) -- need Id{Loop n (Trunc k _) _} _ _ 

    paths : {y : S^ (S n)} (p : P y) → center y ≃ p
    paths = Trunc-elim _ (λ x → path-preserves-IsTrunc Trunc-is) 
                         (path-induction (λ y' α → center y' ≃ [ α ]) id)
    
    contra : Contractible (Trunc k (Path{S^ (S n)} S.base S.base))
    contra = center S.base , paths {S.base}


  -- works for k at least 2
  -- separately should do π1(S^n) for 1 < n

  theorem : (k : Positive) (n : Positive) → (tlp k <tl tlp n) 
          → π (S k) (S^ (S n)) S.base ≃ Unit
  theorem k n lt = π (S k) (S^ (S n)) S.base                                          ≃〈 id 〉
                   Trunc (tl 0) (Loop (S k) (S^ (S n)) S.base)                        ≃〈 ap (Trunc (tl 0)) (LoopPath.path k) 〉
                   Trunc (tl 0) (Loop k (Loop One (S^ (S n)) S.base) id)              ≃〈 ! (Loop-Trunc k 0) 〉
                   Loop k (Trunc (tlp (k +pn 0)) (Loop One (S^ (S n)) S.base)) [ id ] ≃〈 ap-Loop-Trunc-tlevel k (ap tlp (+pn-rh-Z k)) 〉
                   Loop k (Trunc (tlp k) (Loop One (S^ (S n)) S.base)) [ id ]         ≃〈 ap-Loop≃ k (Contractible≃Unit (Proof2.contra _ _ lt)) id 〉
                   Loop k Unit <>                                                     ≃〈 ! (LoopUnit.path k) 〉 
                   Unit ∎

  {- why the above argument doesn't work for arbitrary k
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
