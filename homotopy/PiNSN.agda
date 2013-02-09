{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open Truncation
open Int

open LoopSpace
open import homotopy.Pi1S1 using (Ω₁[S¹]≃Int)

module homotopy.PiNSN where

  module S = NSphere1
  open S using (S^ ; S-rec; S-elim)

  promote : ∀ {n} → (S^ n) → (Path{S^ (n +1)} S.base S.base)
  promote{n} = S-rec id (loopSN1 n (S.loop (S n)))

  decode' : ∀ {n} 
          → Trunc (tlp n) (S^ n) 
          → Trunc (tlp n) (Path{S^ (n +1)} S.base S.base)
  decode'{n} = Trunc-func (promote{n})

  P : {n : Positive} → S^ (n +1) → Type
  P {n} x = Trunc (tlp n) (Path{S^ (n +1)} S.base x)

  S-loops : ∀ n -> (x : Trunc (tlp n) (S^ n)) → Loop n (Trunc (tlp n) (S^ n)) x
  S-loops n = Trunc-elim (\ x ->  Loop n (Trunc (tlp n) (S^ n)) x)
                         (λ x → IsKTrunc-Loop n (tlp n) Trunc-level)
                         (S-elim {n} (λ x → Loop n (Trunc (tlp n) (S^ n)) [ x ])
                                     (ap^ n [_] (S.loop n)) 
                                     (preserves n)) where
     preserves : ∀ n → LoopOver n (S.loop n) 
                                  (λ x → Loop n (Trunc (tlp n) (S^ n)) [ x ])
                                  (ap^ n [_] (S.loop n))
     preserves One = (transport (λ x → Loop One (Trunc (tlp One) (S^ One)) [ x ])
                                (S.loop One) 
                                (ap^ One [_] (S.loop One)))                       ≃〈 ap≃ (transport-ap-assoc' (λ x → Path {Trunc (tlp One) (S^ One)} x x) [_] (S.loop One)) 〉
                     (transport (λ x → Path {Trunc (tlp One) (S^ One)} x x) 
                                (ap [_] (S.loop One))
                                (ap [_] (S.loop One)))                            ≃〈 transport-Path (λ x → x) (λ x → x) (ap [_] (S.loop One)) (ap [_] (S.loop One)) 〉
                     (ap (λ x → x) (ap [_] (S.loop One))
                      ∘ (ap [_] (S.loop One))
                      ∘ ! (ap (λ x → x) (ap [_] (S.loop One))))                    ≃〈 ap (λ z → z ∘ (ap [_] (S.loop One)) ∘ ! z) (ap-id (ap [_] (S.loop One))) 〉
                     ((ap [_] (S.loop One)) ∘ 
                      (ap [_] (S.loop One)) ∘ 
                      (! (ap [_] (S.loop One))))                                  ≃〈 ap (λ z → ap [_] (S.loop One) ∘ z) (!-inv-r (ap [_] (S.loop One))) 〉
                     (ap [_] (S.loop One))∎
     preserves (S n) = HProp-unique (NType-LoopOver n (S -2) (id^ n) (λ x → HSet-Loop (S n) Trunc-level)) _ _
                   
  endo : ∀ n -> Loop (S n) Type (Trunc (tlp n) (S^ n))
  endo n = λt n (S-loops n)

  Codes : ∀ n -> (S^ (n +1)) → Type
  Codes n = S-rec (Trunc (tlp n) (S^ n)) (endo n)

  NType-Codes : ∀ n x → NType (tlp n) (Codes n x)
  NType-Codes n = S-elim (\ x -> NType (tlp n) (Codes n x))
                           Trunc-level
                           (HProp-unique (NType-LoopOver n (S -2) (id^ n) (λ x → increment-level (NType-is-HProp _))) _ _)

  demote : {n : _} {x : S^ (n +1)} → Path S.base x → Codes n x
  demote {n} = (\ α → coe (ap (Codes n) α) [ S.base ])

  encode : {n : _} {x : S^ (n +1)} → P x → Codes n x
  encode {n} {x} tα = Trunc-rec (NType-Codes n x) 
                                demote
                                tα

  abstract
    encode-decode' : {n : _} 
                    → (c : Codes n S.base)
                    → encode (decode' c) ≃ c
    encode-decode'{n} = Trunc-elim (\ c -> encode (decode' c) ≃ c) 
                                   (λ x → path-preserves-level Trunc-level)
                                   (S-elim (λ c' → encode (decode' [ c' ]) ≃ [ c' ]) 
                                           id
                                           (resp n)) where
      resp : ∀ n → LoopOver n (S.loop n) (λ c' → encode (decode' [ c' ]) ≃ [ c' ]) id
      resp n = coe (LoopPathOver n (S.loop n) (encode o decode' o [_]) [_] id)
                   (rebase n id (ap^ n (encode o decode' o [_]) (S.loop n)) ≃〈 ap≃ (rebase-idpath n) 〉
                    ap^ n (encode o decode' o [_]) (S.loop n)               ≃〈 id 〉 
                    ap^ n (demote o promote) (S.loop n)                     ≃〈 ap^-o n demote promote (S.loop n) 〉
                    ap^ n demote (ap^ n promote (S.loop n))                 ≃〈 ap (ap^ n demote) (S.βloop/rec n id (loopSN1 n (S.loop (S n)))) 〉
                    ap^ n demote (loopSN1 n (S.loop (S n)))                 ≃〈 id 〉
                    ap^ n (\ x -> coe (ap (Codes n) x) [ S.base ])
                          (loopSN1 n (S.loop (S n)))                         ≃〈 id 〉
                    ap^ n ((\ x -> coe x [ S.base ]) o (ap (Codes n)))
                          (loopSN1 n (S.loop (S n)))                         ≃〈 ap^-o n (λ x → coe x [ S.base ]) (ap (Codes n)) (loopSN1 n (S.loop (S n))) 〉
                    ap^ n (\ x -> coe x [ S.base ]) 
                          (ap^ n (ap (Codes n)) 
                                 (loopSN1 n (S.loop (S n))))                 ≃〈 ap (ap^ n (λ x → coe x [ S.base ])) (ap^-ap-assoc' n (Codes n) (S.loop (S n))) 〉 
                    ap^ n (\ x -> coe x [ S.base ]) (loopSN1 n 
                      (ap^ (S n) (Codes n) 
                                  (S.loop (S n))))                           ≃〈 ap^-o n (λ f → f [ S.base ]) coe (loopSN1 n (ap^ (S n) (Codes n) (S.loop (S n)))) 〉 
                    apt n (ap^ (S n) (Codes n) (S.loop (S n))) [ S.base ]    ≃〈 ap (λ x → apt n x [ S.base ]) (S.βloop/rec (S n) (Trunc (tlp n) (S^ n)) (endo n)) 〉
                    apt n (λt n (S-loops n)) [ S.base ]                      ≃〈 LoopSType.β n _ _ 〉
                    ap^ n [_] (S.loop n) ∎)
  
  decode : {n : _} {x : S^ (n +1)} → Codes n x → P x 
  decode {n} {x} = S-elim (λ x' → Codes n x' → P x') 
                          decode'
                          (pl{n})
                          x 
   where 
    abstract
     pl : ∀ {n} → LoopOver (S n) (S.loop (S n)) (λ x' → Codes n x' → P x') decode'
     pl {n} = coe (Loop→OverS n (S.loop (S n)) {Codes n} {P} decode') 
                  (ap (λl n) (λ≃ STS0)) 
        where 
         STS0 : (x' : _) →
                        ∘^ n (apt n (ap^ (S n) P (S.loop (S n))) (decode' x'))
                             (ap^ n decode' (apt n (!^ (S n) (ap^ (S n) (Codes n) (S.loop (S n)))) x'))
                        ≃ id^ n
         STS0 x' = !^-inv-l≃ n (STS1 x') where
          STS1 : (x' : _) →
                        (apt n (ap^ (S n) P (S.loop (S n))) (decode' x'))
                      ≃ (!^ n (ap^ n decode' (apt n (!^ (S n) (ap^ (S n) (Codes n) (S.loop (S n)))) x')))
          STS1 x' = 
                  (apt n (ap^ (S n) P (S.loop (S n))) (decode' x')) ≃〈 ap (λ x0 → apt n x0 (decode' x')) (ap^TruncPathPost n (tlp n) (S.loop (S n)) _) 〉 
                  (apt n (λt n (Trunc-elim (λ tβ → Loop n (Trunc (tlp n) (Path _ _)) tβ) 
                                           (λ _ → IsKTrunc-Loop n (tlp n) Trunc-level)
                                           (λ β → ap^ n [_]
                                                    (rebase n (∘-unit-l β)
                                                    (ap^ n (λ x → x ∘ β) (loopSN1 n (S.loop (S n))))))))
                              (decode' x')) ≃〈 LoopSType.β n _ _ 〉
                  ((Trunc-elim (λ tβ → Loop n (Trunc (tlp n) (Path _ _)) tβ) 
                                               (λ _ → IsKTrunc-Loop n (tlp n) Trunc-level)
                                               (λ β → ap^ n [_]
                                                    (rebase n (∘-unit-l β)
                                                    (ap^ n (λ x → x ∘ β) (loopSN1 n (S.loop (S n)))))))
                   (decode' x')) ≃〈 STS2 x' 〉 
                  (ap^ n decode' (S-loops n x')) ≃〈 ! (ap (ap^ n decode') (LoopSType.β n _ x')) 〉 
                  -- start expanding back to the other side
                  (ap^ n decode' (apt n (λt n (S-loops n)) x')) ≃〈 ! (ap (λ x0 → ap^ n decode' (apt n x0 x')) (S.βloop/rec (S n) (Trunc (tlp n) (S^ n)) (endo n))) 〉 
                  (ap^ n decode' (apt n (ap^ (S n) (Codes n) (S.loop (S n))) x')) ≃〈 ! (!^-invol n (ap^ n decode' (apt n (ap^ (S n) (Codes n) (S.loop (S n))) x'))) 〉 
                  !^ n (!^ n (ap^ n decode' (apt n (ap^ (S n) (Codes n) (S.loop (S n))) x'))) ≃〈 ap (!^ n) (! (ap^-! n decode' (apt n (ap^ (S n) (Codes n) (S.loop (S n))) x'))) 〉 
                  (!^ n (ap^ n decode' (!^ n (apt n (ap^ (S n) (Codes n) (S.loop (S n))) x')))) ≃〈 ap (λ x0 → !^ n (ap^ n decode' x0)) (! (apt-! n (ap^ (S n) (Codes n) (S.loop (S n))) x')) 〉 
                  (!^ n (ap^ n decode' (apt n (!^ (S n) (ap^ (S n) (Codes n) (S.loop (S n)))) x')))
                  ∎ where
             STS2 : (x' : _) → ((Trunc-elim (λ tβ → Loop n (Trunc (tlp n) (Path _ _)) tβ) 
                                                (λ _ → IsKTrunc-Loop n (tlp n) Trunc-level)
                                                (λ β → ap^ n [_]
                                                     (rebase n (∘-unit-l β)
                                                     (ap^ n (λ x → x ∘ β) (loopSN1 n (S.loop (S n)))))))
                               (decode' x'))
                             ≃ (ap^ n decode' (S-loops n x'))
             STS2 = Trunc-elim _ (λ _ → path-preserves-level (IsKTrunc-Loop n (tlp n) Trunc-level))
                                 (λ x0 → ! (STS3 x0)) where
              STS3 : (s : _) → (ap^ n decode' (S-loops n [ s ]))
                               ≃ (ap^ n [_]
                                   (rebase n (∘-unit-l (promote s))
                                   (ap^ n (λ x → x ∘ (promote s)) (loopSN1 n (S.loop (S n))))))
              STS3 = 
               S-elim _ 
                    (ap^ n decode' (S-loops n [ S.base ]) ≃〈 id 〉
                     ap^ n decode' (ap^ n [_] (S.loop n)) ≃〈 ! (ap^-o n decode' [_] (S.loop n)) 〉
                     ap^ n (decode' o [_]) (S.loop n) ≃〈 id 〉
                     ap^ n ([_] o promote) (S.loop n) ≃〈 ap^-o n [_] promote (S.loop n) 〉
                     ap^ n [_] (ap^ n promote (S.loop n)) ≃〈 ap (ap^ n [_]) STS4 〉
                     ap^ n [_]
                      (rebase n (∘-unit-l (promote S.base))
                                (ap^ n (λ x0 → x0 ∘ promote S.base)
                                (loopSN1 n (S.loop (S n))))) ∎)
                    (fst (use-level (NType-LoopOver n -2 (S.loop n) (λ x → use-level (HSet-Loop n Trunc-level) _ _)))) 
                 where
                  STS4 : (ap^ n promote (S.loop n)) ≃
                         (rebase n (∘-unit-l (promote S.base))
                                (ap^ n (λ x0 → x0 ∘ promote S.base)
                                (loopSN1 n (S.loop (S n))))) 
                  STS4 = (ap^ n promote (S.loop n)) ≃〈 S.βloop/rec n id (loopSN1 n (S.loop (S n))) 〉 
                         (loopSN1 n (S.loop (S n))) ≃〈 ! (ap^-idfunc n (loopSN1 n (S.loop (S n)))) 〉
                         -- start expanding back to the other side
                         (ap^ n (λ x0 → x0 ∘ id)
                                (loopSN1 n (S.loop (S n)))) ≃〈 id 〉 
                         (ap^ n (λ x0 → x0 ∘ promote S.base)
                                (loopSN1 n (S.loop (S n)))) ≃〈 ap≃ (! (rebase-idpath n)) 〉 
                         (rebase n id
                                    (ap^ n (λ x0 → x0 ∘ promote S.base)
                                    (loopSN1 n (S.loop (S n))))) ≃〈 id 〉 
                         (rebase n (∘-unit-l (promote S.base))
                                    (ap^ n (λ x0 → x0 ∘ promote S.base)
                                    (loopSN1 n (S.loop (S n))))) ∎

  abstract
    decode-encode : {n : _} {x : S^ (n +1)} (α : P x) → decode{n}{x} (encode{n}{x} α) ≃ α
    decode-encode {n}{x} = Trunc-elim _ (λ _ → path-preserves-level Trunc-level)
                                        case-for-[] where
      case-for-[] : {x : S^ (n +1)} (α : Path S.base x) → decode{n}{x} (encode{n}{x} [ α ]) ≃ [ α ]
      case-for-[] = path-induction (λ x α → decode{n}{x} (encode{n}{x} [ α ]) ≃ [ α ]) id

  τn[Ω[S^n+1]]-Equiv-τn[S^n] : ∀ {n} → Equiv (Trunc (tlp n) (Path{S^ (n +1)} S.base S.base))
                                             (Trunc (tlp n) (S^ n))
  τn[Ω[S^n+1]]-Equiv-τn[S^n] = (improve (hequiv encode decode decode-encode encode-decode'))

  τn[Ω[S^n+1]]-is-τn[S^n] : ∀ {n} → Trunc (tlp n) (Path{S^ (n +1)} S.base S.base)
                                  ≃ Trunc (tlp n) (S^ n)
  τn[Ω[S^n+1]]-is-τn[S^n] = (ua τn[Ω[S^n+1]]-Equiv-τn[S^n])

  preserves-point : ∀ {n} → coe (τn[Ω[S^n+1]]-is-τn[S^n] {n}) [ id ] ≃ [ S.base ]
  preserves-point {n} = ap≃ (type≃β τn[Ω[S^n+1]]-Equiv-τn[S^n]) {[ id ]}

  πnSⁿ-diagonal : ∀ n → π (S n) (S^ (n +1)) S.base ≃ π n (S^ n) S.base
  πnSⁿ-diagonal n = π (S n) (S^ (n +1)) S.base ≃〈 id 〉
                    τ₀ (Loop (S n) (S^ (n +1)) S.base) ≃〈 ap τ₀ (LoopPath.path n) 〉
                    τ₀ (Loop n (Path {S^ (n +1)} S.base S.base) id) ≃〈 ! (Loop-Trunc0 n) 〉
                    Loop n (Trunc (tlp n) (Path {S^ (n +1)} S.base S.base)) [ id ] ≃〈 ap-Loop≃ n τn[Ω[S^n+1]]-is-τn[S^n] preserves-point 〉
                    Loop n (Trunc (tlp n) (S^ n)) [ S.base ] ≃〈 Loop-Trunc0 n 〉
                    τ₀ (Loop n (S^ n) S.base) ≃〈 id 〉
                    π n (S^ n) S.base ∎

  πnSⁿ-is-Z : ∀ n → π n (S^ n) S.base ≃ Int
  πnSⁿ-is-Z One = (τ₀Int-is-Int ∘ ap τ₀ (Ω₁[S¹]≃Int)) ∘ ap τ₀ (ap-Loop≃ One (! S.S¹-is-S^One.path) (ap≃ (type≃β! S.S¹-is-S^One.eqv)))
  πnSⁿ-is-Z (S n) = πnSⁿ-is-Z n ∘ πnSⁿ-diagonal n

  -- πn(S^ n) = τ₀(Ω^n S^ n) = Ω^n-1(τ^n-1 (Ω(S^n)))
  -- πn-1(S^ n-1) = Ω^n-1(τ^n-1 (S^ n -1))
  -- so STS τ^n-1 (Ω(S^n)) = τ^n-1 (S^ n -1)
  -- so STS τ^n (Ω(S^n+1)) = τ^n (S^ n)
