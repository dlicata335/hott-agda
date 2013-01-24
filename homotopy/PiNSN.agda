{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open Truncation
open Int
open Paths

module homotopy.PiNSN where

  module S = NSphere1
  open S using (S^ ; S-rec; S-elim)
       
  -- πn(S^ n) = τ₀(Ω^n S^ n) = Ω^n-1(τ^n-1 (Ω(S^n))) 
  -- πn-1(S^ n-1) = Ω^n-1(τ^n-1 (S^ n -1))
  -- so STS τ^n-1 (Ω(S^n)) = τ^n-1 (S^ n -1)
  -- so STS τ^n (Ω(S^n+1)) = τ^n (S^ n)

  promote : ∀ {n} → (S^ n) → (Path{S^ (S n)} S.base S.base)
  promote{n} = S-rec id (coe (LoopPath{n}) (S.loop (S n)))

  decode' : ∀ {n} → Trunc (tlp n) (S^ n) → Trunc (tlp n) (Path{S^ (S n)} S.base S.base)
  decode'{n} = Trunc-func (promote{n})

  P : {n : Positive} → S^ (S n) → Type
  P {n} x = Trunc (tlp n) (Path{S^ (S n)} S.base x)

  S-loops : ∀ n -> (x : Trunc (tlp n) (S^ n)) → Loop n (Trunc (tlp n) (S^ n)) x
  S-loops n = Trunc-elim (\ x ->  Loop n (Trunc (tlp n) (S^ n)) x)
                         (λ x → IsNTrunc-Loop n Trunc-is)
                         (S-elim {n} (λ x → Loop n (Trunc (tlp n) (S^ n)) [ x ])
                                     (ap^ n [_] (S.loop n)) 
                                     (preserves n))
          where
            preserves : ∀ n → LoopOver n (S.loop n) (λ x → Loop n (Trunc (tlp n) (S^ n)) [ x ]) (ap^ n [_] (S.loop n))
            preserves One = (transport (λ x → Loop One (Trunc (tlp One) (S^ One)) [ x ]) (S.loop One) (ap^ One [_] (S.loop One))) ≃〈 ap≃ (transport-ap-assoc' (λ x → Path {Trunc (tlp One) (S^ One)} x x) [_] (S.loop One)) 〉
                            (transport (λ x → Path {Trunc (tlp One) (S^ One)} x x) (ap [_] (S.loop One)) (ap [_] (S.loop One))) ≃〈 transport-Path (λ x → x) (λ x → x) (ap [_] (S.loop One)) (ap [_] (S.loop One)) 〉
                            (ap (λ x → x) (ap [_] (S.loop One)) ∘ (ap [_] (S.loop One)) ∘ ! (ap (λ x → x) (ap [_] (S.loop One)))) ≃〈 ap (λ z → z ∘ (ap [_] (S.loop One)) ∘ ! z) (ap-id (ap [_] (S.loop One))) 〉
                            ((ap [_] (S.loop One)) ∘ (ap [_] (S.loop One)) ∘ (! (ap [_] (S.loop One)))) ≃〈 ap (λ z → ap [_] (S.loop One) ∘ z) (!-inv-r (ap [_] (S.loop One))) 〉
                            (ap [_] (S.loop One))∎
            preserves (S n) = HProp-unique (IsTrunc-LoopOver n (S -2) (id^ n) (λ x → HSet-Loop (S n) Trunc-is)) _ _
                   
  endo : ∀ n -> Loop (S n) Type (Trunc (tlp n) (S^ n))
  endo n = λt n (S-loops n)

  Codes : ∀ n -> (S^ (S n)) → Type
  Codes n = S-rec (Trunc (tlp n) (S^ n)) (endo n)

  IsTrunc-Codes : ∀ n x → IsTrunc (tlp n) (Codes n x)
  IsTrunc-Codes n = S-elim (\ x -> IsTrunc (tlp n) (Codes n x))
                           Trunc-is
                           (HProp-unique (IsTrunc-LoopOver n (S -2) (id^ n) (λ x → increment-IsTrunc (IsTrunc-is-HProp _)))
                                         _ _)

  demote : {n : _} {x : S^ (S n)} → Path S.base x → Codes n x
  demote {n} = (\ α → coe (ap (Codes n) α) [ S.base ])

  encode : {n : _} {x : S^ (S n)} → P x → Codes n x
  encode {n} {x} tα = Trunc-rec (IsTrunc-Codes n x) 
                                demote
                                tα

  encode-decode' : {n : _} 
                  → (c : Codes n S.base)
                  → encode (decode' c) ≃ c
  encode-decode'{n} = Trunc-elim (\ c -> encode (decode' c) ≃ c) 
                                 (λ x → IsTrunc-Path _ Trunc-is _ _) 
                                 (S-elim (λ c' → encode (decode' [ c' ]) ≃ [ c' ]) 
                                         id
                                         (resp n)) where
    resp : ∀ n → LoopOver n (S.loop n) (λ c' → encode (decode' [ c' ]) ≃ [ c' ]) id
    resp n = coe (LoopPathOver n (S.loop n) (encode o decode' o [_]) [_] id) 
                 (rebase n id (ap^ n (encode o decode' o [_]) (S.loop n)) ≃〈 ap≃ (rebase-idpath n) 〉
                  ap^ n (encode o decode' o [_]) (S.loop n)             ≃〈 id 〉 
                  ap^ n (demote o promote) (S.loop n)                   ≃〈 ap^-o n demote promote (S.loop n) 〉
                  ap^ n demote (ap^ n promote (S.loop n))               ≃〈 ap (ap^ n demote) (S.βloop/rec n id (coe (LoopPath{n}) (S.loop (S n)))) 〉
                  ap^ n demote (coe (LoopPath{n}) (S.loop (S n)))       ≃〈 id 〉
                  ap^ n (\ x -> coe (ap (Codes n) x) [ S.base ]) (coe (LoopPath{n}) (S.loop (S n)))  ≃〈 id 〉
                  ap^ n ((\ x -> coe x [ S.base ]) o (ap (Codes n))) (coe (LoopPath{n}) (S.loop (S n)))  ≃〈 ap^-o n (λ x → coe x [ S.base ]) (ap (Codes n)) (coe (LoopPath {n}) (S.loop (S n))) 〉
                  -- ENH: define ap^-ap-assoc' that does the next two steps
                  ap^ n (\ x -> coe x [ S.base ]) (ap^ n (ap (Codes n)) (coe (LoopPath{n}) (S.loop (S n))))  ≃〈 ap (ap^ n (λ x → coe x [ S.base ])) (ap^-ap-assoc n (Codes n) (coe (LoopPath {n}) (S.loop (S n)))) 〉 
                  ap^ n (\ x -> coe x [ S.base ]) (coe (LoopPath{n}) 
                    (ap^ (S n) (Codes n) 
                      (coe (! (LoopPath{n})) 
                           (coe (LoopPath{n}) 
                                (S.loop (S n))))))  ≃〈 ap (λ x → ap^ n (λ x' → coe x' [ S.base ]) (coe (LoopPath {n}) (ap^ (S n) (Codes n) x))) (coe-inv-1 (LoopPath {n}) {S.loop (S n)}) 〉 
                  ap^ n (\ x -> coe x [ S.base ]) (coe (LoopPath{n}) 
                    (ap^ (S n) (Codes n) 
                                (S.loop (S n))))  ≃〈 ! (apt-def n (ap^ (S n) (Codes n) (S.loop (S n))) [ S.base ]) 〉 
                  apt n (ap^ (S n) (Codes n) (S.loop (S n))) [ S.base ]           ≃〈 ap (λ x → apt n x [ S.base ]) (S.βloop/rec (S n) (Trunc (tlp n) (S^ n)) (endo n)) 〉
                  apt n (λt n (S-loops n)) [ S.base ]                             ≃〈 ap≃ (coe-inv-1 (LoopSType n)) 〉
                  ap^ n [_] (S.loop n) ∎)

  decode : {n : _} {x : S^ (S n)} → Codes n x → P x 
  decode {n} {x} = S-elim (λ x' → Codes n x' → P x') 
                          decode'
                          (pl{n})
                          x 
   where 
     pl : ∀ {n} → LoopOver (S n) (S.loop (S n)) (λ x' → Codes n x' → P x') decode'
     pl {n} = coe (Loop→OverS n (S.loop (S n)) {Codes n} {P} decode') 
                  (ap (λl n) (λ≃ STS0)) -- move-right for ∘^n
        where 
         STS0 : (x' : _) →
                        ∘^ n (apt n (ap^ (S n) P (S.loop (S n))) (decode' x'))
                             (ap^ n decode' (apt n (!^ (S n) (ap^ (S n) (Codes n) (S.loop (S n)))) x'))
                        ≃ id^ n
         STS0 x' = ∘^-inv-l≃ n (STS1 x') where
          STS1 : (x' : _) →
                        (apt n (ap^ (S n) P (S.loop (S n))) (decode' x'))
                      ≃ (!^ n (ap^ n decode' (apt n (!^ (S n) (ap^ (S n) (Codes n) (S.loop (S n)))) x')))
          STS1 x' = 
                  (apt n (ap^ (S n) P (S.loop (S n))) (decode' x')) ≃〈 ap (λ x0 → apt n x0 (decode' x')) (ap^TruncPathPost n (S.loop (S n)) _) 〉 
                  (apt n (λt n (Trunc-elim (λ tβ → Loop n (Trunc (tlp n) (Path _ _)) tβ) 
                                           (λ _ → IsNTrunc-Loop n Trunc-is) 
                                           (λ β → ap^ n [_]
                                                    (rebase n (∘-unit-l β)
                                                    (ap^ n (λ x → x ∘ β) (coe (LoopPath {n}) (S.loop (S n))))))))
                              (decode' x')) ≃〈 ap≃ (coe-inv-1 (LoopSType n)) {decode' x'} 〉
                  ((Trunc-elim (λ tβ → Loop n (Trunc (tlp n) (Path _ _)) tβ) 
                                               (λ _ → IsNTrunc-Loop n Trunc-is) 
                                               (λ β → ap^ n [_]
                                                    (rebase n (∘-unit-l β)
                                                    (ap^ n (λ x → x ∘ β) (coe (LoopPath {n}) (S.loop (S n)))))))
                   (decode' x')) ≃〈 STS2 x' 〉 
                  (ap^ n decode' (S-loops n x')) ≃〈 ! (ap (ap^ n decode') (ap≃ (coe-inv-1 (LoopSType n)) {x'})) 〉 
                  -- start expanding back to the other side
                  (ap^ n decode' (apt n (λt n (S-loops n)) x')) ≃〈 ! (ap (λ x0 → ap^ n decode' (apt n x0 x')) (S.βloop/rec (S n) (Trunc (tlp n) (S^ n)) (endo n))) 〉 
                  (ap^ n decode' (apt n (ap^ (S n) (Codes n) (S.loop (S n))) x')) ≃〈 ! (!^-invol n (ap^ n decode' (apt n (ap^ (S n) (Codes n) (S.loop (S n))) x'))) 〉 
                  !^ n (!^ n (ap^ n decode' (apt n (ap^ (S n) (Codes n) (S.loop (S n))) x'))) ≃〈 ap (!^ n) (! (ap^-! n decode' (apt n (ap^ (S n) (Codes n) (S.loop (S n))) x'))) 〉 
                  (!^ n (ap^ n decode' (!^ n (apt n (ap^ (S n) (Codes n) (S.loop (S n))) x')))) ≃〈 ap (λ x0 → !^ n (ap^ n decode' x0)) (! (apt-! n (ap^ (S n) (Codes n) (S.loop (S n))) x')) 〉 
                  (!^ n (ap^ n decode' (apt n (!^ (S n) (ap^ (S n) (Codes n) (S.loop (S n)))) x')))
                  ∎ where
             STS2 : (x' : _) → ((Trunc-elim (λ tβ → Loop n (Trunc (tlp n) (Path _ _)) tβ) 
                                                (λ _ → IsNTrunc-Loop n Trunc-is) 
                                                (λ β → ap^ n [_]
                                                     (rebase n (∘-unit-l β)
                                                     (ap^ n (λ x → x ∘ β) (coe (LoopPath {n}) (S.loop (S n)))))))
                               (decode' x'))
                             ≃ (ap^ n decode' (S-loops n x'))
             STS2 = Trunc-elim _ (λ _ → IsTrunc-Path _ (IsNTrunc-Loop n Trunc-is) _ _)
                                 (λ x0 → ! (STS3 x0)) where
              STS3 : (s : _) → (ap^ n decode' (S-loops n [ s ]))
                               ≃ (ap^ n [_]
                                   (rebase n (∘-unit-l (promote s))
                                   (ap^ n (λ x → x ∘ (promote s)) (coe (LoopPath {n}) (S.loop (S n))))))
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
                                (coe (LoopPath {n}) (S.loop (S n))))) ∎)
                    (fst (use-trunc (IsTrunc-LoopOver n -2 (S.loop n) (λ x → use-trunc (HSet-Loop n Trunc-is) _ _)))) 
                 where
                  STS4 : (ap^ n promote (S.loop n)) ≃
                         (rebase n (∘-unit-l (promote S.base))
                                (ap^ n (λ x0 → x0 ∘ promote S.base)
                                (coe (LoopPath {n}) (S.loop (S n))))) 
                  STS4 = (ap^ n promote (S.loop n)) ≃〈 S.βloop/rec n id (coe (LoopPath {n}) (S.loop (S n))) 〉 
                         (coe (LoopPath{n}) (S.loop (S n))) ≃〈 ! (ap^-idfunc n (coe (LoopPath {n}) (S.loop (S n)))) 〉
                         -- start expanding back to the other side
                         (ap^ n (λ x0 → x0 ∘ id)
                                (coe (LoopPath {n}) (S.loop (S n)))) ≃〈 id 〉 
                         (ap^ n (λ x0 → x0 ∘ promote S.base)
                                (coe (LoopPath {n}) (S.loop (S n)))) ≃〈 ap≃ (! (rebase-idpath n)) 〉 
                         (rebase n id
                                    (ap^ n (λ x0 → x0 ∘ promote S.base)
                                    (coe (LoopPath {n}) (S.loop (S n))))) ≃〈 id 〉 
                         (rebase n (∘-unit-l (promote S.base))
                                    (ap^ n (λ x0 → x0 ∘ promote S.base)
                                    (coe (LoopPath {n}) (S.loop (S n))))) ∎

  decode-encode : {n : _} {x : S^ (S n)} (α : P x) → decode{n}{x} (encode{n}{x} α) ≃ α
  decode-encode {n}{x} = Trunc-elim _ (λ x' → IsTrunc-Path _ Trunc-is _ _) 
                                      case-for-[] where
    case-for-[] : {x : S^ (S n)} (α : Path S.base x) → decode{n}{x} (encode{n}{x} [ α ]) ≃ [ α ]
    case-for-[] = path-induction (λ x α → decode{n}{x} (encode{n}{x} [ α ]) ≃ [ α ]) id

  τn[Ω[S^n+1]]-is-τn[S^n] : ∀ {n} → Trunc (tlp n) (Path{S^ (S n)} S.base S.base)
                                  ≃ Trunc (tlp n) (S^ n)
  τn[Ω[S^n+1]]-is-τn[S^n] = (ua (improve (hequiv encode decode decode-encode encode-decode')))