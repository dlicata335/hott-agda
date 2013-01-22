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
                                     (trivial-LoopOver n (λ x → IsNTrunc-Loop n Trunc-is)))

  endo : ∀ n -> Loop (S n) Type (Trunc (tlp n) (S^ n))
  endo n = λt n (S-loops n)

  Codes : ∀ n -> (S^ (S n)) → Type
  Codes n = S-rec (Trunc (tlp n) (S^ n)) (endo n)

  IsTrunc-Codes : ∀ n x → IsTrunc (tlp n) (Codes n x)
  IsTrunc-Codes n = S-elim (\ x -> IsTrunc (tlp n) (Codes n x)) 
                           Trunc-is
                           (HProp-unique (LoopOver-HProp n (λ x → IsTrunc-is-PosTrunc {n} _))
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
                  ap^ n (demote o promote) (S.loop n)                   ≃〈 {!ap-o!} 〉
                  ap^ n demote (ap^ n promote (S.loop n))               ≃〈 {!beta for promote!} 〉
                  ap^ n demote (coe (LoopPath{n}) (S.loop (S n)))       ≃〈 id 〉
                  ap^ n (\ x -> coe (ap (Codes n) x) [ S.base ]) (coe (LoopPath{n}) (S.loop (S n)))  ≃〈 id 〉
                  ap^ n ((\ x -> coe x [ S.base ]) o (ap (Codes n))) (coe (LoopPath{n}) (S.loop (S n)))  ≃〈 {!ap^-o!} 〉
                  ap^ n (\ x -> coe x [ S.base ]) (ap^ n (ap (Codes n)) (coe (LoopPath{n}) (S.loop (S n))))  ≃〈 {!ap^-ap-assoc!} 〉 
                  ap^ n (\ x -> coe x [ S.base ]) (coe (LoopPath{n}) (ap^ (S n) (Codes n) (S.loop (S n))))  ≃〈 {!definition of apt!} 〉 -- STATE LEMMA
                  apt n (ap^ (S n) (Codes n) (S.loop (S n))) [ S.base ]           ≃〈 {!β!} 〉
                  apt n (λt n (S-loops n)) [ S.base ]                             ≃〈 {!β!} 〉
                  ap^ n [_] (S.loop n) ∎)

  decode : {n : _} {x : S^ (S n)} → Codes n x → P x 
  decode {n} {x} = S-elim (λ x' → Codes n x' → P x') 
                          decode'
                          (pl{n})
                          x 
   where 
     pl : ∀ {n} → LoopOver (S n) (S.loop (S n)) (λ x' → Codes n x' → P x') decode'
     pl {n} = coe (Loop→OverS n (S.loop (S n)) {Codes n} {P} decode') 
                  (ap (λl n) (λ≃ STS))
        where 
          STS : (x' : _) →
                        ∘^ n (apt n (ap^ (S n) P (S.loop (S n))) (decode' x'))
                             (ap^ n decode' (apt n (!^ (S n) (ap^ (S n) (Codes n) (S.loop (S n)))) x'))
                      ≃ (id^ n)
          STS x' = ∘^ n (apt n (ap^ (S n) P (S.loop (S n))) (decode' x'))
                        (ap^ n decode' (apt n (!^ (S n) (ap^ (S n) (Codes n) (S.loop (S n)))) x')) ≃〈 {!β Codes!} 〉 
                  ∘^ n (apt n (ap^ (S n) P (S.loop (S n))) (decode' x'))
                       (ap^ n decode' (apt n (!^ (S n) (λt n (S-loops n))) x')) ≃〈 {!apt-!!} 〉 
                  ∘^ n (apt n (ap^ (S n) P (S.loop (S n))) (decode' x'))
                       (ap^ n decode' (!^ n (apt n (λt n (S-loops n)) x'))) ≃〈 {!β!} 〉 
                  ∘^ n (apt n (ap^ (S n) P (S.loop (S n))) (decode' x'))
                       (ap^ n decode' (!^ n (S-loops n x'))) ≃〈 {!ap^-!!} 〉
                  ∘^ n (apt n (ap^ (S n) P (S.loop (S n))) (decode' x'))
                       (!^ n (ap^ n decode' (S-loops n x'))) ≃〈 {!ap^TruncPathPost!} 〉 
                  ∘^ n (apt n (λt n (Trunc-elim (λ tβ → Loop n (Trunc (tlp n) (Path _ _)) tβ) 
                                               (λ _ → IsNTrunc-Loop n Trunc-is) 
                                               (λ β → ap^ n [_]
                                                    (rebase n (∘-unit-l β)
                                                    (ap^ n (λ x → x ∘ β) (coe (LoopPath {n}) (S.loop (S n))))))))
                              (decode' x'))
                       (!^ n (ap^ n decode' (S-loops n x'))) ≃〈 {!β!} 〉
                  ∘^ n ((Trunc-elim (λ tβ → Loop n (Trunc (tlp n) (Path _ _)) tβ) 
                                               (λ _ → IsNTrunc-Loop n Trunc-is) 
                                               (λ β → ap^ n [_]
                                                    (rebase n (∘-unit-l β)
                                                    (ap^ n (λ x → x ∘ β) (coe (LoopPath {n}) (S.loop (S n)))))))
                        (decode' x'))
                       (!^ n (ap^ n decode' (S-loops n x'))) ≃〈 {!STS2 and inverses!} 〉 
                  (id^ n) ∎ where
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
                   (ap^ n decode' (S-loops n [ S.base ]) ≃〈 {! S.βloop/rec n (coe (LoopPath {n}) (S.loop (S n))) !} 〉
                    ap^ n decode' (ap^ n [_] (S.loop n)) ≃〈 {!ap^-o!} 〉
                    ap^ n (decode' o [_]) (S.loop n) ≃〈 id 〉
                    ap^ n ([_] o promote) (S.loop n) ≃〈 {!ap^-o!} 〉
                    ap^ n [_] (ap^ n promote (S.loop n)) ≃〈 {!β!} 〉
                    ap^ n [_] (coe (LoopPath{n}) (S.loop (S n))) ≃〈 {!ap^-by-id!} 〉
                    -- start expanding back to the other side
                    ap^ n [_] (ap^ n (λ x0 → x0 ∘ id)
                                     (coe (LoopPath {n}) (S.loop (S n)))) ≃〈 id 〉 
                    ap^ n [_] (ap^ n (λ x0 → x0 ∘ promote S.base)
                                     (coe (LoopPath {n}) (S.loop (S n)))) ≃〈 {!rebase-id!} 〉 
                    ap^ n [_]
                     (rebase n id
                               (ap^ n (λ x0 → x0 ∘ promote S.base)
                               (coe (LoopPath {n}) (S.loop (S n))))) ≃〈 id 〉 
                    ap^ n [_]
                     (rebase n (∘-unit-l (promote S.base))
                               (ap^ n (λ x0 → x0 ∘ promote S.base)
                               (coe (LoopPath {n}) (S.loop (S n))))) ∎)
                   (trivial-LoopOver n (λ x0 → IsTrunc-Path _ (IsNTrunc-Loop n Trunc-is) _ _))

  decode-encode : {n : _} {x : S^ (S n)} (α : P x) → decode{n}{x} (encode{n}{x} α) ≃ α
  decode-encode {n}{x} = Trunc-elim _ (λ x' → IsTrunc-Path _ Trunc-is _ _) 
                                      case-for-[] where
    case-for-[] : {n : _} {x : S^ (S n)} (α : Path S.base x) → decode{n}{x} (encode{n}{x} [ α ]) ≃ [ α ]
    case-for-[] id = id

  τn[Ω[S^n+1]]-is-τn[S^n] : ∀ {n} → Trunc (tlp n) (Path{S^ (S n)} S.base S.base)
                                  ≃ Trunc (tlp n) (S^ n)
  τn[Ω[S^n+1]]-is-τn[S^n] = (ua (improve (hequiv encode decode decode-encode encode-decode')))
   
