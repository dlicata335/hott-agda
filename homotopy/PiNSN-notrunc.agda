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

  P : {n : Positive} → S^ (S n) → Type
  P {n} x = (Path{S^ (S n)} S.base x)

  S-loops : ∀ n -> (x : S^ n) → Loop n (S^ n) x
  S-loops n = (S-elim {n} (λ x → Loop n (S^ n) x) 
                          (S.loop n)
                          NEED_TRUNCATION) where
            postulate 
             NEED_TRUNCATION : _ 
             -- would be a Path in (Loop n (Trunc n (S^ n)) -) between two things,
             -- and therefore high enough to get killed by truncation.  

  endo : ∀ n -> Loop (S n) Type (S^ n)
  endo n = λt n (S-loops n)

  Codes : ∀ n -> (S^ (S n)) → Type
  Codes n = S-rec (S^ n) (endo n)

  encode : {n : _} {x : S^ (S n)} → P x → Codes n x
  encode {n} {x} α = coe (ap (Codes n) α) S.base

  encode-promote : {n : _} 
                  → (c : Codes n S.base)
                  → encode (promote c) ≃ c
  encode-promote{n} c = S-elim (λ c' → encode (promote c') ≃ c') 
                                id
                                (resp n)
                                c where
    resp : ∀ n → LoopOver n (S.loop n) (λ c' → encode (promote c') ≃ c') id
    resp n = coe (LoopPathOver n (S.loop n) (encode o promote) (λ x → x) id) 
                 (rebase n id (ap^ n (encode o promote) (S.loop n)) ≃〈 ap≃ (rebase-idpath n) 〉
                  (ap^ n (encode o promote) (S.loop n))             ≃〈 sts 〉
                  (S.loop n)                                         ≃〈 ! (ap^-idfunc n (S.loop n)) 〉
                  (ap^ n (λ x → x) (S.loop n) ∎))
     where
      sts : ap^ n (encode o promote) (S.loop n) ≃ (S.loop n)
      sts = ap^ n (encode o promote) (S.loop n) ≃〈 {!ap^-o!} 〉 
            ap^ n encode (ap^ n promote (S.loop n)) ≃〈 {!beta for promote!} 〉
            ap^ n encode (coe (LoopPath{n}) (S.loop (S n)))  ≃〈 id 〉
            ap^ n (\ x -> coe (ap (Codes n) x) S.base) (coe (LoopPath{n}) (S.loop (S n)))  ≃〈 id 〉
            ap^ n ((\ x -> coe x S.base) o (ap (Codes n))) (coe (LoopPath{n}) (S.loop (S n)))  ≃〈 {!ap^-o!} 〉
            ap^ n (\ x -> coe x S.base) (ap^ n (ap (Codes n)) (coe (LoopPath{n}) (S.loop (S n))))  ≃〈 {!ap^-ap-assoc!} 〉 
            ap^ n (\ x -> coe x S.base) (coe (LoopPath{n}) (ap^ (S n) (Codes n) (S.loop (S n))))  ≃〈 {!β!} 〉
            ap^ n (\ x -> coe x S.base) (coe (LoopPath{n}) (endo n))  ≃〈 {!inverses!} 〉
            ap^ n (\ x -> coe x S.base) (coe (! (LoopPathType n)) (S-loops n))  ≃〈 id 〉 
            ap^ n ((\ f -> f S.base) o coe) (coe (! (LoopPathType n)) (S-loops n))  ≃〈 {!ap-o!} 〉 
            ap^ n (\ f -> f S.base) (ap^ n coe (coe (! (LoopPathType n)) (S-loops n)))  ≃〈 {!these should be the other sides of LoopPathType!} 〉
            (S-loops n S.base) ≃〈 id 〉
            (S.loop n ∎)
  
  decode : {n : _} {x : S^ (S n)} → Codes n x → P x 
  decode {n} {x} = S-elim (λ x' → Codes n x' → P x') 
                          promote
                          (pl{n})
                          x 
   where 
     pl : ∀ {n} → LoopOver (S n) (S.loop (S n)) (λ x' → Codes n x' → P x') promote
     pl {n} = coe (Loop→OverS n (S.loop (S n)) {Codes n} {P} promote) 
                  (ap (λl n) (λ≃ STS))
        where 
          STS : (x' : _) →
                        ∘^ n (apt n (ap^ (S n) P (S.loop (S n))) (promote x'))
                             (ap^ n promote (apt n (!^ (S n) (ap^ (S n) (Codes n) (S.loop (S n)))) x'))
                      ≃ (id^ n)
          STS x' = ∘^ n (apt n (ap^ (S n) P (S.loop (S n))) (promote x'))
                        (ap^ n promote (apt n (!^ (S n) (ap^ (S n) (Codes n) (S.loop (S n)))) x')) ≃〈 {!β Codes!} 〉 
                  ∘^ n (apt n (ap^ (S n) P (S.loop (S n))) (promote x'))
                       (ap^ n promote (apt n (!^ (S n) (λt n (S-loops n))) x')) ≃〈 {!apt-!!} 〉 
                  ∘^ n (apt n (ap^ (S n) P (S.loop (S n))) (promote x'))
                       (ap^ n promote (!^ n (apt n (λt n (S-loops n)) x'))) ≃〈 {!β!} 〉 
                  ∘^ n (apt n (ap^ (S n) P (S.loop (S n))) (promote x'))
                       (ap^ n promote (!^ n (S-loops n x'))) ≃〈 {!ap^-!!} 〉
                  ∘^ n (apt n (ap^ (S n) P (S.loop (S n))) (promote x'))
                       (!^ n (ap^ n promote (S-loops n x'))) ≃〈 {!ap^PathPost!} 〉 
                  ∘^ n (apt n (λt n (λ β → rebase n (∘-unit-l β)
                               (ap^ n (λ x → x ∘ β) 
                                (coe (LoopPath {n}) (S.loop (S n))))))
                              (promote x'))
                       (!^ n (ap^ n promote (S-loops n x'))) ≃〈 {!β!} 〉 
                  ∘^ n (rebase n (∘-unit-l (promote x'))
                                 (ap^ n (λ x → x ∘ (promote x')) 
                                  (coe (LoopPath {n}) (S.loop (S n)))))
                       (!^ n (ap^ n promote (S-loops n x'))) ≃〈 {!STS2!} 〉 
                  (id^ n) ∎ where
           STS2 : (x' : _) → (ap^ n promote (S-loops n x'))
                           ≃ (rebase n (∘-unit-l (promote x'))
                                       (ap^ n (λ x → x ∘ (promote x')) 
                                             (coe (LoopPath {n}) (S.loop (S n)))))
           STS2 = S-elim _ 
                  (ap^ n promote (S-loops n S.base) ≃〈 id 〉
                   ap^ n promote (S.loop n) ≃〈 {! S.βloop/rec n (coe (LoopPath {n}) (S.loop (S n))) !} 〉
                   (coe (LoopPath{n}) (S.loop (S n))) ≃〈 {!ap^-by-id!} 〉
                   (ap^ n (λ x0 → x0 ∘ id)
                          (coe (LoopPath {n}) (S.loop (S n)))) ≃〈 id 〉 
                   (ap^ n (λ x0 → x0 ∘ promote S.base)
                          (coe (LoopPath {n}) (S.loop (S n)))) ≃〈 {!rebase-id!} 〉 
                   rebase n (∘-unit-l (promote S.base))
                            (ap^ n (λ x0 → x0 ∘ promote S.base)
                              (coe (LoopPath {n}) (S.loop (S n)))) ∎) 
                  FIXME-CHECK-TRUNCATION where
            postulate
                FIXME-CHECK-TRUNCATION : _
                       
  decode-encode : {n : _} {x : S^ (S n)} (α : P x) → decode{n}{x} (encode{n}{x} α) ≃ α
  decode-encode id = id
   