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

  {-
  Loop-assoc : ∀ {A n b} → Path {Loop A b n} (id^ _ _ n) (id^ _ _ n) ≃ Loop A b (S n)
  Loop-assoc = {!!}
  -}

  Loop-assoc : ∀ {n A a} 
             → Path {Loop n A a} (id^ n) (id^ n) 
             ≃ Loop n (Path a a) id
  Loop-assoc = {!!}

  promote' : ∀ {n} → (S^ n) → (Path{S^ (S n)} S.base S.base)
  promote'{n} = S-rec id (coe (Loop-assoc{n}) (S.loop (S n)))

  P : {n : Positive} → S^ (S n) → Type
  P {n} x = Trunc (tlp n) (Path{S^ (S n)} S.base x)

  decode' : ∀ {n} → Trunc (tlp n) (S^ n) → P S.base
  decode'{n} = Trunc-func promote'

  postulate 
    LoopPathType : ∀ {n} -> Loop n (S^ n ≃ S^ n) id 
                          ≃ ((x : S^ n) -> Loop n (S^ n) x)

  S-loops : ∀ n -> (x : _) → Loop n (S^ n) x
  S-loops n = (S-elim {n} (λ x → Loop n (S^ n) x) 
                          (S.loop n)
                          {!!})

  endo : ∀ n -> Loop (S n) Set (S^ n)
  endo n = coe (! (Loop-assoc {n})) 
          (coe (! LoopPathType)
               (S-loops n))

  -- FIXME: needs truncation, but let's see if we're in the ballpark
  Codes : ∀ n -> (S^ (S n)) → Type
  Codes n = S-rec (S^ n) (endo n)

  -- FIXME: need truncation
  encode : {n : _} {x : S^ (S n)} → Path{S^ (S n)} S.base x → Codes n x
  encode {n} {x} α = transport (Codes n) α S.base

  encode-promote' : {n : _} 
                  → (c : Codes n S.base)
                  → encode (promote' c) ≃ c
  encode-promote'{n} c = S-elim (λ c' → encode (promote' c') ≃ c') 
                                id
                                (resp n)
                                c where
    resp : ∀ n → LoopOver n (S.loop n) (λ c' → encode (promote' c') ≃ c') id
    resp n = {!!}

    encoden = encode{n}{S.base}
    promote'n = promote'{n}

    sts : ap^ n (encoden o promote'n) (S.loop n) ≃ (S.loop n)
    sts = ap^ n (encoden o promote'n) (S.loop n) ≃〈 {!!} 〉
          ap^ n encoden (ap^ n promote'n (S.loop n)) ≃〈 {!!} 〉
          ap^ n encoden (coe (Loop-assoc{n}) (S.loop (S n)))  ≃〈 {!!} 〉
          ap^ n (\ x -> transport (Codes n) x S.base) (coe (Loop-assoc{n}) (S.loop (S n)))  ≃〈 {!!} 〉
          ap^ n (\ x -> transport (Codes n) x S.base) (coe (Loop-assoc{n}) (S.loop (S n)))  ≃〈 {!!} 〉
          ap^ n (\ x -> coe (ap (Codes n) x) S.base) (coe (Loop-assoc{n}) (S.loop (S n)))  ≃〈 {!!} 〉
          ap^ n ((\ x -> coe x S.base) o (ap (Codes n))) (coe (Loop-assoc{n}) (S.loop (S n)))  ≃〈 {!!} 〉
          ap^ n ((\ x -> coe x S.base) o (ap (Codes n))) (coe (Loop-assoc{n}) (S.loop (S n)))  ≃〈 {!!} 〉
          ap^ n (\ x -> coe x S.base) (ap^ n (ap (Codes n)) (coe (Loop-assoc{n}) (S.loop (S n))))  ≃〈 {!whaaaa????!} 〉
          ap^ n (\ x -> coe x S.base) (coe (Loop-assoc{n}) (ap^ (S n) (Codes n) (S.loop (S n))))  ≃〈 {!!} 〉
          ap^ n (\ x -> coe x S.base) (coe (Loop-assoc{n}) (endo n))  ≃〈 {!!} 〉
          ap^ n (\ x -> coe x S.base) (coe (! LoopPathType) (S-loops n))  ≃〈 {!!} 〉
          (S-loops n S.base) ≃〈 {!!} 〉
          (S.loop n ∎)
  


  -- FIXME: need truncation
  decode : {n : _} {x : S^ (S n)} → Codes n x → Path{S^ (S n)} S.base x 
  decode {n} {x} = S-elim (λ x' → Codes n x' → Path {S^ (S n)} S.base x') 
                          promote'
                          (pl{n})
                          x 
   where 
     pl : ∀ {n} → LoopOver (S n) (S.loop (S n)) (λ x' → Codes n x' → Path {S^ (S n)} S.base x') promote'
     pl = {!!}
