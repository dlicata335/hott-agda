{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open Truncation
open Int
open Paths

module homotopy.PiNSN where

  module S = NSphere1
  open S using (S^ ; S-rec)
       
  -- πn(S^ n) = τ₀(Ω^n S^ n) = Ω^n-1(τ^n-1 (Ω(S^n))) 
  -- πn-1(S^ n-1) = Ω^n-1(τ^n-1 (S^ n -1))
  -- so STS τ^n-1 (Ω(S^n)) = τ^n-1 (S^ n -1)
  -- so STS τ^n (Ω(S^n+1)) = τ^n (S^ n)

  {-
  Loop-assoc : ∀ {A n b} → Path {Loop A b n} (id^ _ _ n) (id^ _ _ n) ≃ Loop A b (S n)
  Loop-assoc = {!!}
  -}

  Loop-assoc : ∀ {n A b} 
             → Path {Loop A b n} (id^ n) (id^ n) 
             ≃ Loop (Path b b) id n
  Loop-assoc = {!!}

  promote' : ∀ {n} → (S^ n) → (Path{S^ (S n)} S.base S.base)
  promote'{n} = S-rec id (coe (Loop-assoc{n}) (S.loop (S n)))

  P : {n : Positive} → S^ (S n) → Type
  P {n} x = Trunc (tlp n) (Path{S^ (S n)} S.base x)

  decode' : ∀ {n} → Trunc (tlp n) (S^ n) → P S.base
  decode'{n} = Trunc-func promote'

  endo : ∀ n -> Loop Set (S^ n) (S n)
  endo n = coe (! (Loop-assoc {n})) (coe (! iso) 
               {!S.loop n!}) where
    iso : Loop (S^ n ≃ S^ n) id n 
        ≃ -- Loop (S^ n → S^ n) (\ x -> x) n
          ((x : S^ n) -> Loop (S^ n) x n)
    iso = {!!}

  -- FIXME: needs truncation, but let's see if we're in the ballpark
  Codes : ∀ n -> (S^ (S n)) → Type
  Codes n = S-rec (Trunc (tlp n) (S^ n))
                  {!!}

