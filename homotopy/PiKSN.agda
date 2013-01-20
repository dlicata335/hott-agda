{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open Truncation
open Int
open Paths
open Suspension

module homotopy.PiKSN where
       
  Codes : ∀ n -> (S^ (S n)) → Type
  Codes n = Susp-rec Unit Unit (λ _ → id) 

  Codes-is : ∀ {k n x} → IsTrunc k (Codes n x)
  Codes-is = {!!}

  encode : ∀ {k n} {x : S^ (S n)} → Trunc k (Path{S^ (S n)} No x) → Codes n x
  encode {k}{n}{x} tα = 
    Trunc-rec (Codes-is{k}{n}{x}) (λ α → transport (Codes n) α <>) tα

  base : ∀ n → S^ n
  base One   = S¹.base
  base (S n) = No

  decode : ∀ {k n} {x : S^ (S n)} → Codes n x → Trunc k (Path{S^ (S n)} No x) 
  decode{k}{n}{x} = Susp-elim (λ x' → Codes n x' → Trunc k (Path {S^ (S n)} No x')) 
                      (λ _ → [ id ]) 
                      (λ _ → [ mer (base n) ])
                      {!!}
                      x
     {-
     (transport (λ x0 → Codes n x0 → Trunc k (Path No x0)) (mer x')
                (λ z → [ id ]))
     = \ _ -> transport (Trunc k (Path No -)) (mer x') [ id ] 
     = \ x' -> [ mer x' ]
                  

  