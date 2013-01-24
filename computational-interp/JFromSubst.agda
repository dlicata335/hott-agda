{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open Paths

module computational-interp.JFromSubst where

  j-transport : {A : Set} {M : A} (C : (x : A) -> Path M x -> Set)
       -> {N : A} -> (P : Path M N)
       -> (C M id)
       -> C N P
  j-transport {A}{M}C {N} α = 
    transport (\ (p : Σ \ y -> Path M y) -> C (fst p) (snd p))
          (pair≃ α (transport-Path-right α id))

-- need:
-- Id {Id {A} M N}
--    (transport (λ y → Id {A} M y) α (id {_} {M}))
--    α
  
  j-transport-compute : {A : Set} {M : A} (C : (x : A) -> Path M x -> Set)
       -> (M0 : C M id)
       -> j-transport C id M0 ≃ M0
  j-transport-compute {A}{M} C M0 = 
    transport (λ (p : Σ (λ y → Path M y)) → C (fst p) (snd p))
          (pair≃ id (transport-Path-right id id)) M0           ≃〈 id 〉 -- transport-Path-post id id ≡ id
    transport (λ (p : Σ (λ y → Path M y)) → C (fst p) (snd p)) 
          (pair≃ id id) M0                                ≃〈 id 〉 -- pair≃ id id ≃ id
    transport (λ (p : Σ (λ y → Path M y)) → C (fst p) (snd p)) 
          id M0                                             ≃〈 id 〉
    M0 ∎ 

  
       

       