{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open Paths

module applications.JFromSubst where

  j-subst : {A : Set} {M : A} (C : (x : A) -> Id M x -> Set)
       -> {N : A} -> (P : Id M N)
       -> (C M Refl)
       -> C N P
  j-subst {A}{M}C {N} α = 
    subst (\ (p : Σ \ y -> Id M y) -> C (fst p) (snd p)) (pair≃ α (subst-Id-post α Refl))
