{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open Paths

module applications.JFromSubst where

  j-subst : {A : Set} {M : A} (C : (x : A) -> Id M x -> Set)
       -> {N : A} -> (P : Id M N)
       -> (C M Refl)
       -> C N P
  j-subst {A}{M}C {N} α = 
    subst (\ (p : Σ \ y -> Id M y) -> C (fst p) (snd p))
          (pair≃ α (subst-Id-post α Refl))

  
  j-subst-compute : {A : Set} {M : A} (C : (x : A) -> Id M x -> Set)
       -> (M0 : C M Refl)
       -> j-subst C Refl M0 ≃ M0
  j-subst-compute {A}{M} C M0 = 
    subst (λ (p : Σ (λ y → Id M y)) → C (fst p) (snd p))
          (pair≃ Refl (subst-Id-post Refl Refl)) M0           ≃〈 Refl 〉 -- subst-Id-post Refl Refl ≡ Refl
    subst (λ (p : Σ (λ y → Id M y)) → C (fst p) (snd p)) 
          (pair≃ Refl Refl) M0                                ≃〈 Refl 〉 -- pair≃ Refl Refl ≃ Refl
    subst (λ (p : Σ (λ y → Id M y)) → C (fst p) (snd p)) 
          Refl M0                                             ≃〈 Refl 〉
    M0 ∎ 

  
       

       