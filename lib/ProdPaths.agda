
{-# OPTIONS --type-in-type --without-K #-}

open import lib.Paths
open Paths
open import lib.Prods 
open import lib.AdjointEquiv 

module lib.ProdPaths where

  Σ≃Iso : {A : Set} {B : A -> Set} {M N : Σ B}
        -> Iso (Σ \ (α : Id (fst M) (fst N)) -> 
                    Id (subst B α (snd M)) (snd N))
               (Id M N) 
  Σ≃Iso = (λ x → pair≃ (fst x) (snd x)) , isiso (λ α → fst≃ α , snd≃ α) {!!} {!!}


