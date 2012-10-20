
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
  Σ≃Iso = (λ x → pair≃ (fst x) (snd x)) , isiso (λ α → fst≃ α , snd≃ α) 
          (λ y → pair≃ (resp fst y) (snd≃ y) 
                       ≃〈 Refl 〉
                 pair≃ (fst≃ y) (snd≃ y)
                       ≃〈 Σ≃η y 〉
                 (y ∎)) 
          (λ x → (resp fst (pair≃ (fst x) (snd x)) , snd≃ (pair≃ (fst x) (snd x)))
                       ≃〈 resp (λ p → p , snd≃ (pair≃ (fst x) (snd x))) 
                               (Σ≃β1 (fst x) (snd x)) 〉
                 (fst x , snd≃ (pair≃ (fst x) (snd x)))
                       ≃〈 resp (λ p → fst x , p) 
                               (Σ≃β2 (fst x) (snd x)) 〉
                 (x ∎))


