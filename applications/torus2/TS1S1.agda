{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open import lib.ProdPaths
open Paths
open S¹
open T
open NDPair
open import applications.torus2.TS1S1-helpers


module applications.torus2.TS1S1 where

  precomp-torus-circles-equiv : {X : Set} -> (T -> X) ≃ (S¹ × S¹ -> X)
  precomp-torus-circles-equiv {X} = sym 
    ((S¹ × S¹ → X)
           -- use isormphism between currying and uncurrying
           ≃〈 curry-iso 〉 
    (S¹ -> (S¹ -> X)) 
           -- S¹ -> X is equivalent to the premises of S¹-rec
           ≃〈 resp (λ t → S¹ → t) circle-X-rec 〉
    (S¹ -> Σ[ x ∶ X ] (Id x x))
           -- Same step as above
           ≃〈 circle-X-rec 〉
    (Σ[ p ∶ (Σ[ x ∶ X ] (Id x x)) ] (Id p p))
           -- Associativity of dependent sums
           ≃〈 dep-sum-assoc-equiv 〉
    (Σ[ x ∶ X ] (Σ[ l1 ∶ Id x x ] (Id (x , l1) (x , l1))))
           -- snd-≃
           ≃〈 Σ-resp (λ≃ (λ x → 
              Σ-resp (λ≃ (λ l1 → 
                     sym (ua (isoToAdj Σ≃Iso)))))) 〉
    (Σ[ x ∶ X ] (Σ[ l1 ∶ Id x x ] (Σ[ l2 ∶ Id x x ] (Id (subst (λ x → Id x x) l2 l1) l1))))
           -- Subst-Id
           ≃〈 Σ-resp (λ≃ (λ x → 
              Σ-resp (λ≃ (λ l1 → 
              Σ-resp (λ≃ (λ l2 → 
                     resp (λ y → Id y l1) 
                          (subst-Id (λ x' → x') (λ x' → x') l2 l1))))))) 〉
    (Σ[ x ∶ X ] (Σ[ l1 ∶ Id x x ] (Σ[ l2 ∶ Id x x ] 
                Id ((resp (λ x → x) l2) ∘ l1 ∘ (! (resp (λ x → x) l2))) l1)))
           ≃〈 Σ-resp (λ≃ (λ x → 
              Σ-resp (λ≃ (λ l1 → 
              Σ-resp (λ≃ (λ l2 → 
                     resp{X} (λ y → Id (y ∘ l1 ∘ ! y) l1) 
                          Refl)))))) 〉
    (Σ[ x ∶ X ] (Σ[ l1 ∶ Id x x ] (Σ[ l2 ∶ Id x x ] Id (l2 ∘ l1 ∘ (! l2)) l1)))
           -- !-to-left
           ≃〈 Σ-resp (λ≃ (λ x → 
              Σ-resp (λ≃ (λ l1 → 
              Σ-resp (λ≃ (λ l2 → 
                     !-left l2 l1 l1)))))) 〉
    (Σ[ x ∶ X ] (Σ[ l1 ∶ Id x x ] (Σ[ l2 ∶ Id x x ] Id (l2 ∘ l1) (l1 ∘ l2))))
           -- Premises of T-rec is equivalent to T -> X
           ≃〈 {!!} 〉
    (T → X) ∎)