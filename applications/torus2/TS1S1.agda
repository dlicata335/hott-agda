{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open Paths
open S¹
open T
open NDPair
open import applications.torus2.TS1S1-helpers


module applications.torus2.TS1S1 where

  -- Generalized associativity proof for dependent sums
  dep-sum-assoc : {X : Set} 
                -> {A : X -> Set}
                -> {B : (Σ[ x ∶ X ] (A x)) -> Set}
                -> (Σ[ p ∶ (Σ[ x ∶ X ] (A x)) ] (B p))
                -> Σ[ x  ∶ X ] (Σ[ l1 ∶ A x ] (B (x , l1)))
  dep-sum-assoc ((fst , snd) , snd') = fst , (snd , snd')

  dep-sum-unassoc : {X : Set}
                 -> {A : X -> Set}
                 -> {B : (Σ[ x ∶ X ] (A x)) -> Set}
                 -> Σ[ x ∶ X ] (Σ[ l1 ∶ A x ] (B (x , l1)))
                 -> (Σ[ p ∶ (Σ[ x ∶ X ] (A x)) ] (B p))
  dep-sum-unassoc (fst , fst' , snd) = (fst , fst') , snd

  dep-sum-assoc-equiv : {X : Set}
                      -> {A : X -> Set}
                      -> {B : (Σ[ x ∶ X ] (A x)) -> Set}
                      -> (Σ[ p ∶ (Σ[ x ∶ X ] (A x)) ] (B p))
                      ≃ (Σ[ x  ∶ X ] (Σ[ l1 ∶ A x ] (B (x , l1))))
  dep-sum-assoc-equiv = ua (isoToAdj (dep-sum-assoc , 
                                      isiso dep-sum-unassoc 
                                            (λ y → Refl) 
                                            (λ x → Refl)))

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
           -- Id-Σ ?
           ≃〈 {!!} 〉
    (Σ[ x ∶ X ] (Σ[ l1 ∶ Id x x ] (Σ[ l2 ∶ Id x x ] (Id (subst (λ x → Id x x) l2 l1) l1))))
           -- Subst-Id
           ≃〈 {!!} 〉
    (Σ[ x ∶ X ] (Σ[ l1 ∶ Id x x ] (Σ[ l2 ∶ Id x x ] Id (l2 ∘ l1 ∘ (! l2)) l1)))
           -- !-to-left
           ≃〈 {!!} 〉
    (Σ[ x ∶ X ] (Σ[ l1 ∶ Id x x ] (Σ[ l2 ∶ Id x x ] Id (l2 ∘ l1) (l1 ∘ l2))))
           -- Premises of T-rec is equivalent to T -> X
           ≃〈 {!!} 〉
    Refl {_} {T → X})