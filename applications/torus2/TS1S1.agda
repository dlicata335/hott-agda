{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open Paths
open S¹
open T
open NDPair
open import applications.torus2.TS1S1-helpers


module applications.torus2.TS1S1 where

  -- Associativity proof for dependent sums
  dep-sum-assoc : {X : Set} 
                -> (Σe (Σe X (\ x → Id x x)) (\ p → Id p p))
                -> Σe X (λ x → Σe (Id x x) (λ l1 → Id (x , l1) (x , l1)))
  dep-sum-assoc ((fst , snd) , snd') = fst , snd , snd'

  dep-sum-unassoc : {X : Set}
                 -> Σe X (λ x → Σe (Id x x) (λ l1 → Id (x , l1) (x , l1)))
                 -> (Σe (Σe X (\ x → Id x x)) (\ p → Id p p))
  dep-sum-unassoc (fst , fst' , snd) = (fst , fst') , snd

  dep-sum-assoc-equiv : {X : Set}
                      -> (Σe (Σe X (\ x → Id x x)) (\ p → Id p p))
                      ≃ Σe X (λ x → Σe (Id x x) (λ l1 → Id (x , l1) (x , l1)))
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
    (S¹ -> Σe X (\ x → Id x x))
           -- Same step as above
           ≃〈 circle-X-rec 〉
    Σe (Σe X (\ x → Id x x)) (\ p → Id p p)
           -- Associativity of dependent sums
           ≃〈 dep-sum-assoc-equiv 〉
    Σe X (λ x → Σe (Id x x) (λ l1 → Id (x , l1) (x , l1)))
           ≃〈 {!!} 〉
    Σe X (λ x → Σe (Id x x) (λ l1 → Σe (Id x x) (λ l2 → Id (subst (λ x → Id x x) l2 l1) l1)))
           ≃〈 {!!} 〉
    Σe X (λ x → Σe (Id x x) (λ l1 → Σe (Id x x) (λ l2 → Id (l2 ∘ l1 ∘ (! l1)) l1)))
           ≃〈 {!!} 〉
    Σe X (λ x → Σe (Id x x) (λ l1 → Σe (Id x x) (λ l2 → Id (l2 ∘ l1) (l1 ∘ l2))))
           ≃〈 {!!} 〉
    Refl {_} {T → X})