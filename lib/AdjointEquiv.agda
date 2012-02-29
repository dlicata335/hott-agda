{-# OPTIONS --type-in-type --without-K #-}

open import lib.Paths 
open import lib.Prods
open Paths

module lib.AdjointEquiv where

  -- FIXME: clean up the notation here

  record IsAEq {A B : Set} (f : A -> B) : Set where
    constructor isadj
    field
      g  : B -> A
      α : (y : _) -> Id (f (g y)) y
      β : (x : _) -> Id (g (f x)) x
      γ : (x : _) → Id (α (f x)) (resp f (β x))

  AEq : Set -> Set -> Set 
  AEq A B = Σ \ (f : A -> B) -> IsAEq f

  _·⊢_ : ∀ {A B} -> AEq A B -> A -> B
  _·⊢_ = fst

  _·⊣_ : ∀ {A B} -> AEq A B -> B -> A
  (_ , isadj g _ _ _) ·⊣ x = g x

  record IsIso {A B : Set} (f : A -> B) : Set where
    constructor isiso
    field
      g  : B -> A
      α : (y : _) -> Id (f (g y)) y
      β : (x : _) -> Id (g (f x)) x

  Iso : Set -> Set -> Set 
  Iso A B = Σ \ (f : A -> B) -> IsIso f

  isoToAdj : ∀ {A B} -> Iso A B -> AEq A B
  isoToAdj (f , isiso g α β) = (f , isadj g α β improve) where
    postulate improve : _ 
  
  id⊣ : ∀ {A} -> AEq A A
  id⊣ = ( (\ x -> x) , isadj (λ x → x) (\ _ -> Refl) (\ _ -> Refl) (\ _ -> Refl))

  comp : ∀ {A B C} -> AEq A B -> AEq B C -> AEq A C
  comp a1 a2 = (λ x → a2 ·⊢ (a1 ·⊢ x)) , isadj (λ y → a1 ·⊣ (a2 ·⊣ y)) FIXME1 FIXME2 FIXME3 where
    postulate 
      FIXME1 : _
      FIXME2 : _
      FIXME3 : _

