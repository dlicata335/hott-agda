{-# OPTIONS --type-in-type --without-K #-}

open import lib.Paths 
open Paths

module lib.Functions where 

  _o_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
  g o f = \ x -> g (f x)

  app≃ : ∀ {A} {B : A -> Set} {f g : (x : A) -> B x} -> Id f g -> ({x : A} -> Id (f x) (g x))
  app≃ α {x} = resp (\ f -> f x) α

  postulate 
    λ≃ : ∀ {A} {B : A -> Set} {f g : (x : A) -> B x} -> ((x : A) -> Id (f x) (g x)) -> Id f g
    -- FIXME computation rule

  app≃2 : ∀ {A} {B : A -> Set} {f g : (x : A) -> B x} -> Id f g -> ({x y : A} -> (α : Id x y) -> Id (subst B α (f x)) (g y))
  app≃2 {A} {B} {f} {.f} Refl Refl = Refl 

  subst-→ : ∀ {Γ} (A B : Γ -> Set) {θ1 θ2 : Γ} (δ : θ1 ≃ θ2) (f : (A θ1) -> B θ1) 
           -> subst (\ γ -> (A γ) -> B γ) δ f ≃ (\ y -> subst B δ (f (subst A (! δ) y)))
  subst-→ _ _ Refl f = Refl 