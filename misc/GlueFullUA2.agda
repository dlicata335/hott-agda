{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open import lib.cubical.Cubical

module misc.GlueFullUA2 where

  -- read α : A == B as a line in type, and PathOver α as a line as a classifier

  postulate
    -- note: simpler if this is not contravariant
    Glue : ∀ (B : Type) {X : Type} → Equiv B X → B == X

    -- this is the intro and elim for Glue
    unglue-eqv : ∀ {B X} (e : Equiv B X) {b x} → Equiv (PathOver (\ X → X) (Glue B e) b x) (fst e b == x)

  -- proof of full univalence below also uses funext,
  -- so you need to postulate/have that separately (or can it be proved directly from the above 3 axioms?)

  coe-Glue-eqv : ∀ {B X} (e : Equiv B X) {b x} 
     → Equiv (coe (Glue B e) b == x) (fst e b == x)
  coe-Glue-eqv {B} e = (unglue-eqv e) ∘equiv hom-to-over/left-eqv 

  full : ∀ {B X} → IsEquiv {B == X} {Equiv B X} (coe-equiv)
  full = retract-of-Id-is-Id coe-equiv (Glue _) (λ c → pair≃ (composite1 c) (HProp-unique (IsEquiv-HProp _) _ _)) where
        composite1 : ∀ {B} {X} (e : Equiv B X) → coe (Glue B e) == fst e 
        composite1 e = λ≃ (λ x → ! (fst (coe-Glue-eqv e) id))

  VV : ∀ {A B} → IsEquiv {A == B} {Equiv A B} (pathToEquiv)
  VV = transport IsEquiv (λ≃ (λ x → ! (pathToEquiv-is-' x))) full 

  
