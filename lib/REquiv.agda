{-# OPTIONS --type-in-type --without-K #-}

-- FIXME prune imports

open import lib.Prelude
open import lib.cubical.Cubical

module lib.REquiv where

  record REquiv {A0 A1 : Type} (f : A0 → A1) : Type where
    constructor requiv
    field
      _~_  : A0 → A1 → Type
      g    : A1 → A0
      het0 : (x : A0) → x ~ f x
      het1 : (y : A1) → g y ~ y
      hom0 : ∀ {x y} → x ~ y → x == g y
      hom1 : ∀ {x y} → x ~ y → f x == y
      homhet01 : ∀ {x y} (e : x ~ y) → PathOver (\ p → _~_ (fst p) (snd p)) (pair×≃ (hom0 e) (hom1 e)) (het0 x) (het1 y)

  open BoolM

  not : Bool → Bool
  not = (Bool-elim _ False True)

  Not : Bool -> Bool -> Set
  Not = Bool-elim _ (Bool-elim _ Void Unit) (Bool-elim _ Unit Void)

  example : REquiv not
  example = requiv Not
                   not
                   (Bool-elim _ <> <>)
                   (Bool-elim _ <> <>) 
                   (λ {x} {y} →
                        Bool-elim (λ x₁ → (y₁ : Bool) → Not x₁ y₁ → x₁ == not y₁) 
                                  (Bool-elim _ Sums.abort (λ _ → id))
                                  (Bool-elim _ (λ _ → id) Sums.abort) x y) 
                   (λ {x} {y} →
                        Bool-elim (λ x₁ → (y₁ : Bool) → Not x₁ y₁ → not x₁ == y₁)
                        (Bool-elim _ Sums.abort (λ _ → id))
                        (Bool-elim _ (λ _ → id) Sums.abort) x y)
                   sq  where
          sq : {x y : Bool} (e : Not x y) → PathOver (λ p → Not (fst p) (snd p)) (pair×≃ (Bool-elim (λ x₁ → (y₁ : Bool) → Not x₁ y₁ → x₁ == not y₁) (Bool-elim (λ z → Not True z → True == not z) Sums.abort (λ _ → id)) (Bool-elim (λ z → Not False z → False == not z) (λ _ → id) Sums.abort) x y e) (Bool-elim (λ x₁ → (y₁ : Bool) → Not x₁ y₁ → not x₁ == y₁) (Bool-elim (λ z → Not True z → not True == z) Sums.abort (λ _ → id)) (Bool-elim (λ z → Not False z → not False == z) (λ _ → id) Sums.abort) x y e)) (Bool-elim (λ z → Not z (not z)) <> <> x) (Bool-elim (λ z → Not (not z) z) <> <> y)
          sq {True} {True} e = Sums.abort e
          sq {True} {False} e = {!basically id!}
          sq {False} {True} e = {!basically id!}
          sq {False} {False} e = Sums.abort e

  module Foo {A0 A1} (f : A0 → A1) where
    to' : IsEquiv f → REquiv f
    to' (isequiv g α β γ) = record
                             { _~_ = λ a0 a1 → Σ \ (p : (f a0 == a1)) → Σ \ (q : a0 == g a1) → p == β _ ∘ ap f q
                             ; g = g
                             ; het0 = λ x → id , ! (α x) , {!γ!}
                             ; het1 = λ x → β x , α (g x) ∘ ap g (! (β x)) , {!other triangle!}
                             ; hom0 = λ x → fst (snd x)
                             ; hom1 = fst
                             ; homhet01 = {!!}
                             } where 
       sq : ∀ {x y} (e : f x == y) → Square id (ap f (ap g e ∘ (! (α x)))) e (β y)
       sq {x} id = {!γ x!}

    to : IsEquiv f → REquiv f
    to (isequiv g α β γ) = record
                             { _~_ = λ a0 a1 → f a0 == a1
                             ; g = g
                             ; het0 = λ _ → id
                             ; het1 = β
                             ; hom0 = λ e → ap g e ∘ ! (α _)
                             ; hom1 = λ e → e
                             ; homhet01 = λ e → PathOver=.in-PathOver-= (whisker-square id {!!} {!!} id (sq e))
                             } where 
       sq : ∀ {x y} (e : f x == y) → Square id (ap f (ap g e ∘ (! (α x)))) e (β y)
       sq {x} id = {!γ x!}

    from : REquiv f → IsEquiv f
    from (requiv _~_ g het0 het1 hom0 hom1 homhet01) = 
      isequiv g (λ x → ! (hom0 (het0 x))) (λ x → hom1 (het1 x)) (λ x → {!!})

-- Goal: Path (hom1 (het1 (f x))) (ap f (! (hom0 (het0 x))))
-- PathOver (λ p → fst p ~ snd p) (pair×≃ (hom0 (het0 x)) (hom1 (het0 x))) (het0 x) (het1 (f x))
-- Have: PathOver (λ p → fst p ~ snd p)
    --   (pair×≃ (hom0 (het1 (f x))) (hom1 (het1 (f x)))) (het0 (g (f x)))
    --   (het1 (f x))

    to-from : ∀ e → from (to e) == e
    to-from (isequiv g α β γ) = {!!}

    from-to : ∀ e → to (from e) == e
    from-to (requiv _~_ g het0 het1 hom0 hom1 homhet01) = {!!}
