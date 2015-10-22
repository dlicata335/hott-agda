{-# OPTIONS --type-in-type --without-K #-}

-- FIXME prune imports

open import lib.Prelude
open import lib.cubical.Cubical

module lib.REquiv where

  record REquiv (A0 A1 : Type) : Type where
    constructor requiv
    field
      _~_  : A0 → A1 → Type
      total1 : (a0 : A0) → Contractible (Σ \ (a1 : A1) → a0 ~ a1)
      total2 : (a1 : A1) → Contractible (Σ \ (a0 : A0) → a0 ~ a1)

  record IsREquiv {A0 A1 : Type} (f : A0 → A1) : Type where
    constructor requiv
    field
      _~_  : A0 → A1 → Type
      g    : A1 → A0
      het0 : (x : A0) → x ~ f x
      het1 : (y : A1) → g y ~ y
      hom0 : ∀ {x y} → x ~ y → x == g y
      hom1 : ∀ {x y} → x ~ y → f x == y
      homhet0 : ∀ {x y} {e : x ~ y} → PathOver (λ z → z ~ y) (hom0 e) e (het1 y)
      homhet1 : ∀ {x y} {e : x ~ y} → PathOver (λ z → x ~ z) (hom1 e) (het0 x) e

  IsREquiv' : {A0 A1 : Type} (f : A0 → A1) → Set
  IsREquiv' {A0}{A1} f = Σ (λ (R : A0 → A1 → Set) → (x : A0) (y : A1) → Equiv (R x y) (Id (f x) y))

  module IsREquiv-IsREquiv' {A0 A1 : Type} (f : A0 → A1) where
    het0' : (R : IsREquiv f) {x : A0} {y : A1} → Id (f x) y → IsREquiv._~_ R x y
    het0' R id = IsREquiv.het0 R _
    
    to : IsREquiv f → IsREquiv' f
    to (requiv _~_ g het0 het1 hom0 hom1 homhet0 homhet1) = _~_ , (λ x y → hom1 , (isequiv (het0' (requiv _~_ g het0 het1 hom0 hom1 homhet0 homhet1)) {!!} {!!} {!!}))

    from : IsREquiv' f → IsREquiv f
    from (R , f) = requiv R {!!} {!!} {!!} {!!} {!!} {!!} {!!}


  -- FIXME: prove REquiv f == IsEquiv f

  REquiv-to-IsEquiv : ∀ {A0 A1} (f : A0 → A1) → IsREquiv f → IsEquiv f
  REquiv-to-IsEquiv f (requiv _~_ g het0 het1 hom0 hom1 homhet0 homhet1) = isequiv g (λ x → ! (hom0 (het0 x))) (λ x → hom1 (het1 x)) {!!}

  IsEquiv-to-REquiv : ∀ {A0 A1} (f : A0 → A1) → IsEquiv f → IsREquiv f
  IsEquiv-to-REquiv f (isequiv g α β γ) = requiv (λ a0 a1 → f a0 == a1) g (λ _ → id) β (λ p → ap g p ∘ ! (α _)) (λ p → p) {!!} {!!}

  -- compose to the identity?  
  -- or is it easier to show REquiv is a prop directly?  

  record RHEquiv (A0 A1 : Type) : Type where
    constructor requiv
    field
      _~_  : A0 → A1 → Type
      f : A0 → A1
      g    : A1 → A0
      het0 : (x : A0) → x ~ f x
      het1 : (y : A1) → g y ~ y
      hom0 : ∀ {x y} → x ~ y → x == g y
      hom1 : ∀ {x y} → x ~ y → f x == y
  
  rhequiv-to-hequiv : ∀ {A0 A1} → RHEquiv A0 A1 → HEquiv A0 A1
  rhequiv-to-hequiv (requiv _~_ f g het0 het1 hom0 hom1) = hequiv f g (λ x → ! (hom0 (het0 x))) (λ x → hom1 (het1 x))

  hequiv-to-rhequiv : ∀ {A0 A1} → HEquiv A0 A1 → RHEquiv A0 A1
  hequiv-to-rhequiv (f , ishequiv g α β) = requiv (λ a0 a1 → f a0 == a1) f g (λ _ → id) β (λ p → ap g p ∘ ! (α _)) (λ p → p)

  rhequiv-to-hequiv-c1 : ∀ {A0 A1} (h : HEquiv A0 A1) → h == rhequiv-to-hequiv (hequiv-to-rhequiv h)
  rhequiv-to-hequiv-c1 (f , ishequiv g α β) = {!OK!}

  rhequiv-to-hequiv-c2 : ∀ {A0 A1} (r : RHEquiv A0 A1) → r == hequiv-to-rhequiv (rhequiv-to-hequiv r)
  rhequiv-to-hequiv-c2 (requiv _~_ f g het0 het1 hom0 hom1) = {!!}
    -- requires (a0 ~ a1) == (f a0 == a1), which is probably not true for the incoherent definition?
