{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open BoolM 

module HomotopyCanonHSet where

  -- make some syntax to induct over, a la Outrageous but Meaningful Coindcidences
  mutual
    data CanonicalProp : Set where
      unit : CanonicalProp
      void : CanonicalProp
      `∀   : (A : CanonicalProp) (B : ElP A → CanonicalProp) → CanonicalProp
  
    ElP : CanonicalProp → Set
    ElP unit = Unit
    ElP void = Void
    ElP (`∀ A B) = (x : ElP A) → ElP (B x)

  mutual
    data CanonicalSet : Set where
      prop  : CanonicalSet
      proof : CanonicalProp → CanonicalSet
      bool  : CanonicalSet
      Π : (A : CanonicalSet) (B : El A → CanonicalSet) → CanonicalSet
  
    El : CanonicalSet → Set
    El bool = Bool
    El prop = CanonicalProp
    El (proof P) = ElP P
    El (Π A B) = (x : El A) → El (B x)

  mutual
    data CanonicalCtx : Set where
      ·   : CanonicalCtx
      _,_ : (Γ : CanonicalCtx) (A : ElC Γ → CanonicalSet) → CanonicalCtx

    ElC : CanonicalCtx → Set
    ElC · = Unit
    ElC (Γ , A) = Σ \ (θ : ElC Γ) → El (A θ)

  mutual
    data Ty : (Γ : CanonicalCtx) → Set where
      bool : ∀ {Γ} → Ty Γ
      prop : ∀ {Γ} → Ty Γ
      proof : ∀ {Γ} →  Tm Γ prop → Ty Γ
      Π : ∀ {Γ} → (A : Ty Γ) (B : Ty (Γ , interpA A)) → Ty Γ
      w : ∀ {Γ} → (A B : Ty Γ) → Ty (Γ , interpA A)
      subst1 : ∀ {Γ} → {A : Ty Γ} (B : Ty (Γ , interpA A))
             (M : Tm Γ A) → Ty Γ 

    -- work around the mutual scoping rules
    prop' : ∀ {Γ} → Ty Γ
    prop' = prop

    bool' : ∀ {Γ} → Ty Γ
    bool' = bool

    interpA : {Γ : CanonicalCtx} → Ty Γ → (ElC Γ → CanonicalSet)
    interpA (w A B) θ = interpA B (fst θ)
    interpA (subst1 A M) θ = interpA A (θ , interpM M θ)
    interpA bool θ = bool
    interpA prop θ = prop
    interpA (proof P) θ = proof (interpProp P θ)
    interpA (Π A B) θ = Π (interpA A θ) (λ x → interpA B (θ , x))

    interpBool : {Γ : CanonicalCtx} {θ : ElC Γ} → interpA bool' θ == bool
    interpBool = id

    data Tm : (Γ : CanonicalCtx) → Ty Γ → Set where
      REMOVE : ∀ {Γ A} → Tm Γ A
      v    : {Γ : CanonicalCtx} {A : Ty Γ} → Tm (Γ , interpA A) (w A A)
      w    : ∀ {Γ} → {A B : Ty Γ} → Tm Γ B → Tm (Γ , interpA A) (w A B)
      true : ∀ {Γ} → Tm Γ bool
      false : ∀ {Γ} → Tm Γ bool
      if    : ∀ {Γ} {C : Ty (Γ , interpA bool)} → Tm Γ (subst1 C true) → Tm Γ (subst1 C false) → (x : Tm Γ bool) → Tm Γ (subst1 C x)
    
    true' : ∀ {Γ} → Tm Γ bool'
    true' = true

    interpM : {Γ : CanonicalCtx} {A : Ty Γ} → Tm Γ A → (θ : ElC Γ) → El(interpA A θ)
    interpM v (θ , M) = M
    interpM (w M) (θ , _) = interpM M θ
    interpM true _ = True
    interpM false _ = False
    interpM (if{Γ}{C} M1 M2 M) θ with interpM M θ
    ... | True = transport (λ x → El (interpA C (θ , x))) interpTrue (interpM M1 θ)
    ... | False = {!  M2 θ !}
    interpM _ _ = {!!}

    -- work around what's in scope where
    interpProp : {Γ : CanonicalCtx} → Tm Γ prop' → (θ : ElC Γ) → CanonicalProp
    interpProp = interpM

    interpTrue : ∀ {Γ} {θ : ElC Γ} → interpM true' θ == transport El (! interpBool) True
    interpTrue = id