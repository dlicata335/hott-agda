-- typing and propositional-ish equality defined mutually recursively intrinsically

{-# OPTIONS --type-in-type #-}

open import lib.Prelude
open ListM

module misc.SubstMutual2 where

  data Tp : Set where
    i  : Tp
    r+ : Tp
    _⊃_ : Tp → Tp → Tp

  Ctx = List Tp

  mutual
    data _⊢_ (Γ : Ctx) : Tp → Set where
      v   : ∀ {A} → A ∈ Γ → Γ ⊢ A
      app : ∀ {A B} → Γ ⊢ (A ⊃ B) → Γ ⊢ A → Γ ⊢ B
      lam : ∀ {A B} → (A :: Γ) ⊢ B → Γ ⊢ (A ⊃ B)
      irec : ∀ {A} (M N : Γ ⊢ A) → M ≡ N → Γ ⊢ i → Γ ⊢ A
      iz    : Γ ⊢ i
      io    : Γ ⊢ i
      rz    : Γ ⊢ r+
      rs    : Γ ⊢ r+ → Γ ⊢ r+
      rrec  : ∀ {A} → (b : Γ ⊢ A) → (s : Γ ⊢ (r+ ⊃ (A ⊃ A))) → b ≡ app (app s rz) b → Γ ⊢ r+ → Γ ⊢ A

    _⊢s_ : Ctx → Ctx → Set
    Γ ⊢s Γ' = {A : Tp} → A ∈ Γ' → Γ ⊢ A

    data _≡_ : ∀ {Γ A} → (M N : Γ ⊢ A) → Set where
      refl : ∀ {Γ A} {M : Γ ⊢ A} → M ≡ M
      trans : ∀ {Γ A} {M1 M2 M3 : Γ ⊢ A} → M1 ≡ M2 → M2 ≡ M3 → M1 ≡ M3
      sym    : ∀ {Γ A} {M1 M2 : Γ ⊢ A} → M1 ≡ M2 → M2 ≡ M1
      ⊃β     : ∀ {Γ A B} {M : (A :: Γ) ⊢ B} {N} → (app (lam M) N) ≡ subst (pair 1s N) M
      rencong  : ∀ {Γ Γ' A} → (ρ : Γ ⊢r Γ') {M N : Γ' ⊢ A} (D : M ≡ N) → ren ρ M ≡ ren ρ N 
      substcong  : ∀ {Γ Γ' A} → (θ : Γ ⊢s Γ') {M N : Γ' ⊢ A} (D : M ≡ N) → subst θ M ≡ subst θ N 
      substcong2 : ∀ {Γ Γ' A} → (θ θ' : Γ ⊢s Γ') {M : Γ' ⊢ A} 
                   → ({A' : Tp} → (x : A ∈ Γ') → θ x ≡ θ' x)
                   → subst θ M ≡ subst θ' M 
      subst-· : ∀ {Γ1 Γ2 Γ3 A} → (θ1 : Γ1 ⊢s Γ2) (θ2 : Γ2 ⊢s Γ3) {M : Γ3 ⊢ A} 
                   → subst θ1 (subst θ2 M) ≡ subst (θ1 ·ss θ2) M 
      iβ1        : ∀ {Γ A} {M N : Γ ⊢ A} {D : M ≡ N} → irec M N D iz ≡ M
      iβ2        : ∀ {Γ A} {M N : Γ ⊢ A} {D : M ≡ N} → irec M N D io ≡ N
      segm       : ∀ {Γ} → iz{Γ} ≡ io
      segr+      : ∀ {Γ} → rz ≡ rs{Γ} rz

    _⊢r_ : Ctx → Ctx → Set
    Γ ⊢r Γ' = {A : Tp} → A ∈ Γ' → A ∈ Γ

    1s : ∀ {Γ} → Γ ⊢s Γ
    1s = v

    pair : ∀ {Γ Γ' A} → Γ ⊢s Γ' → Γ ⊢ A → Γ ⊢s (A :: Γ')
    pair θ M i0 = M
    pair θ M (iS x) = θ x
    
    ren-parallel : ∀ {Γ Γ' A} → Γ ⊢r Γ' → (A :: Γ) ⊢r (A :: Γ')
    ren-parallel ρ i0 = i0
    ren-parallel ρ (iS x) = iS (ρ x)

    p : ∀ {Γ A} → (A :: Γ) ⊢r Γ
    p = iS

    ren : ∀ {Γ Γ' A} → Γ ⊢r Γ' → Γ' ⊢ A → Γ ⊢ A
    ren ρ (v x) = v (ρ x)
    ren ρ (app M M₁) = app (ren ρ M) (ren ρ M₁)
    ren ρ (lam M) = lam (ren (ren-parallel ρ) M)
    ren ρ (irec M N D P) = irec (ren ρ M) (ren ρ N) (rencong ρ D) (ren ρ P)
    ren ρ iz = iz
    ren ρ io = io
    ren ρ rz = rz
    ren ρ (rs M) = rs (ren ρ M)
    ren ρ (rrec b s D M) = rrec (ren ρ b) (ren ρ s) (rencong ρ D) (ren ρ M) 

    _·rs_ : ∀ {Γ Γ' Γ''} → Γ ⊢r Γ' → Γ' ⊢s Γ'' → Γ ⊢s Γ''
    ρ ·rs θ = λ x → ren ρ (θ x)

    subst : ∀ {Γ Γ' A} → Γ ⊢s Γ' → Γ' ⊢ A → Γ ⊢ A
    subst θ (v x) = θ x
    subst θ (app M M₁) = app (subst θ M) (subst θ M₁)
    subst θ (lam M) = lam (subst (pair (p ·rs θ) (v i0)) M)
    subst θ (irec M N D P) = irec (subst θ M) (subst θ N) (substcong θ D) (subst θ P)
    subst θ iz = iz
    subst θ io = io
    subst θ rz = rz
    subst θ (rs M) = rs (subst θ M)
    subst θ (rrec b s D M) = rrec (subst θ b) (subst θ s) (substcong θ D) (subst θ M) 

    _·ss_ : ∀ {Γ Γ' Γ''} → Γ ⊢s Γ' → Γ' ⊢s Γ'' → Γ ⊢s Γ''
    θ1 ·ss θ2 = λ x → subst θ1 (θ2 x)

  flip : [] ⊢ (i ⊃ i)
  flip = lam (irec io iz (sym segm) (v i0))

  test : app flip iz ≡ io
  test = trans ⊃β iβ1
