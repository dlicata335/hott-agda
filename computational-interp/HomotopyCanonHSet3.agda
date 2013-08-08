{-# OPTIONS --type-in-type --without-K --no-termination-check #-}

open import lib.Prelude 
open BoolM 

module HomotopyCanonHSet3 where

  MetaType = Type

  -- make some syntax to induct over, a la Outrageous but Meaningful Coindcidences
  -- this version uses large indexing (datatypes indexed by Types); 
  -- see version 2 for a (partial) version that uses a universe instead.

  -- Agda has trouble with non-constructor indices if we
  -- represent contexts as Types instead of lists of Types
  mutual
    data Ctx : MetaType where
      ·   : Ctx
      _,_ : (Γ : Ctx) (A : ElC Γ → Type) → Ctx

    ElC : Ctx → Type
    ElC · = Unit
    ElC (Γ , A) = Σ \ (θ : ElC Γ) → (A θ)


  -- syntax and its interpretation

  -- due to all the mutality, Agda is happier if Ty is indexed by the denotation of the type,
  -- rather than using a decoding function interpA.  See HomotopyCanonHType1.agda for what goes wrong.  
  data Ty : (Γ : Ctx) → (ElC Γ → Type) → MetaType 

  data Tm : (Γ : _) {A : _} → Ty Γ A → MetaType 

  interp : ∀ {Γ A} {A* : Ty Γ A} → Tm Γ A* → (θ : ElC Γ) → (A θ)

  data Ty where
    bool : ∀ {Γ} → Ty Γ (\ _ -> Bool)
    prop : ∀ {Γ} → Ty Γ (\ _ -> Type)  -- really small hprops?
    proof : ∀ {Γ} → (M : Tm Γ prop) → Ty Γ (\ θ → (interp M θ))
    Π : ∀ {Γ A B} → (A* : Ty Γ A) (B* : Ty (Γ , A) B) → Ty Γ (\ θ → (x : A θ) → (B (θ , x)))
    w : ∀ {Γ A B} → (A* : Ty Γ A) (B* : Ty Γ B) → Ty (Γ , A) (\ θ → B (fst θ))
    subst1 : ∀ {Γ A B} → {A* : Ty Γ A} (B* : Ty (Γ , A) B)
               (M : Tm Γ A*) → Ty Γ (\ θ → B (θ , interp M θ))

  data Tm where
    v    : ∀ {Γ A} {A* : Ty Γ A} → Tm (Γ , A) (w A* A*)
    w    : ∀ {Γ A B} → {A* : Ty Γ A} {B* : Ty Γ B} → Tm Γ B* → Tm (Γ , A) (w A* B*)
    true : ∀ {Γ} → Tm Γ bool
    false : ∀ {Γ} → Tm Γ bool
    unit  : ∀ {Γ} → Tm Γ prop
    void  : ∀ {Γ} → Tm Γ prop
    `∀    : ∀ {Γ} (A : Tm Γ prop) (B : Tm (Γ , (λ θ → (interp A θ))) prop) → Tm Γ prop
    <>    : ∀ {Γ} → Tm Γ (proof unit)
    abort : ∀ {Γ C} {C* : Ty Γ C} → Tm Γ (proof void) → Tm Γ C*
    plam  : ∀ {Γ A B} → Tm (Γ , _) (proof B) → Tm Γ (proof (`∀ A B))
    papp  : ∀ {Γ A B} → Tm Γ (proof (`∀ A B)) → (M : Tm Γ (proof A)) → Tm Γ (subst1 (proof B) M)
    if    : ∀ {Γ C} {C* : Ty (Γ , \ _ -> Bool) C} 
          → Tm Γ (subst1 C* true) 
          → Tm Γ (subst1 C* false) 
          → (x : Tm Γ bool) → Tm Γ (subst1 C* x)
    lam  : ∀ {Γ A B} {A* : Ty Γ A} {B* : Ty (Γ , A) B} → Tm (Γ , A) B* → Tm Γ (Π A* B*)
    app  : ∀ {Γ A B} {A* : Ty Γ A} {B* : Ty (Γ , A) B} → Tm Γ (Π A* B*) → (M : Tm Γ A*) → Tm Γ (subst1 B* M)

  ifcase : 
    {Γ   : Ctx}
    {C   : Σe (ElC Γ) (λ θ₁ → Bool) → Type}
    (C*  : Ty (Γ , (λ _ → Bool)) C)
    (M   : Tm Γ bool)
    (M1  : Tm Γ (subst1 C* true))
    (M2  : Tm Γ (subst1 C* false))
    (θ   : ElC Γ)
    → C (θ , interp M θ)

  <>case : {Γ : Ctx} {θ : ElC Γ} → (interp unit θ)
  abortcase : ∀ {Γ A} (A* : Ty Γ A) → Tm Γ (proof void) → (θ : ElC Γ) → (A θ)
  plamcase : ∀ {Γ A B} → (M : Tm (Γ , _) (proof B)) (θ : ElC Γ) → (interp (`∀ A B) θ)
  pappcase  : ∀ {Γ A B} → (M : Tm Γ (proof (`∀ A B))) → (N : Tm Γ (proof A)) (θ : ElC Γ)
              → (interp B (θ , interp N θ))

  interp v θ = snd θ
  interp (w M) θ = interp M (fst θ)
  interp true _ = True
  interp false _ = False
  interp unit _ = Unit
  interp void _ = Void
  interp (`∀ A B) θ = (x : interp A θ) -> interp B (θ , x)
  interp <> θ = <>case
  interp (abort{_}{_}{A*} M) θ = abortcase A* M θ
  interp (plam M) θ = plamcase M θ
  interp (papp M N) θ = pappcase M N θ
  interp (if{Γ}{C}{C*} M1 M2 M) θ = ifcase C* M M1 M2 θ
  interp (lam M) θ = λ x → interp M (θ , x)
  interp (app M N) θ = (interp M θ) (interp N θ)

  -- can't inline these because we need the prior cases of interp to be available
  ifcase {_}{C} C* M M1 M2 θ = if (λ x → (C (θ , x))) / interp M θ then interp M1 θ else (interp M2 θ)
  <>case = <>
  abortcase _ M θ = Sums.abort (interp M θ)
  plamcase M θ = λ x → interp M (θ , x)
  pappcase M N θ = interp M θ (interp N θ)


  -- syntactic contexts
  Ctx* : Ctx → MetaType 
  Ctx* · = Unit
  Ctx* (Γ , A) = Ctx* Γ × Ty Γ A 

  U~ : Type
  U~ = Σ \ (X : Type) → X

  mutual
    RC : ∀ {Γ} → (Γ* : Ctx* Γ) (θ : ElC Γ) → MetaType
    RC {·} <> θ = Unit
    RC {Γ , A} (Γ* , A*) (θ , M) = Σ (λ (sθ : RC Γ* θ) → R Γ* A* sθ M)

    R : ∀ {Γ A} (Γ* : Ctx* Γ) (A* : Ty Γ A) → {θ : ElC Γ} → RC Γ* θ → (A θ) → MetaType
    R _ bool rθ M = Either (M == True) (M == False)
    R Γ* prop rθ φ = (φ'x : U~) → fst φ'x == φ → MetaType
    R Γ* (proof M) rθ pf = propcase Γ* M rθ pf
    R Γ* (Π{Γ}{A}{B} A* B*) {θ} rθ M = (N : (A θ)) (rN : R Γ* A* rθ N) → R (Γ* , A*) B* (rθ , rN) (M N)
    R (Γ* , _) (w A* B*) {θ , _} (rθ , _) M = 
      R Γ* B* rθ M
    R Γ* (subst1{Γ}{A0}{B}{A0*} B* M0) {θ} rθ M = 
      R (Γ* , A0*) B* (rθ , fund _ A0* rθ M0) M

    -- workaround
    propcase : ∀ {Γ} (Γ* : Ctx* Γ) (φ : Tm Γ prop) {θ : ElC Γ} (rθ : RC Γ* θ) (pf : interp φ θ) → MetaType
    propcase Γ* φ rθ pf = fund Γ* prop rθ φ (_ , pf) id 

    -- proof that R is well-defined on Γ₀(A θ), without using transport.  
    -- FIXME: should be able to do this without using transport at any MetaTypes!
    -- and it should be a bijection?
    transportR : ∀ {Γ A θ M M'} (Γ* : Ctx* Γ) (A* : Ty Γ A) (rθ : RC Γ* θ) → M == M' → 
                 R Γ* A* rθ M → R Γ* A* rθ M'
    transportR Γ* bool rθ p (Inl x) = Inl (x ∘ ! p)
    transportR Γ* bool rθ p (Inr x) = Inr (x ∘ ! p)
    transportR Γ* prop rθ p rφ = λ φ'x q → rφ φ'x (! p ∘ q)  {- R Γ* prop rθ φ = φ → MetaType fails this case -} 
    transportR Γ* (proof M) rθ p rM = {!!} -- these are equal in Γ₀(U~)... 
    transportR Γ* (Π A* B*) rθ p rM = λ N rn → transportR (Γ* , A*) B* (rθ , rn) (ap≃ p) (rM N rn)  -- FIXME: no contravariance?
    transportR (Γ* , A*) (w A1* A2*) rθ p rM = transportR Γ* A2* (fst rθ) p rM
    transportR Γ* (subst1{Γ}{A0}{B}{A0*} B* M0) rθ p rM = transportR (Γ* , A0*) B* (rθ , _) p rM

    fund : ∀ {Γ A θ} (Γ* : Ctx* Γ) (A* : Ty Γ A) (rθ : RC Γ* θ) → (M : Tm Γ A*) → R Γ* A* rθ (interp M θ)
    fund (Γ* , A0*) .(w A* A*) (rθ , rM) (v {Γ} {A} {A*}) = coe {!!} rM -- need coherence for two typing derivations for Ty Γ A
    fund (Γ* , A0*) .(w A* B*) (rθ , rM) (w {Γ} {A} {B} {A*} {B*} M) = fund Γ* B* rθ M
    fund Γ* .bool rθ true = Inl id
    fund Γ* .bool rθ false = Inr id
    fund Γ* .prop rθ unit = λ φ'x p → Unit
    fund Γ* .prop rθ void = λ _ _ → Void
    fund Γ* .prop rθ (`∀ M M₁) = λ {(φ , x) p → {!coe p x!}}
    fund Γ* .(proof unit) rθ <> = {! <>!}
    fund Γ* A* rθ (abort M) = {! Sums.abort (fund Γ* (proof void) rθ M) !}
    fund Γ* .(proof (`∀ M M₁)) rθ (plam {Γ} {M} {M₁} M₂) = {!!}
    fund Γ* .(subst1 (proof M₁) M₃) rθ (papp {Γ} {M} {M₁} M₂ M₃) = {!!}
    fund {θ = θ} Γ* .(subst1 C* M) rθ (if {Γ} {C} {C*} M1 M2 M) = 
      (if (λ z → (rz : _) → R (Γ* , bool) C* (rθ , rz) (if (λ x → C (θ , x)) / z then interp M1 θ else (interp M2 θ))) / 
          interp M θ 
          then (λ rz → {!fund Γ* (subst1 C* true) rθ M1!}) -- need hset/consistency
          else {!!}) (fund Γ* bool rθ M)
    fund Γ* .(Π A* B*) rθ (lam {Γ} {A} {B} {A*} {B*} M) = λ N rN → fund (Γ* , A*) B* (rθ , rN) M
    fund Γ* .(subst1 B* N) rθ (app {Γ} {A} {B} {A*} {B*} M N) = fund Γ* (Π A* B*) rθ M _ (fund Γ* A* rθ N)

    canonicity : (M : Tm · bool) → Either (interp M <> == True) (interp M <> == False)
    canonicity M = fund <> bool <> M