{-# OPTIONS --type-in-type --without-K --no-termination-check #-}

open import lib.Prelude 
open BoolM 

module HomotopyCanonHSet2 where

  -- make some syntax to induct over, a la Outrageous but Meaningful Coindcidences

  -- universe of propositions
  mutual
    data CanonicalProp : Type where
      unit : CanonicalProp
      void : CanonicalProp
      `∀   : (A : CanonicalProp) (B : ElP A → CanonicalProp) → CanonicalProp
  
    ElP : CanonicalProp → Type
    ElP unit = Unit
    ElP void = Void
    ElP (`∀ A B) = (x : ElP A) → ElP (B x)

  -- universe of sets
  mutual
    data CanonicalSet : Type where
      prop  : CanonicalSet
      proof : CanonicalProp → CanonicalSet
      bool  : CanonicalSet
      Π : (A : CanonicalSet) (B : El A → CanonicalSet) → CanonicalSet
  
    El : CanonicalSet → Type
    El bool = Bool
    El prop = CanonicalProp
    El (proof P) = ElP P
    El (Π A B) = (x : El A) → El (B x)

  mutual
    data CanonicalCtx : Type where
      ·   : CanonicalCtx
      _,_ : (Γ : CanonicalCtx) (A : ElC Γ → CanonicalSet) → CanonicalCtx

    ElC : CanonicalCtx → Type
    ElC · = Unit
    ElC (Γ , A) = Σ \ (θ : ElC Γ) → El (A θ)


  -- syntax and its interpretation

  -- due to all the mutality, Agda is happier if this is indexed by the denotation, rather than
  -- using a decoding function interpA.  See HomotopyCanonHType1.agda for what goes wrong.  
  data Ty : (Γ : CanonicalCtx) → (ElC Γ → CanonicalSet) → Type 

  data Tm : (Γ : _) {A : _} → Ty Γ A → Type 

  interp : ∀ {Γ A} {A* : Ty Γ A} → Tm Γ A* → (θ : ElC Γ) → El (A θ)

  data Ty where
    bool : ∀ {Γ} → Ty Γ (\ _ -> bool)
    prop : ∀ {Γ} → Ty Γ (\ _ -> prop)
    proof : ∀ {Γ} → (M : Tm Γ prop) → Ty Γ (\ θ → proof (interp M θ))
    Π : ∀ {Γ A B} → (A* : Ty Γ A) (B* : Ty (Γ , A) B) → Ty Γ (\ θ → Π (A θ) (\ x → (B (θ , x))))
    w : ∀ {Γ A B} → (A* : Ty Γ A) (B* : Ty Γ B) → Ty (Γ , A) (\ θ → B (fst θ))
    subst1 : ∀ {Γ A B} → {A* : Ty Γ A} (B* : Ty (Γ , A) B)
               (M : Tm Γ A*) → Ty Γ (\ θ → B (θ , interp M θ))

  data Tm where
--    REMOVE : ∀ {Γ A} {A* : Ty Γ A} → Tm Γ A*
    v    : ∀ {Γ A} {A* : Ty Γ A} → Tm (Γ , A) (w A* A*)
    w    : ∀ {Γ A B} → {A* : Ty Γ A} {B* : Ty Γ B} → Tm Γ B* → Tm (Γ , A) (w A* B*)
    true : ∀ {Γ} → Tm Γ bool
    false : ∀ {Γ} → Tm Γ bool
    unit  : ∀ {Γ} → Tm Γ prop
    void  : ∀ {Γ} → Tm Γ prop
    `∀    : ∀ {Γ} (A : Tm Γ prop) (B : Tm (Γ , (λ θ → proof (interp A θ))) prop) → Tm Γ prop
    <>    : ∀ {Γ} → Tm Γ (proof unit)
    abort : ∀ {Γ C} {C* : Ty Γ C} → Tm Γ (proof void) → Tm Γ C*
    plam  : ∀ {Γ A B} → Tm (Γ , _) (proof B) → Tm Γ (proof (`∀ A B))
    papp  : ∀ {Γ A B} → Tm Γ (proof (`∀ A B)) → (M : Tm Γ (proof A)) → Tm Γ (subst1 (proof B) M)
    if    : ∀ {Γ C} {C* : Ty (Γ , \ _ -> bool) C} 
          → Tm Γ (subst1 C* true) 
          → Tm Γ (subst1 C* false) 
          → (x : Tm Γ bool) → Tm Γ (subst1 C* x)
    lam  : ∀ {Γ A B} {A* : Ty Γ A} {B* : Ty (Γ , A) B} → Tm (Γ , A) B* → Tm Γ (Π A* B*)
    app  : ∀ {Γ A B} {A* : Ty Γ A} {B* : Ty (Γ , A) B} → Tm Γ (Π A* B*) → (M : Tm Γ A*) → Tm Γ (subst1 B* M)

  ifcase : 
    {Γ   : CanonicalCtx}
    {C   : Σe (ElC Γ) (λ θ₁ → Bool) → CanonicalSet}
    (C*  : Ty (Γ , (λ _ → bool)) C)
    (M   : Tm Γ bool)
    (M1  : Tm Γ (subst1 C* true))
    (M2  : Tm Γ (subst1 C* false))
    (θ   : ElC Γ)
    → (El (C (θ , interp M θ)))

  <>case : {Γ : CanonicalCtx} {θ : ElC Γ} → ElP (interp unit θ)
  abortcase : ∀ {Γ A} (A* : Ty Γ A) → Tm Γ (proof void) → (θ : ElC Γ) → El (A θ)
  plamcase : ∀ {Γ A B} → (M : Tm (Γ , _) (proof B)) (θ : ElC Γ) → ElP (interp (`∀ A B) θ)
  pappcase  : ∀ {Γ A B} → (M : Tm Γ (proof (`∀ A B))) → (N : Tm Γ (proof A)) (θ : ElC Γ)
              → ElP (interp B (θ , interp N θ))

  interp v θ = snd θ
  interp (w M) θ = interp M (fst θ)
  interp true _ = True
  interp false _ = False
  interp unit _ = unit
  interp void _ = void
  interp (`∀ A B) θ = `∀ (interp A θ) (\ x -> interp B (θ , x))
  interp <> θ = <>case
  interp (abort{_}{_}{A*} M) θ = abortcase A* M θ
  interp (plam M) θ = plamcase M θ
  interp (papp M N) θ = pappcase M N θ
  interp (if{Γ}{C}{C*} M1 M2 M) θ = ifcase C* M M1 M2 θ
  interp (lam M) θ = λ x → interp M (θ , x)
  interp (app M N) θ = (interp M θ) (interp N θ)

  -- can't inline these because we need the prior cases of interp to be available
  ifcase {_}{C} C* M M1 M2 θ = if (λ x → El (C (θ , x))) / interp M θ then interp M1 θ else (interp M2 θ)
  <>case = <>
  abortcase _ M θ = Sums.abort (interp M θ)
  plamcase M θ = λ x → interp M (θ , x)
  pappcase M N θ = interp M θ (interp N θ)


  -- syntactic contexts
  data Ctx : CanonicalCtx → Type where
      ·   : Ctx ·
      _,_ : ∀ {Γ A} → (Γ* : Ctx Γ) → Ty Γ A → Ctx (Γ , A)

  mutual
    RC : ∀ {Γ} → (Γ* : Ctx Γ) (θ : ElC Γ) → Type
    RC · θ = Unit
    RC (Γ* , A*) (θ , M) = Σ (λ (sθ : RC Γ* θ) → R Γ* A* sθ M)

    R : ∀ {Γ A} (Γ* : Ctx Γ) (A* : Ty Γ A) → {θ : ElC Γ} → RC Γ* θ → El (A θ) → Type
    R _ bool rθ M = Either (M == True) (M == False)
    R Γ* prop rθ M = {!!}
    R Γ* (proof M) rθ M₁ = {!!}
    R Γ* (Π{Γ}{A}{B} A* B*) {θ} rθ M = (N : El (A θ)) (rN : R Γ* A* rθ N) → R (Γ* , A*) B* (rθ , rN) (M N)
    R (Γ* , _) (w A* B*) {θ , _} (rθ , _) M = 
      R Γ* B* rθ M
    R Γ* (subst1{Γ}{A0}{B}{A0*} B* M0) {θ} rθ M = 
      R (Γ* , A0*) B* (rθ , fund A0* rθ M0) M

    fund : ∀ {Γ A θ} {Γ* : Ctx Γ} (A* : Ty Γ A) (rθ : RC Γ* θ) → (M : Tm Γ A*) → R Γ* A* rθ (interp M θ)
    fund = {!!}
  
