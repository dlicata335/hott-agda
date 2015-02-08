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
    id : ∀ {Γ A} (A* : Ty Γ A) (M N : Tm Γ A*) → Ty Γ (\ θ → interp M θ == interp N θ)
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
    refl : ∀ {Γ A} {A* : Ty Γ A} (M : Tm Γ A*) → Tm Γ (id A* M M) 
    tr   : ∀ {Γ A C} {A* : Ty Γ A} (C* : Ty (Γ , A) C) {M1 M2 : Tm Γ A*} (α : Tm Γ (id A* M1 M2)) →  Tm Γ (subst1 C* M1) →  Tm Γ (subst1 C* M2)

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
  interp (refl M) θ = id
  interp (tr{Γ}{A}{C} C* α N) θ = transport (λ x → C (θ , x)) (interp α θ) (interp N θ)

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


  -- definition and proof of reducibility

  RC : ∀ {Γ} → (Γ* : Ctx* Γ) (θ : ElC Γ) → MetaType
  R : ∀ {Γ A} (Γ* : Ctx* Γ) (A* : Ty Γ A) → {θ : ElC Γ} → RC Γ* θ → (A θ) → MetaType
  Q : ∀ {Γ A} (Γ* : Ctx* Γ) (A* : Ty Γ A) → {θ : ElC Γ} → (rθ : RC Γ* θ) 
    → {M N : A θ} → R Γ* A* rθ M → R Γ* A* rθ N → (α : M == N) → MetaType
  fund : ∀ {Γ A θ} (Γ* : Ctx* Γ) (A* : Ty Γ A) (rθ : RC Γ* θ) → (M : Tm Γ A*) → R Γ* A* rθ (interp M θ)
  -- workaround scoping rules
  R-proof : ∀ {Γ} (Γ* : Ctx* Γ) (φ : Tm Γ prop) {θ : ElC Γ} (rθ : RC Γ* θ) (pf : interp φ θ) → MetaType

  RC {·} <> θ = Unit
  RC {Γ , A} (Γ* , A*) (θ , M) = Σ (λ (sθ : RC Γ* θ) → R Γ* A* sθ M)

  R _ bool rθ M = Either (M == True) (M == False)
  R Γ* prop rθ φ = (φ'x : U~) → fst φ'x == φ → MetaType
  R Γ* (proof M) rθ pf = R-proof Γ* M rθ pf
  R Γ* (Π{Γ}{A}{B} A* B*) {θ} rθ M = (N : (A θ)) (rN : R Γ* A* rθ N) → R (Γ* , A*) B* (rθ , rN) (M N)
  R (Γ* , _) (w A* B*) {θ , _} (rθ , _) M = 
    R Γ* B* rθ M
  R Γ* (subst1{Γ}{A0}{B}{A0*} B* M0) {θ} rθ M = 
    R (Γ* , A0*) B* (rθ , fund _ A0* rθ M0) M
  R Γ* (id A* M N) rθ α = Q Γ* A* rθ (fund Γ* A* rθ M) (fund Γ* A* rθ N) α

  R-proof Γ* φ rθ pf = fund Γ* prop rθ φ (_ , pf) id 

  -- is this an hprop in the metalanguage?
  Q Γ* bool rθ rM rN α = Unit  -- FIXME: should we insist that it's refl?
  Q Γ* prop rθ rM rN α = (x : _) → rM (_ , x) id → rN (_ , coe α x) id -- FIXME and symmetrically?
  Q Γ* (proof M) rθ rM rN α = Unit
  Q Γ* (Π A* B*) rθ rM rN α = (x : _) (rx : R Γ* A* rθ x) → Q (Γ* , A*) B* (rθ , rx) (rM _ rx) (rN _ rx) (ap≃ α)
  Q Γ* (id A* M N) rθ rM rN α = Unit
  Q Γ* (w A* B*) rθ rM rN α = Q (fst Γ*) B* (fst rθ) rM rN α
  Q Γ* (subst1{_}{_}{_}{A0*} B* M) rθ rM rN α = Q (Γ* , A0*) B* (rθ , fund Γ* A0* rθ M) rM rN α


  -- proof that R is well-defined on Γ₀(A θ), without using transport.  
  -- FIXME: should be able to do this without using transport at any MetaTypes?
  -- and it should be a bijection?

  transportQ : ∀ {Γ A} (Γ* : Ctx* Γ) (A* : Ty Γ A) → {θ : ElC Γ} → (rθ : RC Γ* θ) 
             → {M N : A θ} → (rM : R Γ* A* rθ M) → (rN : R Γ* A* rθ N) → {α α' : M == N} (p : α == α')
             → Q Γ* A* rθ rM rN α → Q Γ* A* rθ rM rN α'
  transportQ Γ* bool rθ rM rN p q = <>
  transportQ Γ* prop rθ rM rN p q = {!!} -- equal in Γ₀ U~
  transportQ Γ* (proof M) rθ rM rN p q = <>
  transportQ Γ* (Π A* B*) rθ rM rN p q = (λ x rx → transportQ (Γ* , A*) B* (rθ , rx) (rM _ rx) (rN _ rx) (ap (λ z → ap≃ z {x}) p) (q x rx))
  transportQ Γ* (id A* M N) rθ rM rN p q = <>
  transportQ Γ* (w A* B*) rθ rM rN p q = transportQ (fst Γ*) B* (fst rθ) rM rN p q
  transportQ Γ* (subst1{_}{_}{_}{A0*} B* M) rθ rM rN p q = transportQ (Γ* , A0*) B* (rθ , fund Γ* A0* rθ M) rM rN p q

  transportR : ∀ {Γ A θ M M'} (Γ* : Ctx* Γ) (A* : Ty Γ A) (rθ : RC Γ* θ) → M == M' → 
               R Γ* A* rθ M → R Γ* A* rθ M'
  transportR Γ* bool rθ p (Inl x) = Inl (x ∘ ! p)
  transportR Γ* bool rθ p (Inr x) = Inr (x ∘ ! p)
  transportR Γ* prop rθ p rφ = λ φ'x q → rφ φ'x (! p ∘ q)  {- R Γ* prop rθ φ = φ → MetaType fails this case -} 
  transportR Γ* (proof M) rθ p rM = {!!} -- these are equal in Γ₀(U~)... 
  transportR Γ* (Π A* B*) rθ p rM = λ N rn → transportR (Γ* , A*) B* (rθ , rn) (ap≃ p) (rM N rn)  -- FIXME: no contravariance?
  transportR (Γ* , A*) (w A1* A2*) rθ p rM = transportR Γ* A2* (fst rθ) p rM
  transportR Γ* (subst1{Γ}{A0}{B}{A0*} B* M0) rθ p rM = transportR (Γ* , A0*) B* (rθ , _) p rM
  transportR Γ* (id A* M* N*) rθ p rα = transportQ Γ* A* rθ (fund Γ* A* rθ M*) (fund Γ* A* rθ N*) p rα

  fund-refl : ∀ {Γ A} (Γ* : Ctx* Γ) (A* : Ty Γ A) → {θ : ElC Γ} → (rθ : RC Γ* θ) 
       → {M : A θ} → (rM : R Γ* A* rθ M) 
       → Q Γ* A* rθ rM rM id

  fund-tr : ∀ {Γ A C θ M1 M2 α N} (Γ* : Ctx* Γ) {A* : Ty Γ A} (C* : Ty (Γ , A) C) (rθ : RC Γ* θ)
          (rM1 : R Γ* A* rθ M1) (rM2 : R Γ* A* rθ M2) 
          (rα : Q Γ* A* rθ rM1 rM2 α) (rN : R (Γ* , A*) C* (rθ , rM1) N)
          → R (Γ* , A*) C* (rθ , rM2) (transport (\ x → C (θ , x)) α N)

  fund (Γ* , A0*) .(w A* A*) (rθ , rM) (v {Γ} {A} {A*}) = coe {!!} rM -- need coherence for two typing derivations for Ty Γ A
  fund (Γ* , A0*) .(w A* B*) (rθ , rM) (w {Γ} {A} {B} {A*} {B*} M) = fund Γ* B* rθ M
  fund Γ* .bool rθ true = Inl id
  fund Γ* .bool rθ false = Inr id
  fund Γ* .prop rθ unit = λ _ _ → Unit
  fund Γ* .prop rθ void = λ _ _ → Void
  fund Γ* .prop rθ (`∀ φ ψ) = λ {(φ' , x) p → {!coe p x!}}
  fund Γ* .(proof unit) rθ <> = {! <>!}
  fund Γ* A* rθ (abort M) = {! Sums.abort (fund Γ* (proof void) rθ M) !}
  fund Γ* .(proof (`∀ M M₁)) rθ (plam {Γ} {M} {M₁} M₂) = {!!}
  fund Γ* .(subst1 (proof M₁) M₃) rθ (papp {Γ} {M} {M₁} M₂ M₃) = {!!}
  fund {θ = θ} Γ* .(subst1 C* M) rθ (if {Γ} {C} {C*} M1 M2 M) = 
    (if (λ z → (rz : _) → R (Γ* , bool) C* (rθ , rz) (if (λ x → C (θ , x)) / z then interp M1 θ else (interp M2 θ))) / 
        interp M θ 
        then (λ rz → {!fund Γ* (subst1 C* true) rθ M1!}) -- need bool is an hset/consistency
        else {!!}) (fund Γ* bool rθ M)
  fund Γ* .(Π A* B*) rθ (lam {Γ} {A} {B} {A*} {B*} M) = λ N rN → fund (Γ* , A*) B* (rθ , rN) M
  fund Γ* .(subst1 B* N) rθ (app {Γ} {A} {B} {A*} {B*} M N) = fund Γ* (Π A* B*) rθ M _ (fund Γ* A* rθ N)
  fund Γ* .(id A* M* M*) rθ (refl{_}{_}{A*} M*) = fund-refl Γ* A* rθ (fund Γ* A* rθ M*)
  fund Γ* ._ rθ (tr{Γ}{A}{C}{A*} C* {M1}{M2} α N) = fund-tr Γ* C* rθ (fund Γ* _ rθ M1) (fund Γ* _ rθ M2) (fund Γ* _ rθ α) (fund Γ* _ rθ N)

  fund-refl Γ* bool rθ rM = <>
  fund-refl Γ* prop rθ rM = λ x rx → rx
  fund-refl Γ* (proof M) rθ rM = <>
  fund-refl Γ* (Π A* B*) rθ rM = λ x rx → fund-refl (Γ* , A*) B* (rθ , rx) (rM _ rx)
  fund-refl Γ* (id A* M N) rθ rM = <>
  fund-refl Γ* (w A* B*) rθ rM = fund-refl (fst Γ*) B* (fst rθ) rM
  fund-refl Γ* (subst1{_}{_}{_}{A0*} B* M) rθ rM = fund-refl (Γ* , A0*) B* (rθ , fund Γ* A0* rθ M) rM

  fund-tr {α = α} Γ* bool rθ rM1 rM2 rα (Inl x) = Inl (x ∘ ap≃ (transport-constant α))
  fund-tr {α = α} Γ* bool rθ rM1 rM2 rα (Inr x) = Inr (x ∘ ap≃ (transport-constant α))
  fund-tr Γ* prop rθ rM1 rM2 rα rN = {!!}
  fund-tr Γ* (proof M) rθ rM1 rM2 rα rN = {!!}
  fund-tr {Γ}{A0}{._}{θ}{M1}{M2}{α}{f} Γ* {A0*} (Π{.(Γ , A0)}{A}{B} A* B*) rθ rM1 rM2 rα rf = 
          λ x rx → {!fund-tr Γ* B* ? (rf _ (fund-tr Γ* A* rθ rM2 rM1 ? rx)) !}
  fund-tr Γ* (id C* M N) rθ rM1 rM2 rα rN = {!!}
  fund-tr {α = α} Γ* (w A* B*) rθ rM1 rM2 rα rN = transportR Γ* B* rθ (! (ap≃ (transport-constant α))) rN
  fund-tr Γ* (subst1 B* M) rθ rM1 rM2 rα rN = {!!}

  canonicity : (M : Tm · bool) → Either (interp M <> == True) (interp M <> == False)
  canonicity M = fund <> bool <> M

