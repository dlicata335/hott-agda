{-# OPTIONS --type-in-type --no-termination-check #-}

open import lib.Prelude 
open BoolM 
import lib.PrimTrustMe

module computational-interp.HomotopyCanonHSet9 where

  -- RULE: no transport at MetaTypes!
  MetaType = Type

  {-
    Make some syntax to induct over, a la Outrageous but Meaningful Coindcidences.  

    This version uses large indexing (datatypes indexed by Types); 
    see version 2 for a (partial) version that uses a universe instead.

    Unlike in the paper, terms are indexed by *syntactic* types and contexts,
    but there is a definitional equality rule that uses the semantics.
    The reason is that I couldn't figure out how to prove the fundamental
    theorem if terms are indexed by semantic types:
    splitting the term doesn't determine the syntactic type,
    and after splitting the syntactic type you can't split the term.  
  -}

  Context = Type

  -- syntax and its interpretation

  -- due to all the mutality, Agda is happier if Ty is indexed by the denotation of the type,
  -- rather than using a decoding function interpA.  See HomotopyCanonHType1.agda for what goes wrong.  
  data Ctx : Context → MetaType 
  data Ty : ∀ {Γ} (Γ* : Ctx Γ) → (Γ → Type) → MetaType 
  data Tm : ∀ {Γ} (Γ* : Ctx Γ) {A : _} → Ty Γ* A → MetaType 
  Subst : ∀ {Γ Γ'} (Γ* : Ctx Γ) (Γ'* : Ctx Γ') → MetaType
  interp  : ∀ {Γ A} {Γ* : Ctx Γ} {A* : Ty Γ* A} → Tm Γ* A* → (θ : Γ) → (A θ)
  interps : ∀ {Γ Γ'} {Γ* : Ctx Γ} {Γ'* : Ctx Γ'} → Subst Γ* Γ'* → Γ → Γ'

  data Ctx where
    ·   : Ctx Unit
    _,_ : ∀ {Γ A} → (Γ* : Ctx Γ) → Ty Γ* A → Ctx (Σ A)

  data Ty where
    bool : ∀ {Γ} {Γ* : Ctx Γ} → Ty Γ* (\ _ -> Bool)
    prop : ∀ {Γ} {Γ* : Ctx Γ} → Ty Γ* (\ _ -> Type)  -- really small hprops?
    proof : ∀ {Γ} {Γ* : Ctx Γ} (M : Tm Γ* prop) → Ty Γ* (\ θ → (interp M θ))
    Π : ∀ {Γ A B} {Γ* : Ctx Γ} (A* : Ty Γ* A) (B* : Ty (Γ* , A*) B) → Ty Γ* (\ θ → (x : A θ) → (B (θ , x)))
    id : ∀ {Γ A} {Γ* : Ctx Γ} (A* : Ty Γ* A) (M N : Tm Γ* A*) → Ty Γ* (\ θ → interp M θ == interp N θ)
    subst : ∀ {Γ Γ' A} {Γ* : Ctx Γ} (Γ'* : Ctx Γ') (θ'* : Subst Γ* Γ'*) (A* : Ty Γ'* A) → Ty Γ* (λ θ → A (interps θ'* θ))
    w : ∀ {Γ A B} {Γ* : Ctx Γ} → (A* : Ty Γ* A) (B* : Ty Γ* B) → Ty (Γ* , A*) (\ θ → B (fst θ))
    subst1 : ∀ {Γ A B} {Γ* : Ctx Γ} {A* : Ty Γ* A} (B* : Ty (Γ* , A*) B)
               (M : Tm Γ* A*) → Ty Γ* (\ θ → B (θ , interp M θ))
    ex : ∀ {Γ A B C} {Γ* : Ctx Γ} (A* : Ty Γ* A) (B* : Ty Γ* B) → Ty ((Γ* , A*) , w A* B*) C → Ty ((Γ* , B*) , w B* A*) (\ θ → C ((fst (fst θ) , snd θ) , snd (fst θ)))
    -- FIXME: missing some structural properties?

  Subst Γ* · = Unit
  Subst Γ* (Γ'* , A*) = Σ (λ (θ* : Subst Γ* Γ'*) → Tm Γ* (subst Γ'* θ* A*))

  interps {Γ'* = ·} θ'* θ = <>
  interps {Γ'* = Γ' , A} (θ'* , M*) θ = interps θ'* θ , interp M* θ

  unlam : ∀ {Γ A B} {Γ* : Ctx Γ} {A* : Ty Γ* A} {B* : Ty (Γ* , A*) B} → Tm Γ* (Π A* B*) → Tm (Γ* , A*) B*

  data Tm where
    v    : ∀ {Γ A} {Γ* : Ctx Γ} {A* : Ty Γ* A} → Tm (Γ* , A*) (w A* A*)
    w    : ∀ {Γ A B} {Γ* : Ctx Γ} {A* : Ty Γ* A} {B* : Ty Γ* B} → Tm Γ* B* → Tm (Γ* , A*) (w A* B*)
    true : ∀ {Γ} {Γ* : Ctx Γ} → Tm Γ* bool
    false : ∀ {Γ} {Γ* : Ctx Γ} → Tm Γ* bool
    unit  : ∀ {Γ} {Γ* : Ctx Γ} → Tm Γ* prop
    unit⁺  : ∀ {Γ} {Γ* : Ctx Γ} → Tm Γ* prop
    void  : ∀ {Γ} {Γ* : Ctx Γ} → Tm Γ* prop
    `∀    : ∀ {Γ} {Γ* : Ctx Γ} (A* : Tm Γ* prop) (B* : Tm (Γ* , proof A*) prop) → Tm Γ* prop
    <>    : ∀ {Γ} {Γ* : Ctx Γ} → Tm Γ* (proof unit)
    <>⁺     : ∀ {Γ} {Γ* : Ctx Γ} → Tm Γ* (proof unit⁺)
    split1 : ∀ {Γ} {Γ* : Ctx Γ} {C : _} (C* : Ty (Γ* , proof unit⁺) C)
          → Tm Γ* (subst1 C* <>⁺) 
          → (x : Tm Γ* (proof unit⁺)) → Tm Γ* (subst1 C* x)
    abort : ∀ {Γ C} {Γ* : Ctx Γ} {C* : Ty Γ* C} → Tm Γ* (proof void) → Tm Γ* C*
    plam  : ∀ {Γ} {Γ* : Ctx Γ} {A* : Tm Γ* prop} {B* : Tm (Γ* , proof A*) prop}
          → Tm (Γ* , proof A*) (proof B*) → Tm Γ* (proof (`∀ A* B*))
    papp  : ∀ {Γ} {Γ* : Ctx Γ} {A* : Tm Γ* prop} {B* : Tm (Γ* , proof A*) prop}
          → Tm Γ* (proof (`∀ A* B*)) → (M* : Tm Γ* (proof A*)) → Tm Γ* (subst1 (proof B*) M*)
    if    : ∀ {Γ C} {Γ* : Ctx Γ} {C* : Ty (Γ* , bool) C} 
          → Tm Γ* (subst1 C* true) 
          → Tm Γ* (subst1 C* false) 
          → (x : Tm Γ* bool) → Tm Γ* (subst1 C* x)
    lam  : ∀ {Γ A B} {Γ* : Ctx Γ} {A* : Ty Γ* A} {B* : Ty (Γ* , A*) B} → Tm (Γ* , A*) B* → Tm Γ* (Π A* B*)
    app  : ∀ {Γ A B} {Γ* : Ctx Γ} {A* : Ty Γ* A} {B* : Ty (Γ* , A*) B} → Tm Γ* (Π A* B*) → (M* : Tm Γ* A*) → Tm Γ* (subst1 B* M*)
    refl : ∀ {Γ A} {Γ* : Ctx Γ} {A* : Ty Γ* A} (M : Tm Γ* A*) → Tm Γ* (id A* M M) 
    tr   : ∀ {Γ A C} {Γ* : Ctx Γ} {A* : Ty Γ* A} (C* : Ty (Γ* , A*) C) {M1 M2 : Tm Γ* A*} (α : Tm Γ* (id A* M1 M2)) →  Tm Γ* (subst1 C* M1) →  Tm Γ* (subst1 C* M2)
    uap  : ∀ {Γ} {Γ* : Ctx Γ} {P : Tm Γ* prop} {Q : Tm Γ* prop} 
           (f : Tm (Γ* , proof P) (w (proof P) (proof Q)))
           (g : Tm (Γ* , proof Q) (w (proof Q) (proof P)))
           → Tm Γ* (id prop P Q)
    deq : ∀ {Γ A} {Γ* : Ctx Γ} {A* A'* : Ty Γ* A} → Tm Γ* A* → Tm Γ* A'* -- any two ways of saying the same thing are equal
    lam=  : ∀ {Γ A B} {Γ* : Ctx Γ} {A* : Ty Γ* A} {B* : Ty (Γ* , A*) B} 
           (f g : Tm Γ* (Π A* B*))
           (α : Tm (Γ* , A*) (id B* (unlam f) (unlam g)))
           → Tm Γ* (id _ f g)

  interp-if : ∀ {Γ C} {Γ* : Ctx Γ} (C*  : Ty (Γ* , bool) C) (M : Tm Γ* bool) (M1  : Tm Γ* (subst1 C* true)) (M2  : Tm Γ* (subst1 C* false)) (θ : Γ) → C (θ , interp M θ)
  interp-<> : ∀ {Γ} {Γ* : Ctx Γ} {θ : Γ} → (interp {Γ* = Γ*} unit θ)
  interp-<>⁺ : ∀ {Γ} {Γ* : Ctx Γ} {θ : Γ} → (interp {Γ* = Γ*} unit⁺ θ)
  interp-split1 : ∀ {Γ} {Γ* : Ctx Γ} {C : _} (C*  : Ty (Γ* , proof unit⁺) C) (M1  : Tm Γ* (subst1 C* <>⁺))  (M : Tm Γ* (proof unit⁺)) (θ : Γ) → C (θ , interp M θ)
  interp-abort : ∀ {Γ A} {Γ* : Ctx Γ} (A* : Ty Γ* A) → Tm Γ* (proof void) → (θ : Γ) → (A θ)
  interp-plam : ∀ {Γ} {Γ* : Ctx Γ} {A : _} {B : _}→ (M : Tm (Γ* , _) (proof B)) (θ : Γ) → (interp (`∀ A B) θ)
  interp-papp  : ∀ {Γ} {Γ* : Ctx Γ} {A : _} {B : _} → (M : Tm Γ* (proof (`∀ A B))) → (N : Tm Γ* (proof A)) (θ : Γ) → (interp B (θ , interp N θ))
  interp-uap-eqv : ∀ {Γ} {Γ* : Ctx Γ} {P : Tm Γ* prop} {Q : Tm Γ* prop} 
           (f : Tm (Γ* , proof P) (w (proof P) (proof Q)))
           (g : Tm (Γ* , proof Q) (w (proof Q) (proof P)))
           (θ : _) → Equiv (interp P θ) (interp Q θ)
  interp-lam= : ∀ {Γ A B} {Γ* : Ctx Γ} {A* : Ty Γ* A} {B* : Ty (Γ* , A*) B} 
           (f g : Tm Γ* (Π A* B*))
           (α : Tm (Γ* , A*) (id B* (unlam f) (unlam g))) (θ : Γ)
           → interp f θ == interp g θ

  interp v θ = snd θ
  interp (w M) θ = interp M (fst θ)
  interp true _ = True
  interp false _ = False
  interp unit _ = Unit
  interp unit⁺ _ = Unit⁺
  interp void _ = Void
  interp (`∀ A B) θ = (x : interp A θ) -> interp B (θ , x)
  interp <> θ = interp-<>
  interp <>⁺ θ = interp-<>⁺
  interp (split1 C* M1 M) θ = interp-split1 C* M1 M θ
  interp (abort{_}{_}{_}{A*} M) θ = interp-abort A* M θ
  interp (plam M) θ = interp-plam M θ
  interp (papp M N) θ = interp-papp M N θ
  interp (if{Γ}{_}{C}{C*} M1 M2 M) θ = interp-if C* M M1 M2 θ
  interp (lam M) θ = λ x → interp M (θ , x)
  interp (app M N) θ = (interp M θ) (interp N θ)
  interp (refl M) θ = id
  interp (tr{Γ}{A}{C} C* α N) θ = transport (λ x → C (θ , x)) (interp α θ) (interp N θ)
  interp (uap f g) θ = ua (interp-uap-eqv f g θ) 
  interp (deq M) θ = interp M θ
  interp (lam= f g α) θ = interp-lam= f g α θ

  unlam{Γ}{A}{B}{Γ*}{A*}{B*} f = deq (app wf' v) -- deq (app {A* = w A* A*}{B* = {!w (w A* A*) B*!}} (deq (w{A* = A*} f)) v)
    where wf : Tm (Γ* , A*) (w A* (Π A* B*))
          wf = w f

          B1 : Ty ((Γ* , A*) , w A* A*) (λ θ → B (fst θ))
          B1 = w (w A* A*) B*

          wf' : Tm (Γ* , A*) (Π (w A* A*) (ex A* A* B1)) 
          wf' = deq wf

  -- can't inline these because we need the prior cases of interp to be available
  interp-if {_}{C} C* M M1 M2 θ = if (λ x → (C (θ , x))) / interp M θ then interp M1 θ else (interp M2 θ)
  interp-<> = <>
  interp-<>⁺ = <>⁺
  interp-split1 {_}{_}{C} C* M1 M θ = split1⁺ (λ x → C (θ , x)) (interp M1 θ) (interp M θ)
  interp-abort _ M θ = Sums.abort (interp M θ)
  interp-plam M θ = λ x → interp M (θ , x)
  interp-papp M N θ = interp M θ (interp N θ)
  interp-uap-eqv f g θ = (improve (hequiv (λ x → interp f (θ , x)) (λ y → interp g (θ , y)) FIXME1 FIXME2))  where
    postulate FIXME1 : _
              FIXME2 : _
    -- one option would be to observe that all props are hprops, but what goes wrong if we don't?
  interp-lam= f g α θ = λ≃ (λ x → interp α (θ , x))

  -- definition and proof of reducibility

  RC : ∀ {Γ} → (Γ* : Ctx Γ) (θ : Γ) → MetaType
  R : ∀ {Γ A} (Γ* : Ctx Γ) (A* : Ty Γ* A) → {θ : Γ} → RC Γ* θ → (A θ) → MetaType
  Q : ∀ {Γ A} (Γ* : Ctx Γ) (A* : Ty Γ* A) → {θ : Γ} → (rθ : RC Γ* θ) 
     → {M N : A θ} → R Γ* A* rθ M → R Γ* A* rθ N → (α : M == N) → MetaType
  fund : ∀ {Γ A θ} (Γ* : Ctx Γ) (A* : Ty Γ* A) (rθ : RC Γ* θ) → (M : Tm Γ* A*) → R Γ* A* rθ (interp M θ)

  RC · θ = Unit
  RC (Γ* , A*) (θ , M) = Σ (λ (sθ : RC Γ* θ) → R Γ* A* sθ M)

  -- workaround scoping rules
  R-proof : ∀ {Γ} (Γ* : Ctx Γ) (φ : Tm Γ* prop) {θ : Γ} (rθ : RC Γ* θ) (pf : interp φ θ) → MetaType
  R-ex    : ∀ {Γ A B C} (Γ* : Ctx Γ) (A* : Ty Γ* A) (B* : Ty Γ* B) 
            → (C* : Ty ((Γ* , A*) , w A* B*) C) 
            → {θ : Γ} {a : A θ} {b : B θ} → (rθ : RC Γ* θ) -> (rb :  R Γ* B* rθ b) (ra : R (Γ* , B*) (w B* A*) (rθ , rb) a) → C ((θ , a) , b) 
            → MetaType

  R _ bool rθ M = Either (M == True) (M == False)
  R Γ* prop rθ φ = Σ \ (Rφ : (φ' : Type) → φ == φ' → φ' → MetaType) → 
                       (φ' : Type) (α : φ == φ') → (p1 p2 : φ') → p1 == p2 → Rφ φ' α p1 → Rφ φ' α p2 -- has a transport function
  R Γ* (proof M) rθ pf = R-proof Γ* M rθ pf
  R Γ* (Π{Γ}{A}{B} A* B*) {θ} rθ M = (N : (A θ)) (rN : R Γ* A* rθ N) → R (Γ* , A*) B* (rθ , rN) (M N)
  R ._ (w{Γ* = Γ*} A* B*) {θ , _} (rθ , _) M = 
    R Γ* B* rθ M
  R .Γ* (subst1{Γ}{A0}{B}{Γ*}{A0*} B* M0) {θ} rθ M = 
    R (Γ* , A0*) B* (rθ , fund _ A0* rθ M0) M
  R Γ* (id A* M N) rθ α = Q Γ* A* rθ (fund Γ* A* rθ M) (fund Γ* A* rθ N) α
  R ._ (ex {Γ* = Γ*} A* B* C*) ((rθ , rb) , ra) M = R-ex Γ* A* B* C* rθ rb ra M
  R Γ* _ rθ p = {!!}

  R-ex Γ* A* B* C* rθ rb ra M = R ((Γ* , A*) , w A* B*) C* ((rθ , ra) , rb) M
  R-proof Γ* φ rθ pf = fst (fund Γ* prop rθ φ) _ id pf

  -- is this an hprop in the metalanguage?
  Q Γ* bool rθ rM rN α = Unit  -- FIXME: should we insist that it's refl?
  Q Γ* prop rθ rM rN α = ((x : _) → fst rM _ id x → fst rN _ id (coe α x)) × ((y : _) → fst rN _ id y → fst rM _ id (coe (! α) y))
  Q Γ* (proof M) rθ rM rN α = Unit
  Q Γ* (Π A* B*) rθ rM rN α = (x : _) (rx : R Γ* A* rθ x) → Q (Γ* , A*) B* (rθ , rx) (rM _ rx) (rN _ rx) (ap≃ α)
  Q Γ* (id A* M N) rθ rM rN α = Unit
  Q ._ (w{Γ* = Γ*} A* B*) rθ rM rN α = Q Γ* B* (fst rθ) rM rN α
  Q ._ (subst1{_}{_}{_}{Γ*}{A0*} B* M) rθ rM rN α = Q (Γ* , A0*) B* (rθ , fund Γ* A0* rθ M) rM rN α
  Q ._ (ex {Γ* = Γ*} A* B* C*) ((rθ , ra) , rb) rM rN α = Q ((Γ* , A*) , w A* B*) C* ((rθ , rb) , ra) rM rN α
  Q Γ* _ rθ rM rN α = {!!}

  -- proof that R is well-defined on Γ₀(A θ), without using transport.  
  -- FIXME do we need to know that it is a bijection?

  transportQ : ∀ {Γ A} (Γ* : Ctx Γ) (A* : Ty Γ* A) → {θ : Γ} → (rθ : RC Γ* θ) 
             → {M N : A θ} → (rM : R Γ* A* rθ M) → (rN : R Γ* A* rθ N) → {α α' : M == N} (p : α == α')
             → Q Γ* A* rθ rM rN α → Q Γ* A* rθ rM rN α'
  transportQ Γ* bool rθ rM rN p q = <>
  transportQ Γ* prop rθ rM rN p q = (λ x rx → snd rN _ id _ _ (ap (λ z → transport (λ x₁ → x₁) z x) p) (fst q _ rx)) , 
                                   (λ y ry → snd rM _ id _ _ (ap (λ z → transport (λ x₁ → x₁) (! z) y) p) (snd q _ ry))
  transportQ Γ* (proof M) rθ rM rN p q = <>
  transportQ Γ* (Π A* B*) rθ rM rN p q = (λ x rx → transportQ (Γ* , A*) B* (rθ , rx) (rM _ rx) (rN _ rx) (ap (λ z → ap≃ z {x}) p) (q x rx))
  transportQ Γ* (id A* M N) rθ rM rN p q = <>
  transportQ ._ (w{Γ* = Γ*} A* B*) rθ rM rN p q = transportQ Γ* B* (fst rθ) rM rN p q
  transportQ .Γ* (subst1{_}{_}{_}{Γ*}{A0*} B* M) rθ rM rN p q = transportQ (Γ* , A0*) B* (rθ , fund Γ* A0* rθ M) rM rN p q
  transportQ ._ (ex {Γ* = Γ*} A* B* C*) ((rθ , ra) , rb) rM rN p q = transportQ ((Γ* , A*) , w A* B*) C* ((rθ , rb) , ra) rM rN p q
  transportQ Γ* _ rθ rM rN p q = {!!}

  transportR : ∀ {Γ A θ M M'} (Γ* : Ctx Γ) (A* : Ty Γ* A) (rθ : RC Γ* θ) → M == M' → 
               R Γ* A* rθ M → R Γ* A* rθ M'
  transportR Γ* bool rθ p (Inl x) = Inl (x ∘ ! p)
  transportR Γ* bool rθ p (Inr x) = Inr (x ∘ ! p)
  transportR Γ* prop rθ p rφ = (λ φ' q x → fst rφ φ' (q ∘ p) x) , (λ φ' φ=φ' pf1 pf2 α rpf1 → snd rφ _ (φ=φ' ∘ p) pf1 pf2 α rpf1)  
  transportR Γ* (proof M) rθ p rM = snd (fund Γ* prop rθ M) _ id _ _ p rM 
  transportR Γ* (Π A* B*) rθ p rM = λ N rn → transportR (Γ* , A*) B* (rθ , rn) (ap≃ p) (rM N rn) 
  transportR ._ (w {Γ* = Γ*} A1* A2*) rθ p rM = transportR Γ* A2* (fst rθ) p rM
  transportR Γ* (subst1{Γ}{A0}{B}{._}{A0*} B* M0) rθ p rM = transportR (Γ* , A0*) B* (rθ , _) p rM
  transportR Γ* (id A* M* N*) rθ p rα = transportQ Γ* A* rθ (fund Γ* A* rθ M*) (fund Γ* A* rθ N*) p rα
  transportR ._ (ex {Γ* = Γ*} A* B* C*) ((rθ , ra) , rb) p M = transportR ((Γ* , A*) , w A* B*) C* ((rθ , rb) , ra) p M
  transportR Γ* _ rθ p q = {!!}

  -- definitionally equal types give the same R
  -- FIXME could also allow changing Gamma but we haven't needed it yet
  R-deq : ∀ {Γ A θ M} (Γ* : Ctx Γ) (A* A1* : Ty Γ* A) (rθ : RC Γ* θ) → R Γ* A* rθ M → R Γ* A1* rθ M
  R-deq Γ* A* A1* rθ = lib.PrimTrustMe.unsafe-cast

  fund-<> : ∀ {Γ θ} → (Γ* : Ctx Γ) (rθ : RC Γ* θ) → R Γ* (proof unit) rθ <>
  fund-<>⁺ : ∀ {Γ θ} → (Γ* : Ctx Γ) (rθ : RC Γ* θ) → R Γ* (proof unit⁺) rθ <>⁺
  fund-abort : ∀ {Γ θ C} → (Γ* : Ctx Γ) (rθ : RC Γ* θ) → Tm Γ* (proof void) → C
  fund-lam= : ∀ {Γ A B} (Γ* : Ctx Γ) (A* : Ty Γ* A) (B* : Ty (Γ* , A*) B)
              (f g : Tm Γ* (Π A* B*))
              (α : Tm (Γ* , A*) (id B* (unlam f) (unlam g)))
              {θ : Γ} (rθ : RC Γ* θ)
            → (x : _) (rx : _) → _
  fund-split1 : ∀ {Γ θ} (Γ* : Ctx Γ) {C : _} (C* : Ty (Γ* , proof unit⁺) C)
          → (M1 : Tm Γ* (subst1 C* <>⁺) )
          → (M : Tm Γ* (proof unit⁺))
          → (rθ : RC Γ* θ)
          → R Γ* (subst1 C* M) rθ (interp (split1 C* M1 M) θ)

  fund-refl : ∀ {Γ A} (Γ* : Ctx Γ) (A* : Ty Γ* A) → {θ : Γ} → (rθ : RC Γ* θ) 
       → {M : A θ} → (rM : R Γ* A* rθ M) 
       → Q Γ* A* rθ rM rM id

  fund-tr : ∀ {Γ A C θ M1 M2 α N} (Γ* : Ctx Γ) {A* : Ty Γ* A} (C* : Ty (Γ* , A*) C) (rθ : RC Γ* θ)
          (rM1 : R Γ* A* rθ M1) (rM2 : R Γ* A* rθ M2) 
          (rα : Q Γ* A* rθ rM1 rM2 α) (rN : R (Γ* , A*) C* (rθ , rM1) N)
          → R (Γ* , A*) C* (rθ , rM2) (transport (\ x → C (θ , x)) α N)

  fund .(Γ* , A*) .(w A* A*) (rθ , rM) (v {Γ} {A} {Γ*} {A*}) = rM
  fund .(Γ* , A*) .(w A* B*) (rθ , rM) (w {Γ} {A} {B} {Γ*} {A*} {B*} M) = fund Γ* B* rθ M
  fund Γ* .bool rθ true = Inl id
  fund Γ* .bool rθ false = Inr id
  fund Γ* .prop rθ unit = (λ _ _ _ → Unit) , (λ φ' α p1 p2 x x₁ → <>)
  fund Γ* .prop rθ unit⁺ = (λ ψ p x → coe (! p) x == <>⁺) , (λ φ' α p1 p2 α₁ r1 → r1 ∘ ap (λ z → coe (! α) z) (! α₁))
  fund Γ* .prop rθ void = (λ _ _ _ → Void) , (λ φ' α p1 p2 x x₁ → x₁)
  fund {θ = θ} Γ* .prop rθ (`∀ φ ψ) = 
    (λ φ' p x → (y : interp φ θ) → (ry : fst (fund Γ* prop rθ φ) _ id y) → fst (fund (Γ* , proof φ) prop (rθ , ry) ψ) _ id (coe (! p) x y)) , 
    (λ φ' α p1 p2 q w y ry → snd (fund (Γ* , proof φ) prop (rθ , ry) ψ) (interp ψ (θ , y)) id (coe (! α) p1 y) (coe (! α) p2 y) (ap (λ z → coe (! α) z y) q) (w y ry))
  fund Γ* .(proof unit) rθ <> = fund-<> Γ* rθ
  fund Γ* A* rθ (abort M) = fund-abort Γ* rθ M
  fund .Γ* .(proof (`∀ M M₁)) rθ (plam {Γ}{Γ*} {M} {M₁} M₂) = {!!} -- should be like lam 
  fund .Γ* .(subst1 (proof M₁) M₃) rθ (papp {Γ}{Γ*} {M} {M₁} M₂ M₃) = {!!} -- should be like app
  fund {θ = θ} .Γ* .(subst1 C* M) rθ (if {Γ} {C} {Γ*} {C*} M1 M2 M) with interp M θ | (fund Γ* bool rθ M)
  ... | i | Inl x = transportR (Γ* , bool) C* (rθ , Inl x) (path-induction
                                                              (λ i₁ x₁ →
                                                                 transport (λ x₂ → C (θ , x₂)) x₁ (interp M1 θ) ==
                                                                 if (λ x₂ → C (θ , x₂)) / i₁ then interp M1 θ else (interp M2 θ))
                                                              id (! x)) 
                               (fund-tr{_}{_}{_}{_}{_}{_}{ ! x }{_}  Γ* C* rθ (fund Γ* bool rθ true) (Inl x) <>  (fund Γ* _ rθ M1)) 
                -- see split1 for a cleaner version
  ... | i | Inr x = transportR (Γ* , bool) C* (rθ , Inr x) (path-induction
                                                              (λ i₁ x₁ →
                                                                 transport (λ x₂ → C (θ , x₂)) x₁ (interp M2 θ) ==
                                                                 if (λ x₂ → C (θ , x₂)) / i₁ then interp M1 θ else (interp M2 θ))
                                                              id (! x)) 
                               (fund-tr{_}{_}{_}{_}{_}{_}{ ! x }{_} Γ* C* rθ (fund Γ* bool rθ false) (Inr x) <>  (fund Γ* _ rθ M2)) 
  fund .Γ* .(Π A* B*) rθ (lam {Γ} {A} {B} {Γ*} {A*} {B*} M) = λ N rN → fund (Γ* , A*) B* (rθ , rN) M
  fund .Γ* .(subst1 B* N) rθ (app {Γ} {A} {B} {Γ*} {A*} {B*} M N) = fund Γ* (Π A* B*) rθ M _ (fund Γ* A* rθ N)
  fund .Γ* .(id A* M* M*) rθ (refl{_}{_}{Γ*}{A*} M*) = fund-refl Γ* A* rθ (fund Γ* A* rθ M*)
  fund .Γ* ._ rθ (tr{Γ}{A}{C}{Γ*}{A*} C* {M1}{M2} α N) = fund-tr Γ* C* rθ (fund Γ* _ rθ M1) (fund Γ* _ rθ M2) (fund Γ* _ rθ α) (fund Γ* _ rθ N)
  fund {θ = θ} .Γ* ._ rθ (uap{Γ}{Γ*}{P}{Q} f* g*) = 
       (λ x rx → snd (fund Γ* prop rθ Q) _ id (interp f* (θ , x)) (coe (interp (uap{P = P}{Q = Q} f* g*) θ) x) 
                     (! (ap≃ (type≃β (interp-uap-eqv{P = P}{Q = Q} f* g* θ))))
                     (fund (Γ* , proof P) (w (proof P) (proof Q)) (rθ , rx) f*)) , 
       (λ x rx → snd (fund Γ* prop rθ P) _ id (interp g* (θ , x)) (coe (! (interp (uap{P = P}{Q = Q} f* g*) θ)) x) 
                     (! (ap≃ (type≃β! (interp-uap-eqv{P = P}{Q = Q} f* g* θ))))
                     (fund (Γ* , proof Q) (w (proof Q) (proof P)) (rθ , rx) g*)) 
  fund .Γ* .A* rθ (deq{Γ}{A}{Γ*}{A1*}{A*} M) = R-deq Γ* A1* A* rθ (fund Γ* A1* rθ M) 
  fund Γ* ._ rθ (lam={A* = A*}{B* = B*} f* g* α*) = λ x rx → fund-lam= Γ*  A* B* f* g* α* rθ x rx
  fund Γ* ._ rθ <>⁺ = fund-<>⁺ Γ* rθ
  fund Γ* ._ rθ (split1 C* M1 M) = fund-split1 Γ* C* M1 M rθ 

  fund-<> Γ* rθ = <>
  fund-<>⁺ Γ* rθ = id
  fund-abort Γ* rθ M = Sums.abort (fund Γ* (proof void) rθ M)
  fund-lam= Γ* A* B* f* g* α* rθ x rx = transportQ (Γ* , A*) B* (rθ , rx) (fund Γ* (Π A* B*) rθ f* x rx)
                                         (fund Γ* (Π A* B*) rθ g* x rx) (! (Π≃β (λ x₁ → interp α* (_ , x₁)))) (fund (Γ* , A*) _ (rθ , rx) α*)

  fund-split1 {θ = θ} Γ* {C} C* M1 M rθ = transportR (Γ* , proof unit⁺) C* (rθ , (fund Γ* (proof unit⁺) rθ M)) (apd (split1⁺ (λ x → C (θ , x)) (interp M1 θ)) (! (fund Γ* (proof unit⁺) rθ M))) 
                                          (fund-tr {α = ! (fund Γ* (proof unit⁺) rθ M)}
                                                  Γ* C* rθ id (fund Γ* (proof unit⁺) rθ M) <>  -- uses the fact that all paths are reducible in Prooff(-)
                                                  (fund Γ* (subst1 C* <>⁺) rθ M1))
  -- (fund Γ* (subst1 C* <>⁺) rθ M1) -- 

  fund-refl Γ* bool rθ rM = <>
  fund-refl Γ* prop rθ rM = (λ x rx → rx) , (λ x rx → rx)
  fund-refl Γ* (proof M) rθ rM = <>
  fund-refl Γ* (Π A* B*) rθ rM = λ x rx → fund-refl (Γ* , A*) B* (rθ , rx) (rM _ rx)
  fund-refl Γ* (id A* M N) rθ rM = <>
  fund-refl ._ (w {Γ* = Γ*} A* B*) rθ rM = fund-refl Γ* B* (fst rθ) rM
  fund-refl Γ* (subst1{_}{_}{_}{._}{A0*} B* M) rθ rM = fund-refl (Γ* , A0*) B* (rθ , fund Γ* A0* rθ M) rM
  fund-refl Γ* _ rθ rM = {!!}

  fund-sym : ∀ {Γ A θ M N α} (Γ* : Ctx Γ) (A* : Ty Γ* A) (rθ : RC Γ* θ)
               (rM : R Γ* A* rθ M) (rN : R Γ* A* rθ N)
           → Q Γ* A* rθ rM rN α
           → Q Γ* A* rθ rN rM (! α)
  fund-sym Γ* bool rθ rM rN rα = <>
  fund-sym {α = α} Γ* prop rθ rM rN rα = snd rα , (λ x rx → snd rN _ id _ _ (ap (λ z → coe z x) (! (!-invol α))) (fst rα x rx))
  fund-sym Γ* (proof M) rθ rM rN rα = <>
  fund-sym {α = α} Γ* (Π A* B*) rθ rM rN rα = λ x rx → transportQ (Γ* , A*) B* (rθ , rx) _ _ (! (ap-! (λ f → f x) α))
                                               (fund-sym (Γ* , A*) B* (rθ , rx) (rM x rx) (rN x rx) (rα x rx))
  fund-sym Γ* (id A* M N) rθ rM rN rα = <>
  fund-sym ._ (w {Γ* = Γ*} A* B*) rθ rM rN rα = fund-sym Γ* B* (fst rθ) rM rN rα
  fund-sym Γ* (subst1{_}{_}{_}{._}{A*} B* M) rθ rM rN rα = fund-sym (Γ* , A*) B* (rθ , _) rM rN rα
  fund-sym Γ* _ rθ rM rN rα = {!!}

  fund-trans : ∀ {Γ A θ M N O α β} (Γ* : Ctx Γ) (A* : Ty Γ* A) (rθ : RC Γ* θ)
               (rM : R Γ* A* rθ M) (rN : R Γ* A* rθ N) (rO : R Γ* A* rθ O) 
             → Q Γ* A* rθ rM rN α
             → Q Γ* A* rθ rN rO β
             → Q Γ* A* rθ rM rO (β ∘ α)
  fund-trans Γ* bool rθ rM rN rO qMN qNO = <>
  fund-trans {α = α} {β = β} Γ* prop rθ rM rN rO qMN qNO = 
    (λ x rx → snd rO _ id _ _ (! (ap≃ (transport-∘ (λ x₁ → x₁) β α))) (fst qNO _ (fst qMN x rx))) , 
    (λ y ry → snd rM _ id _ _ (ap (λ z → coe z y) (! (!-∘ β α)) ∘ ! (ap≃ (transport-∘ (λ x₁ → x₁) (! α) (! β)))) (snd qMN _ (snd qNO y ry)))
  fund-trans Γ* (proof M) rθ rM rN rO qMN qNO = <>
  fund-trans {α = α} {β = β} Γ* (Π A* B*) rθ rM rN rO qMN qNO = λ x rx → transportQ (Γ* , A*) B* (rθ , rx) _ _ (! (ap-∘ (λ f → f x) β α))
                                                           (fund-trans (Γ* , A*) B* (rθ , rx) (rM x rx) (rN x rx) (rO x rx)
                                                            (qMN x rx) (qNO x rx))
  fund-trans Γ* (id A* M N) rθ rM rN rO qMN qNO = <>
  fund-trans ._ (w {Γ* = Γ*} A*  B*) rθ rM rN rO qMN qNO = fund-trans Γ* B* (fst rθ) rM rN rO qMN qNO
  fund-trans Γ* (subst1{_}{_}{_}{._}{A*} B* M) rθ rM rN rO qMN qNO = fund-trans (Γ* , A*) B* (rθ , _) rM rN rO qMN qNO
  fund-trans Γ* _ rθ rM rN rO qMN qNO = {!!}

  fund-ap : ∀ {Γ A B θ M1 M2 α} 
           (Γ* : Ctx Γ) {A* : Ty Γ* A} {B* : Ty (Γ* , A*) B} (f : Tm (Γ* , A*) B*) (rθ : RC Γ* θ)
           (rM1 : R Γ* A* rθ M1) (rM2 : R Γ* A* rθ M2) 
           (rα : Q Γ* A* rθ rM1 rM2 α)
          → Q (Γ* , A*) B* (rθ , rM2) 
              (fund-tr Γ* B* rθ rM1 rM2 rα (fund (Γ* , A*) B* (rθ , rM1) f)) 
              (fund (Γ* , A*) B* (rθ , rM2) f) 
              (apd (\ x -> interp f (θ , x)) α)
  fund-ap {α = α} Γ* {A* = A*} v rθ rM1 rM2 rα = transportQ Γ* A* rθ _ rM2 (coh α) (fund-trans {α = ap≃ (transport-constant α)} {β = α} Γ* A* rθ _ _ _ {!!} rα) where
    coh : ∀ {A} {M1 M2 : A} (α : M1 == M2)→ (α ∘ ap (λ f → f M1) (transport-constant α)) == (apd (λ x → x) α)
    coh id = id
  fund-ap Γ* (w f) rθ rM1 rM2 rα = {!!}
  fund-ap Γ* true rθ rM1 rM2 rα = <>
  fund-ap Γ* false rθ rM1 rM2 rα = <>
  fund-ap Γ* unit rθ rM1 rM2 rα = {!!}
  fund-ap Γ* unit⁺ rθ rM1 rM2 rα = {!!}
  fund-ap Γ* void rθ rM1 rM2 rα = {!!}
  fund-ap Γ* (`∀ f f₁) rθ rM1 rM2 rα = {!!}
  fund-ap Γ* <> rθ rM1 rM2 rα = <>
  fund-ap Γ* <>⁺ rθ rM1 rM2 rα = <>
  fund-ap Γ* (split1 _ f f₁) rθ rM1 rM2 rα = {!!}
  fund-ap Γ* (abort f) rθ rM1 rM2 rα = {!!}
  fund-ap Γ* (plam f₂) rθ rM1 rM2 rα = <>
  fund-ap Γ* (papp f₂ f₃) rθ rM1 rM2 rα = <>
  fund-ap Γ* (if f f₁ f₂) rθ rM1 rM2 rα = {!!}
  fund-ap Γ* (lam f) rθ rM1 rM2 rα = {!!}
  fund-ap Γ* (app f f₁) rθ rM1 rM2 rα = {!!}
  fund-ap Γ* (refl f) rθ rM1 rM2 rα = <>
  fund-ap Γ* (tr C* f₂ f₃) rθ rM1 rM2 rα = {!!}
  fund-ap Γ* (uap f₂ f₃) rθ rM1 rM2 rα = <>
  fund-ap Γ* (deq f) rθ rM1 rM2 rα = lib.PrimTrustMe.unsafe-cast (fund-ap Γ* f rθ rM1 rM2 rα)
  fund-ap Γ* (lam= f f₁ f₂) rθ rM1 rM2 rα = <>

  fund-ap1 : ∀ {Γ A B θ M1 M2 α} (Γ* : Ctx Γ) {A* : Ty Γ* A} {B* : Ty Γ* B} (f : Tm (Γ* , A*) (w _ B*)) (rθ : RC Γ* θ)
           (rM1 : R Γ* A* rθ M1) (rM2 : R Γ* A* rθ M2) 
          → Q Γ* A* rθ rM1 rM2 α
          → Q Γ* B* rθ (fund (Γ* , A*) (w _ B*) (rθ , rM1) f) (fund (Γ* , A*) (w _ B*) (rθ , rM2) f) (ap (\ x -> interp f (θ , x)) α)
  fund-ap1 {θ = θ} {α = α} Γ* {B* = B*} f rθ rM1 rM2 rα =
    transportQ Γ* B* rθ _ _ (coh {f = \ x -> interp f (θ , x)} α) (fund-trans {α = ! (ap≃ (transport-constant α))} Γ* B* rθ _ _ _ {!!} (fund-ap Γ* f rθ rM1 rM2 rα)) where
           coh : ∀ {A B} {f : A → B} {M1 M2 : _} (α : M1 == M2) → 
             (apd f α ∘ ! (ap≃ (transport-constant α))) == (ap f α)
           coh id = id


  -- FIXME: why doesn't this work in --without-K? 
  fund-tr {α = α} Γ* bool rθ rM1 rM2 rα (Inl x) = Inl (x ∘ ap≃ (transport-constant α))
  fund-tr {α = α} Γ* bool rθ rM1 rM2 rα (Inr x) = Inr (x ∘ ap≃ (transport-constant α))
  fund-tr {α = α} Γ* prop rθ rM1 rM2 rα rN = (λ φ' p x' → fst rN φ' (p ∘ ! (ap≃ (transport-constant α))) x') , (λ φ' p x1' x2' eq rx1 → snd rN φ' _ x1' x2' eq rx1)
  fund-tr {α = α} Γ* (proof M) rθ rM1 rM2 rα rN = snd (fund (Γ* , _) prop (rθ , rM2) M) _ id _ _ (! (ap≃ (transport-ap-assoc (λ x → interp M (_ , x)) α))) 
                                                      (fst ap-is-reducible _ rN) where
          ap-is-reducible : Q Γ* prop rθ (fund (Γ* , _) prop (rθ , rM1) M) (fund (Γ* , _) prop (rθ , rM2) M) (ap (\ x -> interp M (_ , x)) α)
          ap-is-reducible = fund-ap1 Γ* (deq {A* = prop} {A'* = w _ prop} M) rθ rM1 rM2 rα -- FIXME need to set things up so that we do the equality test after!
  fund-tr {Γ}{A0}{._}{θ}{M1}{M2}{α}{f} Γ* {A0*} (Π{._}{A}{B} A* B*) rθ rM1 rM2 rα rf = 
          λ x rx → {!fund-tr Γ* B* ? (rf _ (fund-tr Γ* A* rθ rM2 rM1 ? rx)) !} -- need Sigmas / generalization to contexts
  fund-tr {θ = θ} Γ* (id C* M N) rθ rM1 rM2 rα rN = {!!} -- need composition and ap and !
  fund-tr Γ* (subst Γ'* θ'* A₂) rθ rM1 rM2 rα M = {!!}
  fund-tr {α = α} Γ* {A*} (w .A* B*) rθ rM1 rM2 rα rN = transportR Γ* B* rθ (! (ap≃ (transport-constant α))) rN
  fund-tr Γ* (subst1 A₃ M) rθ rM1 rM2 rα M₁ = {!!}
  fund-tr ._ (ex _ _ _) rθ rM1 rM2 rα M₁ = {!!}

  example : Tm · (proof unit⁺)
  example = deq (tr {A* = prop} (proof (deq v)) {M1 = unit} {M2 = unit⁺} unit=unit (deq <>)) where
    unit=unit : Tm · (id prop unit unit⁺)
    unit=unit = uap {P = unit} {Q = unit⁺} (deq <>⁺) (deq <>)

  example2 : Tm · bool
  example2 = deq (split1 bool (deq true) example)

  example2a : Tm · bool
  example2a = true

  example2b : Tm · bool
  example2b = (deq (split1 bool (deq true) <>⁺))

  canonicity1 : (M : Tm · (proof unit⁺)) → interp M <> == <>⁺
  canonicity1 M = fund · (proof unit⁺) <> M

  canonicity2 : (M : Tm · bool) → Either (interp M <> == True) (interp M <> == False)
  canonicity2 M = fund · bool <> M

  test : canonicity2 example2 == Inl {!!}
  test = id