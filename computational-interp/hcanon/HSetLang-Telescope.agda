{-# OPTIONS --type-in-type --no-termination-check #-}

open import lib.Prelude 
open BoolM 
import lib.PrimTrustMe

module computational-interp.hcanon.HSetLang-Telescope2 where

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
  data TelescopeTy : ∀ {Γ Γ'} (Γ* : Ctx Γ) (Γ'* : Ctx Γ') → MetaType 
  interp   : ∀ {Γ A} {Γ* : Ctx Γ} {A* : Ty Γ* A} → Tm Γ* A* → (θ : Γ) → (A θ)

  data Ctx where
    ·   : Ctx Unit
    _,_ : ∀ {Γ A} → (Γ* : Ctx Γ) → Ty Γ* A → Ctx (Σ A)

  data TelescopeTy where
    ·   : ∀ {Γ} {Γ* : Ctx Γ} → TelescopeTy Γ* Γ*
    _,_ : ∀ {Γ Γ'} {Γ* : Ctx Γ} {Γ'* : Ctx Γ'} → (Δ* : TelescopeTy Γ* Γ'*) → {A : _} (A* : Ty Γ'* A) → TelescopeTy Γ* (Γ'* , A*) 

  data SubstTele {Γ : _} {Γ* : Ctx Γ} {A : _} {A* : Ty Γ* A} (M : Tm Γ* A*) : ∀ {Γ' Γ''} {Γ'* : Ctx Γ'} (Δ* : TelescopeTy (Γ* , A*) Γ'*) (Γ''* : Ctx Γ'') → Set 

  semsubstmiddle : {Γ : _} {Γ* : Ctx Γ} {A : _} {A* : Ty Γ* A} (M : Tm Γ* A*) 
                 → ∀ {Γ' Γ''} {Γ'* : Ctx Γ'} (Δ* : TelescopeTy (Γ* , A*) Γ'*) (Γ''* : Ctx Γ'') 
                 → SubstTele M Δ* Γ''*
                 → (Γ'' → Γ')

  data Ty where
    bool : ∀ {Γ} {Γ* : Ctx Γ} → Ty Γ* (\ _ -> Bool)
    prop : ∀ {Γ} {Γ* : Ctx Γ} → Ty Γ* (\ _ -> Type)  -- really small hprops?
    proof : ∀ {Γ} {Γ* : Ctx Γ} (M : Tm Γ* prop) → Ty Γ* (\ θ → (interp M θ))
    Π : ∀ {Γ A B} {Γ* : Ctx Γ} (A* : Ty Γ* A) (B* : Ty (Γ* , A*) B) → Ty Γ* (\ θ → (x : A θ) → (B (θ , x)))
    id : ∀ {Γ A} {Γ* : Ctx Γ} (A* : Ty Γ* A) (M N : Tm Γ* A*) → Ty Γ* (\ θ → interp M θ == interp N θ)
    w : ∀ {Γ A B} {Γ* : Ctx Γ} → (A* : Ty Γ* A) (B* : Ty Γ* B) → Ty (Γ* , A*) (\ θ → B (fst θ))
    subst : ∀ {Γ Γ' Γ'' A} {Γ* : Ctx Γ} {A* : Ty Γ* A} {Γ'* : Ctx Γ'} {Γ''* : Ctx Γ''}  
                 (M : Tm Γ* A*) 
                 (Δ* : TelescopeTy (Γ* , A*) Γ'*) {B : _}
                 (B* : Ty Γ'* B)
               → (st : SubstTele M Δ* Γ''*)
               → Ty Γ''* (B o semsubstmiddle _ _ _ st)
    subst1 : ∀ {Γ A B} {Γ* : Ctx Γ} {A* : Ty Γ* A} (B* : Ty (Γ* , A*) B)
               (M : Tm Γ* A*) → Ty Γ* (\ θ → B (θ , interp M θ))
    ex : ∀ {Γ A B C} {Γ* : Ctx Γ} (A* : Ty Γ* A) (B* : Ty Γ* B) → Ty ((Γ* , A*) , w A* B*) C → Ty ((Γ* , B*) , w B* A*) (\ θ → C ((fst (fst θ) , snd θ) , snd (fst θ)))
    -- FIXME: missing some structural properties?

  data SubstTele  {Γ : _} {Γ* : Ctx Γ} {A : _} {A* : Ty Γ* A} (M : Tm Γ* A*) where
    ST-· : SubstTele M · Γ*
    ST-, : ∀ {Γ' Γ''} {Γ'* : Ctx Γ'} (Δ* : TelescopeTy (Γ* , A*) Γ'*) (Γ''* : Ctx Γ'') {B : _} (B* : Ty _ B) 
         → (st : SubstTele M Δ* Γ''*)
         → SubstTele M (Δ* , B*) (Γ''* , subst M Δ* B* st)

  semsubstmiddle M* .· Γ''* ST-· θ = θ , interp M* θ
  semsubstmiddle M* .(Δ* , B*) .(Γ''* , subst M* Δ* B* st) (ST-, Δ* Γ''* B* st) θ = semsubstmiddle _ _ _ st (fst θ) , snd θ

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
    tr   : ∀ {Γ A C} {Γ* : Ctx Γ} {A* : Ty Γ* A} 
           (C* : Ty (Γ* , A*) C) {M* : Tm Γ* A*} {N* : Tm Γ* A*} (α : Tm Γ* (id A* M* N*) )
         → Tm Γ* (subst M* · C* ST-·) → Tm Γ* (subst N* · C* ST-·)
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
  interp (uap f g) θ = ua (interp-uap-eqv f g θ) 
  interp (deq M) θ = interp M θ
  interp (lam= f g α) θ = interp-lam= f g α θ
  interp (tr {C = C} C* α M) θ = transport (λ x → C (θ , x)) (interp α θ) (interp M θ)

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

