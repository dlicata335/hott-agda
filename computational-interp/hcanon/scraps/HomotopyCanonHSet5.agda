{-# OPTIONS --type-in-type --without-K --no-termination-check #-}

open import lib.Prelude 
open BoolM 

module HomotopyCanonHSet5 where

  -- RULE: no transport at MetaTypes!
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


  Propo : Type
  Propo = Type -- really small hprops?

  -- syntax and its interpretation

  -- due to all the mutality, Agda is happier if Ty is indexed by the denotation of the type,
  -- rather than using a decoding function interpA.  See HomotopyCanonHType1.agda for what goes wrong.  
  data Ty : (Γ : Ctx) → (ElC Γ → Type) → MetaType 

  data Tm : (Γ : _) (A : ElC Γ → Type) → MetaType 

  interp : ∀ {Γ A} → Tm Γ A → (θ : ElC Γ) → (A θ)

  data Ty where
    bool : ∀ {Γ} → Ty Γ (\ _ -> Bool)
    -- for this representation, the universe decoding happens definitionally for free!
    prop : ∀ {Γ} → Ty Γ (\ _ -> Type)  
    proof : ∀ {Γ} → (M : Tm Γ (\ _ -> Propo)) → Ty Γ (\ θ → (interp M θ))
    Π : ∀ {Γ A B} → (A* : Ty Γ A) (B* : Ty (Γ , A) B) → Ty Γ (\ θ → (x : A θ) → (B (θ , x)))
    id : ∀ {Γ A} (A* : Ty Γ A) (M N : Tm Γ A) → Ty Γ (\ θ → interp M θ == interp N θ)
    w : ∀ {Γ A B} → (A* : Ty Γ A) (B* : Ty Γ B) → Ty (Γ , A) (\ θ → B (fst θ))
    subst1 : ∀ {Γ A B} → {A* : Ty Γ A} (B* : Ty (Γ , A) B)
               (M : Tm Γ A) → Ty Γ (\ θ → B (θ , interp M θ))

  data Tm where
    v    : ∀ {Γ A} → Tm (Γ , A) (\ θ -> A (fst θ))
    w    : ∀ {Γ A B} → {A* : Ty Γ A} {B* : Ty Γ B} → Tm Γ B → Tm (Γ , A) (\ θ -> B (fst θ))
    true : ∀ {Γ} → Tm Γ (\ _ -> Bool)
    false : ∀ {Γ} → Tm Γ (\ _ -> Bool)
    unit  : ∀ {Γ} → Tm Γ (\ _ -> Propo)
    void  : ∀ {Γ} → Tm Γ (\ _ -> Propo)
    `∀    : ∀ {Γ} (A : Tm Γ (\ _ -> Propo)) (B : Tm (Γ , (λ θ → (interp A θ))) (\ _ -> Propo)) → Tm Γ (\ _ -> Propo)
    <>    : ∀ {Γ} → Tm Γ (\ _ -> Unit) -- these would work for both the "prop" and "set" unit/void if we had them.  
    abort : ∀ {Γ C} (C* : Ty Γ C) → Tm Γ (\ _ -> Void) → Tm Γ C
    if    : ∀ {Γ C} {C* : Ty (Γ , \ _ -> Bool) C} 
          → Tm Γ (\ θ -> C (θ , True))
          → Tm Γ (\ θ -> C (θ , False)) 
          → (x : Tm Γ (\ _ -> Bool)) → Tm Γ (\ θ -> C (θ , interp x θ))
    lam  : ∀ {Γ A B} -- FIXME {A* : Ty Γ A} {B* : Ty (Γ , A) B} 
         → Tm (Γ , A) B → Tm Γ (\ θ → (x : A θ ) → B (θ , x))
    app  : ∀ {Γ A} {B : Σ A → Type} -- FIXME {A* : Ty Γ A} {B* : Ty (Γ , A) B} 
         → Tm Γ (\ θ → (x : A θ) → B (θ , x)) → (M : Tm Γ A) → Tm Γ (\ θ → B (θ , interp M θ))
    refl : ∀ {Γ A} -- FIXME (A* : Ty Γ A)
           (M : Tm Γ A) → Tm Γ (\ θ → interp M θ == interp M θ) 
    tr   : ∀ {Γ A} {C : Σ A → Type} -- FIXME {A* : Ty Γ A} (C* : Ty (Γ , A) C) 
             {M1 M2 : Tm Γ A} (α : Tm Γ (\ θ → interp M1 θ == interp M2 θ)) 
         →  Tm Γ (\ θ → C (θ , interp M1 θ))
         →  Tm Γ (\ θ → C (θ , interp M2 θ))
    uap  : ∀ {Γ} {P : Tm Γ (\ _ -> Propo)} {Q : Tm Γ (\ _ -> Propo)} 
           (f : Tm (Γ , \ θ -> interp P θ) (\ θ → interp Q (fst θ)))
           (g : Tm (Γ , \ θ -> interp Q θ) (\ θ → interp P (fst θ)))
           → Tm Γ (\ θ -> interp P θ == interp Q θ)
    lam=  : ∀ {Γ A} {B : Σ A → Type} -- FIXME {A* : Ty Γ A} {B* : Ty (Γ , A) B} 
           (f g : Tm Γ (\ θ → (x : A θ) → B (θ , x)))
           (α : Tm (Γ , A) (\ θ → interp f (fst θ) (snd θ) == interp g (fst θ) (snd θ)))
           → Tm Γ (\ θ → interp f θ == interp g θ)

  interp v θ = snd θ
  interp (w M) θ = interp M (fst θ)
  interp true _ = True
  interp false _ = False
  interp unit _ = Unit
  interp void _ = Void
  interp (`∀ A B) θ = (x : interp A θ) -> interp B (θ , x)
  interp <> θ = <>
  interp (abort _ M) θ = Sums.abort (interp M θ)
  interp (if{Γ}{C}{C*} M1 M2 M) θ = if (λ x → (C (θ , x))) / interp M θ then interp M1 θ else (interp M2 θ) 
  interp (lam M) θ = λ x → interp M (θ , x)
  interp (app M N) θ = (interp M θ) (interp N θ)
  interp (refl M) θ = id
  interp (tr{Γ}{A}{C} α N) θ = transport (λ x → C (θ , x)) (interp α θ) (interp N θ)
  interp (uap f g) θ = ua (improve (hequiv (λ x → interp f (θ , x)) (λ y → interp g (θ , y)) FIXME1 FIXME2))  where
    -- could demand that propos are hprops
    postulate FIXME1 : _
              FIXME2 : _
  interp (lam= f g α) θ = λ≃ (λ x → interp α (θ , x))

  -- contexts of syntactic types
  Ctx* : Ctx → MetaType 
  Ctx* · = Unit
  Ctx* (Γ , A) = Ctx* Γ × Ty Γ A 

{-
  test : Ty · (λ _ → (x : Unit) → Unit)
  test = (proof (`∀ unit unit))

  test2 : Tm · (λ _ → (x : Unit) → Unit)
  test2 = lam v
-}


  -- definition and proof of reducibility

  RC : ∀ {Γ} → (Γ* : Ctx* Γ) (θ : ElC Γ) → MetaType
  R : ∀ {Γ A} (Γ* : Ctx* Γ) (A* : Ty Γ A) → {θ : ElC Γ} → RC Γ* θ → (A θ) → MetaType
  Q : ∀ {Γ A} (Γ* : Ctx* Γ) (A* : Ty Γ A) → {θ : ElC Γ} → (rθ : RC Γ* θ) 
    → {M N : A θ} → R Γ* A* rθ M → R Γ* A* rθ N → (α : M == N) → MetaType
  fund : ∀ {Γ A θ} (Γ* : Ctx* Γ) (A* : Ty Γ A) (rθ : RC Γ* θ) → (M : Tm Γ A) → R Γ* A* rθ (interp M θ)
{-
  -- workaround scoping rules
  R-proof : ∀ {Γ} (Γ* : Ctx* Γ) (φ : Tm Γ (\ _ -> Propo)) {θ : ElC Γ} (rθ : RC Γ* θ) (pf : interp φ θ) → MetaType
-}

  RC {·} <> θ = Unit
  RC {Γ , A} (Γ* , A*) (θ , M) = Σ (λ (sθ : RC Γ* θ) → R Γ* A* sθ M)

  R _ bool rθ M = Either (M == True) (M == False)
  R Γ* prop rθ φ = Σ \ (Rφ : (φ' : Type) → φ == φ' → φ' → MetaType) → 
                       (φ' : Type) (α : φ == φ') → (p1 p2 : φ') → p1 == p2 → Rφ φ' α p1 → Rφ φ' α p2 -- has a transport function
  R Γ* (proof M) rθ pf = {! R-proof Γ* M rθ pf !}
  R Γ* (Π{Γ}{A}{B} A* B*) {θ} rθ M = (N : (A θ)) (rN : R Γ* A* rθ N) → R (Γ* , A*) B* (rθ , rN) (M N)
  R (Γ* , _) (w A* B*) {θ , _} (rθ , _) M = 
    R Γ* B* rθ M
  R Γ* (subst1{Γ}{A0}{B}{A0*} B* M0) {θ} rθ M = 
    R (Γ* , A0*) B* (rθ , fund _ A0* rθ M0) M
  R Γ* (id A* M N) rθ α = Q Γ* A* rθ (fund Γ* A* rθ M) (fund Γ* A* rθ N) α

  -- R-proof Γ* φ rθ pf = fst (fund Γ* prop rθ φ) _ id pf

  -- is this an hprop in the metalanguage?
  Q Γ* bool rθ rM rN α = Unit  -- FIXME: should we insist that it's refl?
  Q Γ* prop rθ rM rN α = ((x : _) → fst rM _ id x → fst rN _ id (coe α x)) × ((y : _) → fst rN _ id y → fst rM _ id (coe (! α) y))
  Q Γ* (proof M) rθ rM rN α = Unit
  Q Γ* (Π A* B*) rθ rM rN α = (x : _) (rx : R Γ* A* rθ x) → Q (Γ* , A*) B* (rθ , rx) (rM _ rx) (rN _ rx) (ap≃ α)
  Q Γ* (id A* M N) rθ rM rN α = Unit
  Q Γ* (w A* B*) rθ rM rN α = Q (fst Γ*) B* (fst rθ) rM rN α
  Q Γ* (subst1{_}{_}{_}{A0*} B* M) rθ rM rN α = Q (Γ* , A0*) B* (rθ , fund Γ* A0* rθ M) rM rN α

{-
  -- proof that R is well-defined on Γ₀(A θ), without using transport.  
  -- FIXME do we need to know that it is a bijection?

  transportQ : ∀ {Γ A} (Γ* : Ctx* Γ) (A* : Ty Γ A) → {θ : ElC Γ} → (rθ : RC Γ* θ) 
             → {M N : A θ} → (rM : R Γ* A* rθ M) → (rN : R Γ* A* rθ N) → {α α' : M == N} (p : α == α')
             → Q Γ* A* rθ rM rN α → Q Γ* A* rθ rM rN α'
  transportQ Γ* bool rθ rM rN p q = <>
  transportQ Γ* prop rθ rM rN p q = (λ x rx → snd rN _ id _ _ (ap (λ z → transport (λ x₁ → x₁) z x) p) (fst q _ rx)) , {!!}
  transportQ Γ* (proof M) rθ rM rN p q = <>
  transportQ Γ* (Π A* B*) rθ rM rN p q = (λ x rx → transportQ (Γ* , A*) B* (rθ , rx) (rM _ rx) (rN _ rx) (ap (λ z → ap≃ z {x}) p) (q x rx))
  transportQ Γ* (id A* M N) rθ rM rN p q = <>
  transportQ Γ* (w A* B*) rθ rM rN p q = transportQ (fst Γ*) B* (fst rθ) rM rN p q
  transportQ Γ* (subst1{_}{_}{_}{A0*} B* M) rθ rM rN p q = transportQ (Γ* , A0*) B* (rθ , fund Γ* A0* rθ M) rM rN p q

  transportR : ∀ {Γ A θ M M'} (Γ* : Ctx* Γ) (A* : Ty Γ A) (rθ : RC Γ* θ) → M == M' → 
               R Γ* A* rθ M → R Γ* A* rθ M'
  transportR Γ* bool rθ p (Inl x) = Inl (x ∘ ! p)
  transportR Γ* bool rθ p (Inr x) = Inr (x ∘ ! p)
  transportR Γ* prop rθ p rφ = (λ φ' q x → fst rφ φ' (q ∘ p) x) , (λ φ' φ=φ' pf1 pf2 α rpf1 → snd rφ _ (φ=φ' ∘ p) pf1 pf2 α rpf1)  
  transportR Γ* (proof M) rθ p rM = snd (fund Γ* prop rθ M) _ id _ _ p rM 
  transportR Γ* (Π A* B*) rθ p rM = λ N rn → transportR (Γ* , A*) B* (rθ , rn) (ap≃ p) (rM N rn) 
  transportR (Γ* , A*) (w A1* A2*) rθ p rM = transportR Γ* A2* (fst rθ) p rM
  transportR Γ* (subst1{Γ}{A0}{B}{A0*} B* M0) rθ p rM = transportR (Γ* , A0*) B* (rθ , _) p rM
  transportR Γ* (id A* M* N*) rθ p rα = transportQ Γ* A* rθ (fund Γ* A* rθ M*) (fund Γ* A* rθ N*) p rα
-}

{-
  fund-<> : ∀ {Γ θ} → (Γ* : Ctx* Γ) (rθ : RC Γ* θ) → R Γ* (proof unit) rθ <>
  fund-abort : ∀ {Γ θ C} → (Γ* : Ctx* Γ) (rθ : RC Γ* θ) → Tm Γ (\ _ -> Void) → C


  fund-refl : ∀ {Γ A} (Γ* : Ctx* Γ) (A* : Ty Γ A) → {θ : ElC Γ} → (rθ : RC Γ* θ) 
       → {M : A θ} → (rM : R Γ* A* rθ M) 
       → Q Γ* A* rθ rM rM id

  fund-tr : ∀ {Γ A C θ M1 M2 α N} (Γ* : Ctx* Γ) {A* : Ty Γ A} (C* : Ty (Γ , A) C) (rθ : RC Γ* θ)
          (rM1 : R Γ* A* rθ M1) (rM2 : R Γ* A* rθ M2) 
          (rα : Q Γ* A* rθ rM1 rM2 α) (rN : R (Γ* , A*) C* (rθ , rM1) N)
          → R (Γ* , A*) C* (rθ , rM2) (transport (\ x → C (θ , x)) α N)
-}

  fund Γ* A* rθ M = {!A*!} -- unclear what to split!  

{-
  fund (Γ* , A0*) A* (rθ , rM) v = coe FIXME rM where
    -- need coherence for two typing derivations for Ty Γ A
    -- primitive primTrustMe : {l : Level} {A : Set} {x y : A} -> x == y
    FIXME = {!!}
  fund (Γ* , A0*) A1* (rθ , rM) (w {Γ} {A} {B} {A*} {B*} M) = {! fund Γ* B* rθ M !}
  fund Γ* bool rθ true = Inl id
  fund Γ* bool rθ false = Inr id
  fund Γ* prop rθ unit = (λ _ _ _ → Unit) , (λ φ' α p1 p2 x x₁ → <>)
  fund Γ* prop rθ void = (λ _ _ _ → Void) , (λ φ' α p1 p2 x x₁ → x₁)
  fund {θ = θ} Γ* .prop rθ (`∀ φ ψ) = 
    (λ φ' p x → (y : interp φ θ) → (ry : fst (fund Γ* prop rθ φ) _ id y) → fst (fund (Γ* , proof φ) prop (rθ , ry) ψ) _ id (coe (! p) x y)) , 
    (λ φ' α p1 p2 q w y ry → snd (fund (Γ* , proof φ) prop (rθ , ry) ψ) (interp ψ (θ , y)) id (coe (! α) p1 y) (coe (! α) p2 y) (ap (λ z → coe (! α) z y) q) (w y ry))
  fund Γ* (proof unit) rθ <> = fund-<> Γ* rθ
  fund Γ* A* rθ (abort M) = fund-abort Γ* rθ M
  fund {θ = θ} Γ* .(subst1 C* M) rθ (if {Γ} {C} {C*} M1 M2 M) with interp M θ | (fund Γ* bool rθ M)
  ... | i | Inl x = transportR (Γ* , bool) C* (rθ , Inl x) (path-induction
                                                              (λ i₁ x₁ →
                                                                 transport (λ x₂ → C (θ , x₂)) x₁ (interp M1 θ) ==
                                                                 if (λ x₂ → C (θ , x₂)) / i₁ then interp M1 θ else (interp M2 θ))
                                                              id (! x)) 
                               (fund-tr{_}{_}{_}{_}{_}{_}{ ! x }{_} Γ* C* rθ (fund Γ* bool rθ true) (Inl x) <>  (fund Γ* _ rθ M1)) 
                -- Note: is this path-induction kosher?
                --       it seems like it's in a spot where we just need a path in the language!
  ... | i | Inr x = transportR (Γ* , bool) C* (rθ , Inr x) (path-induction
                                                              (λ i₁ x₁ →
                                                                 transport (λ x₂ → C (θ , x₂)) x₁ (interp M2 θ) ==
                                                                 if (λ x₂ → C (θ , x₂)) / i₁ then interp M1 θ else (interp M2 θ))
                                                              id (! x)) 
                               (fund-tr{_}{_}{_}{_}{_}{_}{ ! x }{_} Γ* C* rθ (fund Γ* bool rθ false) (Inr x) <>  (fund Γ* _ rθ M2)) 
  fund Γ* .(Π A* B*) rθ (lam {Γ} {A} {B} {A*} {B*} M) = λ N rN → fund (Γ* , A*) B* (rθ , rN) M
  fund Γ* .(subst1 B* N) rθ (app {Γ} {A} {B} {A*} {B*} M N) = fund Γ* (Π A* B*) rθ M _ (fund Γ* A* rθ N)
  fund Γ* .(id A* M* M*) rθ (refl{_}{_}{A*} M*) = fund-refl Γ* A* rθ (fund Γ* A* rθ M*)
  fund Γ* ._ rθ (tr{Γ}{A}{C}{A*} C* {M1}{M2} α N) = fund-tr Γ* C* rθ (fund Γ* _ rθ M1) (fund Γ* _ rθ M2) (fund Γ* _ rθ α) (fund Γ* _ rθ N)
  fund {θ = θ} Γ* ._ rθ (uap{Γ}{P}{Q} f* g*) = ?
{-
       (λ x rx → snd (fund Γ* prop rθ Q) _ id (interp f* (θ , x)) (coe (interp (uap{P = P}{Q = Q} f* g*) θ) x) 
                     (! (ap≃ (type≃β (interp-uap-eqv{P = P}{Q = Q} f* g* θ))))
                     (fund (Γ* , proof P) (w (proof P) (proof Q)) (rθ , rx) f*)) , 
       (λ x rx → snd (fund Γ* prop rθ P) _ id (interp g* (θ , x)) (coe (! (interp (uap{P = P}{Q = Q} f* g*) θ)) x) 
                     (! (ap≃ (type≃β! (interp-uap-eqv{P = P}{Q = Q} f* g* θ))))
                     (fund (Γ* , proof Q) (w (proof Q) (proof P)) (rθ , rx) g*)) 
  fund Γ* ._ rθ (lam= f* g* α*) = {!!}
-}

  fund-<> Γ* rθ = <>
  fund-abort Γ* rθ M = Sums.abort (fund Γ* (proof void) rθ M)
-}


{-
  fund-refl Γ* bool rθ rM = <>
  fund-refl Γ* prop rθ rM = (λ x rx → rx) , (λ x rx → rx)
  fund-refl Γ* (proof M) rθ rM = <>
  fund-refl Γ* (Π A* B*) rθ rM = λ x rx → fund-refl (Γ* , A*) B* (rθ , rx) (rM _ rx)
  fund-refl Γ* (id A* M N) rθ rM = <>
  fund-refl Γ* (w A* B*) rθ rM = fund-refl (fst Γ*) B* (fst rθ) rM
  fund-refl Γ* (subst1{_}{_}{_}{A0*} B* M) rθ rM = fund-refl (Γ* , A0*) B* (rθ , fund Γ* A0* rθ M) rM

  fund-sym : ∀ {Γ A θ M N α} (Γ* : Ctx* Γ) (A* : Ty Γ A) (rθ : RC Γ* θ)
               (rM : R Γ* A* rθ M) (rN : R Γ* A* rθ N)
           → Q Γ* A* rθ rM rN α
           → Q Γ* A* rθ rN rM (! α)
  fund-sym Γ* bool rθ rM rN rα = <>
  fund-sym {α = α} Γ* prop rθ rM rN rα = snd rα , (λ x rx → snd rN _ id _ _ (ap (λ z → coe z x) (! (!-invol α))) (fst rα x rx))
  fund-sym Γ* (proof M) rθ rM rN rα = <>
  fund-sym {α = α} Γ* (Π A* B*) rθ rM rN rα = λ x rx → transportQ (Γ* , A*) B* (rθ , rx) _ _ (! (ap-! (λ f → f x) α))
                                               (fund-sym (Γ* , A*) B* (rθ , rx) (rM x rx) (rN x rx) (rα x rx))
  fund-sym Γ* (id A* M N) rθ rM rN rα = <>
  fund-sym Γ* (w A* B*) rθ rM rN rα = fund-sym (fst Γ*) B* (fst rθ) rM rN rα
  fund-sym Γ* (subst1{_}{_}{_}{A*} B* M) rθ rM rN rα = fund-sym (Γ* , A*) B* (rθ , _) rM rN rα

  fund-trans : ∀ {Γ A θ M N O α β} (Γ* : Ctx* Γ) (A* : Ty Γ A) (rθ : RC Γ* θ)
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
  fund-trans Γ* (w A* B*) rθ rM rN rO qMN qNO = fund-trans (fst Γ*) B* (fst rθ) rM rN rO qMN qNO
  fund-trans Γ* (subst1{_}{_}{_}{A*} B* M) rθ rM rN rO qMN qNO = fund-trans (Γ* , A*) B* (rθ , _) rM rN rO qMN qNO

  fund-tr {α = α} Γ* bool rθ rM1 rM2 rα (Inl x) = Inl (x ∘ ap≃ (transport-constant α))
  fund-tr {α = α} Γ* bool rθ rM1 rM2 rα (Inr x) = Inr (x ∘ ap≃ (transport-constant α))
  fund-tr {α = α} Γ* prop rθ rM1 rM2 rα rN = (λ φ' p x' → fst rN φ' (p ∘ ! (ap≃ (transport-constant α))) x') , (λ φ' p x1' x2' eq rx1 → snd rN φ' _ x1' x2' eq rx1)
  fund-tr {α = α} Γ* (proof M) rθ rM1 rM2 rα rN = snd (fund (Γ* , _) prop (rθ , rM2) M) _ id _ _ (! (ap≃ (transport-ap-assoc (λ x → interp M (_ , x)) α))) 
                                                      (fst ap-is-reducible _ rN) where
          ap-is-reducible : Q Γ* prop rθ (fund (Γ* , _) prop (rθ , rM1) M) (fund (Γ* , _) prop (rθ , rM2) M) (ap (\ x -> interp M (_ , x)) α)
          ap-is-reducible = {!!}
  fund-tr {Γ}{A0}{._}{θ}{M1}{M2}{α}{f} Γ* {A0*} (Π{.(Γ , A0)}{A}{B} A* B*) rθ rM1 rM2 rα rf = 
          λ x rx → {!fund-tr Γ* B* ? (rf _ (fund-tr Γ* A* rθ rM2 rM1 ? rx)) !} -- need Sigmas / generalization to contexts
  fund-tr {θ = θ} Γ* (id C* M N) rθ rM1 rM2 rα rN = {!!} -- need composition and ap and !
  fund-tr {α = α} Γ* (w A* B*) rθ rM1 rM2 rα rN = transportR Γ* B* rθ (! (ap≃ (transport-constant α))) rN
  fund-tr Γ* (subst1 B* M) rθ rM1 rM2 rα rN = {!!} 

  canonicity : (M : Tm · bool) → Either (interp M <> == True) (interp M <> == False)
  canonicity M = fund <> bool <> M

-}