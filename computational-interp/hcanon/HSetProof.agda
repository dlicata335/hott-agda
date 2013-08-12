{-# OPTIONS --type-in-type --no-termination-check #-}

open import lib.Prelude 
open BoolM 
import lib.PrimTrustMe
open import computational-interp.hcanon.HSetLang

module computational-interp.hcanon.HSetProof where

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
--  R Γ* _ rθ p = {!!}

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
--  Q Γ* _ rθ rM rN α = {!!}

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
--  transportQ Γ* _ rθ rM rN p q = {!!}

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
--  transportR Γ* _ rθ p q = {!!}

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
          (rα : Q Γ* A* rθ rM1 rM2 α) 
          (rN : R (Γ* , A*) C* (rθ , rM1) N)
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
  fund-refl ._ (ex{Γ* = Γ*} A* B* C*) rθ rM = fund-refl _ C* _ rM

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
  fund-sym ._ (ex _ _ C*) rθ rM rN rα = fund-sym _ C* _ rM rN rα

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
  fund-trans ._ (ex _ _ C*) rθ rM rN rO qMN qNO = fund-trans _ C* _ rM rN rO qMN qNO

  fund-ap : ∀ {Γ A B θ M1 M2 α} 
           (Γ* : Ctx Γ) {A* : Ty Γ* A} {B* : Ty (Γ* , A*) B} (f : Tm (Γ* , A*) B*) (rθ : RC Γ* θ)
           (rM1 : R Γ* A* rθ M1) (rM2 : R Γ* A* rθ M2) 
           (rα : Q Γ* A* rθ rM1 rM2 α)
          → Q (Γ* , A*) B* (rθ , rM2) 
              (fund-tr Γ* B* rθ rM1 rM2 rα (fund (Γ* , A*) B* (rθ , rM1) f)) 
              (fund (Γ* , A*) B* (rθ , rM2) f) 
              (apd (\ x -> interp f (θ , x)) α)

  transportRQ : ∀ {Γ A θ M1 M2} {α : M1 == M2} (Γ* : Ctx Γ) (A* : Ty Γ* A) (rθ : RC Γ* θ) (rM1 : R Γ* A* rθ M1) 
              → Q Γ* A* rθ (transportR Γ* A* rθ α rM1) rM1 (! α)
  transportRQ Γ* bool rθ rM1 = <>
  transportRQ {M1 = P} {M2 = Q} Γ* prop rθ rP = (λ q rq → {!!}) , {!!}
  transportRQ Γ* (proof M) rθ rM1 = <>
  transportRQ {α = α} Γ* (Π A* A*₁) rθ rM1 = λ x rx → transportQ (Γ* , A*) A*₁ (rθ , rx) _ _ (! (ap-! (λ f → f x) α))
                                                        (transportRQ {α = ap (λ f → f x) α} (Γ* , A*) A*₁ (rθ , rx)
                                                         (rM1 x rx))
  transportRQ Γ* (id A* M N) rθ rM1 = <>
  transportRQ .(Γ* , A*) (w {Γ} {A} {B} {Γ*} A* A*₁) rθ rM1 = transportRQ Γ* A*₁ (fst rθ) rM1
  transportRQ Γ* (subst1 A*₁ M) rθ rM1 = {!!}
  transportRQ .((Γ* , A*₁) , w A*₁ A*) (ex {Γ} {A} {B} {C} {Γ*} A* A*₁ A*₂) rθ rM1 = {!!}

{-
  fund-transport-constant : ∀ {Γ A θ M1 M2} (Γ* : Ctx Γ) (A* : Ty Γ* A) (rθ : RC Γ* θ) (rM1 : R Γ* A* rθ M1) (rM2 : R Γ* A* rθ M2) (α : M1 == M2)
                          → Q Γ* A* rθ (transportR Γ* A* rθ (! (ap≃ (transport-constant α))) rM1) rM1 (ap≃ (transport-constant α))
  fund-transport-constant Γ* bool rθ rM1 rM2 α = <>
  fund-transport-constant Γ* prop rθ rM1 rM2 α = (λ x x₁ → {!snd rM1!}) , {!transport-constant α!}
  fund-transport-constant Γ* (proof M) rθ rM1 rM2 α = <>
  fund-transport-constant Γ* (Π A* A*₁) rθ rM1 rM2 α = λ x rx → {!!} -- need some generalization
  fund-transport-constant Γ* (id A* M N) rθ rM1 rM2 α = <>
  fund-transport-constant .(Γ* , A*) (w {Γ} {A} {B} {Γ*} A* A*₁) rθ rM1 rM2 α = {!!}
  fund-transport-constant Γ* (subst1 A*₁ M) rθ rM1 rM2 α = {!!}
  fund-transport-constant .((Γ* , A*₁) , w A*₁ A*) (ex {Γ} {A} {B} {C} {Γ*} A* A*₁ A*₂) rθ rM1 rM2 α = {!!}
-}

  fund-ap1 : ∀ {Γ A B θ M1 M2 α} (Γ* : Ctx Γ) {A* : Ty Γ* A} {B* : Ty Γ* B} (f : Tm (Γ* , A*) (w _ B*)) (rθ : RC Γ* θ)
           (rM1 : R Γ* A* rθ M1) (rM2 : R Γ* A* rθ M2) 
          → Q Γ* A* rθ rM1 rM2 α
          → Q Γ* B* rθ (fund (Γ* , A*) (w _ B*) (rθ , rM1) f) (fund (Γ* , A*) (w _ B*) (rθ , rM2) f) (ap (\ x -> interp f (θ , x)) α)

  {-
  fund-apd-to-ap : ∀ {Γ A θ M1 M2} {B : Γ → Type} {α f} (Γ* : Ctx Γ) (A* : Ty Γ* A)
                   (rθ : RC Γ* θ) (rM1 : R Γ* A* rθ M1) (rM2 : R Γ* A* rθ M2) 
                   (rα : Q Γ* A* rθ rM1 rM2 α) 
                 → (B* : Ty (Γ* , A*) (B o fst)) 
                 → (f : Tm (Γ* , A*) B*)
                 → Q (Γ* , A*) B* (rθ , rM2)
                   (fund-tr Γ* B* rθ rM1 rM2 rα (fund (Γ* , A*) B* (rθ , rM1) f))
                   (fund (Γ* , A*) B* (rθ , rM2) f)
                   (apd (λ x → interp f (θ , x)) α)
                 → Q (Γ* , A*) B* (rθ , rM2)
                   (fund (Γ* , A*) B* (rθ , rM1) f)
                   (fund (Γ* , A*) B* (rθ , rM2) f)
                   (ap (λ x → interp f (θ , x)) α)
  -}
  {-
  Goal: Q Γ* A* rθ
      (transportR Γ* A* rθ (! (ap (λ f → f .M1) (transport-constant α)))
       rM1)
      rM2 (apd (λ x → x) α)
  Have: Q Γ* A* rθ rM1 rM2 α

  Goal : Q Γ* prop rθ (fund (Γ* , _) prop (rθ , rM1) M) (fund (Γ* , _) prop (rθ , rM2) M) (ap (\ x -> interp M (_ , x)) α)
  Have: Q (Γ* , .A*) prop (rθ , rM2)
      (fund-tr Γ* prop rθ rM1 rM2 rα (fund (Γ* , .A*) prop (rθ , rM1) M))
      (fund (Γ* , .A*) prop (rθ , rM2) M)
      (apd (λ x → interp M (.θ , x)) α)

  -}

  -- FIXME: why doesn't this work in --without-K? 
  fund-tr {α = α} Γ* bool rθ rM1 rM2 rα (Inl x) = Inl (x ∘ ap≃ (transport-constant α))
  fund-tr {α = α} Γ* bool rθ rM1 rM2 rα (Inr x) = Inr (x ∘ ap≃ (transport-constant α))
  fund-tr {α = α} Γ* prop rθ rM1 rM2 rα rN = (λ φ' p x' → fst rN φ' (p ∘ ! (ap≃ (transport-constant α))) x') , (λ φ' p x1' x2' eq rx1 → snd rN φ' _ x1' x2' eq rx1)
  fund-tr {α = α} Γ* (proof M) rθ rM1 rM2 rα rN = snd (fund (Γ* , _) prop (rθ , rM2) M) _ id _ _ (! (ap≃ (transport-ap-assoc (λ x → interp M (_ , x)) α))) 
                                                      (fst ap-is-reducible _ rN) where
          ap-is-reducible : Q Γ* prop rθ (fund (Γ* , _) prop (rθ , rM1) M) (fund (Γ* , _) prop (rθ , rM2) M) (ap (\ x -> interp M (_ , x)) α)
          ap-is-reducible = fund-ap1 Γ* (deq {A* = prop} {A'* = w _ prop} M) rθ rM1 rM2 rα -- FIXME need to set things up so that we do the equality test after!

          ap-is-reducible' : Q Γ* prop rθ (fund (Γ* , _) prop (rθ , rM1) M) (fund (Γ* , _) prop (rθ , rM2) M) (ap (\ x -> interp M (_ , x)) α)
          ap-is-reducible' = {! fund-ap Γ* M rθ rM1 rM2 rα !} -- FIXME need to set things up so that we do the equality test after!
  fund-tr {Γ}{A0}{._}{θ}{M1}{M2}{α}{f} Γ* {A0*} (Π{._}{A}{B} A* B*) rθ rM1 rM2 rα rf = 
          λ x rx → {!fund-tr Γ* B* ? (rf _ (fund-tr Γ* A* rθ rM2 rM1 ? rx)) !} -- need Sigmas / generalization to contexts
  fund-tr {θ = θ} {α = α} {N = β} Γ* {A*} (id {A = C} C* M N) rθ rM1 rM2 rα rβ = 
    transportQ (Γ* , A*) C* (rθ , rM2) (fund (Γ* , A*) C* (rθ , rM2) M) (fund (Γ* , A*) C* (rθ , rM2) N)
               (! (transport-Path-d (λ x → interp M (θ , x)) (λ x → interp N (θ , x)) α β))
               (fund-trans (Γ* , A*) C* (rθ , rM2) _ _ _ (fund-trans (Γ* , A*) C* (rθ , rM2) _ _ _ !rMα aprβ) rNα) where
          rMα : Q (Γ* , A*) C* (rθ , rM2)
                 (fund-tr Γ* C* rθ rM1 rM2 rα (fund (Γ* , A*) C* (rθ , rM1) M))
                 (fund (Γ* , A*) C* (rθ , rM2) M) (apd (λ x → interp M (θ , x)) α)
          rMα = fund-ap Γ* {_}{C*} M rθ rM1 rM2 rα

          !rMα : Q (Γ* , A*) C* (rθ , rM2)
                 (fund (Γ* , A*) C* (rθ , rM2) M)
                 (fund-tr Γ* C* rθ rM1 rM2 rα (fund (Γ* , A*) C* (rθ , rM1) M)) (! (apd (λ x → interp M (θ , x)) α))
          !rMα = fund-sym (Γ* , A*) C* (rθ , rM2) _ _ rMα

          rNα : Q (Γ* , A*) C* (rθ , rM2)
                 (fund-tr Γ* C* rθ rM1 rM2 rα (fund (Γ* , A*) C* (rθ , rM1) N))
                 (fund (Γ* , A*) C* (rθ , rM2) N) (apd (λ x → interp N (θ , x)) α)
          rNα = fund-ap Γ* {_}{C*} N rθ rM1 rM2 rα

          aprβ : Q (Γ* , A*) C* (rθ , rM2)
                 (fund-tr Γ* C* rθ rM1 rM2 rα (fund (Γ* , A*) C* (rθ , rM1) M))
                 (fund-tr Γ* C* rθ rM1 rM2 rα (fund (Γ* , A*) C* (rθ , rM1) N))
                 (ap (transport (λ z → C (θ , z)) α) β)
          aprβ = {!(transport (λ z → C (θ , z)) α)!}
--  fund-tr Γ* (subst Γ'* θ'* A₂) rθ rM1 rM2 rα M = {!!}
  fund-tr {α = α} Γ* {A*} (w .A* B*) rθ rM1 rM2 rα rN = transportR Γ* B* rθ (! (ap≃ (transport-constant α))) rN
  fund-tr Γ* (subst1 A₃ M) rθ rM1 rM2 rα M₁ = {!!}
  fund-tr ._ (ex _ _ _) rθ rM1 rM2 rα M₁ = {!!}


  fund-ap {α = α} Γ* {A* = A*} v rθ rM1 rM2 rα = transportQ Γ* A* rθ _ _ (coh α)
                                                   (fund-trans Γ* A* rθ _ _ _
                                                    (transportRQ {α = ! (ap≃ (transport-constant α))} Γ* A* rθ rM1) rα) where
    coh : ∀ {A} {M1 M2 : A} (α : M1 == M2)→ (α ∘ !( ! (ap (λ f → f M1) (transport-constant α)))) == (apd (λ x → x) α)
    coh id = id

  fund-ap Γ* (w f) rθ rM1 rM2 rα = {!fund-ap Γ* f !}
  fund-ap Γ* true rθ rM1 rM2 rα = <>
  fund-ap Γ* false rθ rM1 rM2 rα = <>
  fund-ap Γ* unit rθ rM1 rM2 rα = (λ x x₁ → <>) , (λ y x → <>)
  fund-ap Γ* unit⁺ rθ rM1 rM2 rα = (λ x x₁ → {!!}) , {!!}
  fund-ap Γ* void rθ rM1 rM2 rα = (λ x x₁ → x₁) , (λ y x → x)
  fund-ap Γ* (`∀ f f₁) rθ rM1 rM2 rα = {!!}
  fund-ap Γ* <> rθ rM1 rM2 rα = <>
  fund-ap Γ* <>⁺ rθ rM1 rM2 rα = <>
  fund-ap Γ* (split1 _ f f₁) rθ rM1 rM2 rα = {!!}
  fund-ap Γ* (abort f) rθ rM1 rM2 rα = Sums.abort (fund (Γ* , _) (proof void) (rθ , rM1) f)
  fund-ap Γ* (plam f₂) rθ rM1 rM2 rα = <>
  fund-ap Γ* (papp f₂ f₃) rθ rM1 rM2 rα = <>
  fund-ap Γ* (if f f₁ f₂) rθ rM1 rM2 rα = {!!}
  fund-ap Γ* (lam f) rθ rM1 rM2 rα = {!!}
  fund-ap Γ* (app f f₁) rθ rM1 rM2 rα = {!!}
  fund-ap Γ* (refl f) rθ rM1 rM2 rα = <>
  fund-ap Γ* (tr C* f₂ f₃) rθ rM1 rM2 rα = {!!}
  fund-ap Γ* (uap f₂ f₃) rθ rM1 rM2 rα = <>
  fund-ap Γ* (deq f) rθ rM1 rM2 rα = lib.PrimTrustMe.unsafe-cast (fund-ap Γ* f rθ rM1 rM2 rα) -- FIXME: need some lemma about R-deq
  fund-ap Γ* (lam= f f₁ f₂) rθ rM1 rM2 rα = <>

  fund-ap1 {θ = θ} {α = α} Γ* {B* = B*} f rθ rM1 rM2 rα =
   {! 
   transportQ Γ* B* rθ _ _ {!!}
     (fund-trans Γ* B* rθ _ _ _ (fund-sym Γ* B* rθ _ _ {!coe ? (transportRQ {α = ?} Γ* B* rθ (fund (Γ* , _) (w _ B*) (rθ , rM1) f) (fund (Γ* , _) (w _ B*) (rθ , rM1) f) !}))
      (fund-ap Γ* f rθ rM1 rM2 rα))
    !}
{-
    transportQ Γ* B* rθ _ _ (coh {f = λ x → interp f (θ , x)} α)
       (fund-trans {α = ! (ap≃ (transport-constant α))} Γ* B* rθ _ _ _ 
         (fund-sym Γ* B* rθ _ _ 
           {! !}) 
         (fund-ap Γ* f rθ rM1 rM2 rα)) where
           coh : ∀ {A B} {f : A → B} {M1 M2 : _} (α : M1 == M2) → 
             (apd f α ∘ ! (ap≃ (transport-constant α))) == (ap f α)
           coh id = id
-}
{-
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

  test : canonicity2 example2 == Inl ((id ∘
                                        ap≃ (transport-constant (! (fund · (proof unit⁺) <> example))))
                                       ∘
                                       !
                                       (apd (split1⁺ (λ x → Bool) (interp (deq true) <>))
                                        (! (fund · (proof unit⁺) <> example))))
  test = id
-}