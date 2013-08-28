{-# OPTIONS --type-in-type --no-termination-check --no-positivity-check #-}

open import lib.Prelude 
open import lib.PathOver
open BoolM 
import lib.PrimTrustMe
open import computational-interp.hcanon.HSetLang-PathOver

module computational-interp.hcanon.HSetProof-PathOver where

  Propo = Type -- really small hprops?

  record Candidate (P : Propo) : MetaType where
   constructor cand
   field 
    redP            : (Q : Propo) → P == Q → Q → MetaType
    -- redP respects paths in all positions
    -- (this is what you would get if it were (Σ \ Q -> P == Q × Q) → Type)
    transportPfull : {Q1 Q2 : Propo} {α1 : P == Q1} {α2 : P == Q2} {p1 : Q1} {p2 : Q2}
                     (propo : Q1 == Q2) (path : propo ∘ α1 == α2) (elt : coe propo p1 == p2)
                   → redP Q1 α1 p1 → redP Q2 α2 p2
   -- special case: redP respects homotopy of elements
   transportP      : (Q : Propo) (α : P == Q) → (p1 p2 : Q) → p1 == p2 → redP Q α p1 → redP Q α p2
   transportP _ α _ _ β r = transportPfull id (∘-unit-l α) β r
  open Candidate

  transportCand : (P Q : Propo) → P == Q → Candidate P → Candidate Q
  transportCand P Q α (cand rP trP) = cand (λ Q₁ p q1 → rP Q₁ (p ∘ α) q1) 
                                           (λ {Q1} {Q2} {α1} {α2} {p1} {p2} propo path elt rp1 → 
                                              trP (α2 ∘ ! α1)
                                                  (coh1 α α1 α2) 
                                                  (! (ap (λ x → coe x p1) (move-right-right propo α1 α2 path) ∘ ! elt))
                                                  rp1) where
                coh1 : ∀ {A} {P Q Q1 Q2 : A} → (α : P == Q) (α1 : Q == Q1) (α2 : Q == Q2)
                     → ((α2 ∘ ! α1) ∘ α1 ∘ α) == (α2 ∘ α)
                coh1 id id id = id

  -- ----------------------------------------------------------------------
  -- definition of reducibility

  RC : ∀ {Γ} → (Γ* : Ctx Γ) (θ : Γ) → MetaType
  QC : ∀ {Γ θ1 θ2} → (Γ* : Ctx Γ) (rθ1 : RC Γ* θ1) (rθ2 : RC Γ* θ2) (δ : θ1 == θ2) → MetaType

  R : ∀ {Γ A} (Γ* : Ctx Γ) (A* : Ty Γ* A) → {θ : Γ} → RC Γ* θ → (A θ) → MetaType
  QOver : ∀ {Γ θ1 θ2 δ A M1 M2} {Γ* : Ctx Γ} {rθ1 : RC Γ* θ1} {rθ2 : RC Γ* θ2} 
          (rδ : QC Γ* rθ1 rθ2 δ)
          (A* : Ty Γ* A) → R Γ* A* rθ1 M1 → R Γ* A* rθ2 M2 → (α : PathOver A δ M1 M2) → MetaType

  fund : ∀ {Γ A θ} (Γ* : Ctx Γ) (A* : Ty Γ* A) (rθ : RC Γ* θ) (M : Tm Γ* A*) → R Γ* A* rθ (interp M θ)
  funds : ∀ {Γ Γ' θ} (Γ* : Ctx Γ) (Γ'* : Ctx Γ') (rθ : RC Γ* θ) (θ'* : Subst Γ* Γ'*) → RC Γ'* (interps θ'* θ)
  fundps : ∀ {Γ Γ' θ} (Γ* : Ctx Γ) (Γ'* : Ctx Γ') (rθ : RC Γ* θ) (θ1* θ2* : Subst Γ* Γ'*) (δ : PathSubst θ1* θ2*) 
         → QC Γ'* (funds Γ* Γ'* rθ θ1*) (funds Γ* Γ'* rθ θ2*) (interpps δ θ)

  fund-transport : ∀ {Γ' C θ1 θ2 δ N} (Γ'* : Ctx Γ') (C* : Ty Γ'* C) 
          (rθ1 : RC Γ'* θ1) (rθ2 : RC Γ'* θ2) 
          (rδ : QC Γ'* rθ1 rθ2 δ) 
          (rN : R Γ'* C* rθ1 N) 
        → R Γ'* C* rθ2 (transport C δ N)

  fund-ap : ∀ {Γ' B θ1 θ2 δ} 
           (Γ'* : Ctx Γ') {B* : Ty Γ'* B} (f : Tm Γ'* B*) (rθ1 : RC Γ'* θ1) (rθ2 : RC Γ'* θ2)
           (rδ : QC Γ'* rθ1 rθ2 δ)
          → QOver rδ B* (fund Γ'* B* rθ1 f) (fund Γ'* B* rθ2 f) (apdo (interp f) δ)

  fund-aps : ∀ {Γ Γ' θ1 θ2 δ} (Γ* : Ctx Γ) {Γ'* : Ctx Γ'} (θ'* : Subst Γ* Γ'*)
           (rθ1 : RC Γ* θ1) (rθ2 : RC Γ* θ2) (rδ : QC Γ* rθ1 rθ2 δ)
           → QC Γ'* (funds Γ* Γ'* rθ1 θ'*) (funds Γ* Γ'* rθ2 θ'*) (ap (interps θ'*) δ)

  postulate
    fund-transport! : ∀ {Γ' C θ1 θ2 δ N} (Γ'* : Ctx Γ') (C* : Ty Γ'* C) 
            (rθ1 : RC Γ'* θ1) (rθ2 : RC Γ'* θ2) 
            (rδ : QC Γ'* rθ1 rθ2 δ) 
            (rN : R Γ'* C* rθ2 N) 
          → R Γ'* C* rθ1 (transport C (! δ) N)

  fund-refls : ∀ {Γ θ} → (Γ* : Ctx Γ) (rθ : RC Γ* θ) → QC Γ* rθ rθ id

  data LikeRefls : ∀ {Γ θ1} (Γ* : Ctx Γ) (rθ1 : RC Γ* θ1) (δ : QC Γ* rθ1 rθ1 id) → Set 

  fund-refl-over : ∀ {Γ C θ1 N} (Γ* : Ctx Γ) (C* : Ty Γ* C) 
           (rθ1 : RC Γ* θ1) (rN : R Γ* C* rθ1 N) 
           → QOver (fund-refls _ rθ1) C* rN rN id

  RC · θ = Unit
  RC (Γ* , A*) (θ , M) = Σ (λ (sθ : RC Γ* θ) → R Γ* A* sθ M)

  QC · _ _ δ = Unit
  QC {._} {θ1 , M1} {θ2 , M2}  (Γ* , A*) (rθ1 , rM1) (rθ2 , rM2) δ = 
    Σ \ α → Σ \ β → (δ == (pair= α β)) × Σ (λ (rδ : QC Γ* rθ1 rθ2 α) → QOver rδ A* rM1 rM2 β)

  -- workaround scoping rules
  R-proof : ∀ {Γ} (Γ* : Ctx Γ) (φ : Tm Γ* prop) {θ : Γ} (rθ : RC Γ* θ) (pf : interp φ θ) → MetaType
  R-pathOver : ∀ {Γ θ Δ A} (Γ* : Ctx Γ) (Δ* : Ctx Δ) (A* : Ty Δ* A) (θ1* θ2* : Subst Γ* Δ*) (δ* : PathSubst θ1* θ2*)
                 (M : _) (N : _) (rθ : RC Γ* θ) (α : _) → _

  R _ bool rθ M = Either (M == True) (M == False)
  R Γ* prop rθ P = Candidate P
  R Γ* (proof M) rθ pf = R-proof Γ* M rθ pf
  R Γ* (Π{Γ}{A}{B} A* B*) {θ} rθ M = 
   -- note: quantification over rid is part of a trick to get fund-transport-id without
   -- needing to prove fund-ap-id.  
   Σ \ (rM : (N : (A θ)) (rN : R Γ* A* rθ N) → R (Γ* , A*) B* (rθ , rN) (M N)) →
       ((rid : QC Γ* rθ rθ id) -- FIXME leftover... do we need this quantifer? could just do it for fund-refls
        {N1 N2 : (A θ)} {α : PathOver A id N1 N2} (rN1 : R Γ* A* rθ N1) (rN2 : R Γ* A* rθ N2) 
        (rα : QOver rid A* rN1 rN2 α) 
        → QOver {Γ* = (Γ* , A*)} (id , α , id , rid , rα) B* (rM _ rN1) (rM _ rN2) {!!}) -- FIXME mismatch between total substitutions and not
  R Γ* (pathOver {Δ* = Δ*} A* {θ1* = θ1*} {θ2* = θ2*} δ* M N) rθ α = R-pathOver Γ* Δ* A* θ1* θ2* δ* M N rθ α 
  R ._ (w{Γ* = Γ*} A* B*) {θ , _} (rθ , _) M = 
    R Γ* B* rθ M
  R .Γ* (subst1{Γ}{A0}{B}{Γ*}{A0*} B* M0) {θ} rθ M = 
    R (Γ* , A0*) B* (rθ , fund _ A0* rθ M0) M
  R .Γ* (subst{Γ}{Γ'}{B}{Γ*}{Γ'*} B* θ'*) {θ} rθ M = R Γ'* B* (funds Γ* Γ'* rθ θ'*) M

  R-pathOver Γ* Δ* A* θ1* θ2* δ* M N rθ α = 
    QOver (fundps Γ* Δ* rθ θ1* θ2* δ*) A* (fund Γ* (subst A* θ1*) rθ M) (fund Γ* (subst A* θ2*) rθ N) α
  R-proof Γ* φ rθ pf = redP (fund Γ* prop rθ φ) _ id pf

  QOver rδ bool rM1 rM2 α = Unit
  QOver {δ = δ}{Γ* = Γ*} rδ prop rM1 rM2 α = ((x : _) → redP rM1 _ id x → redP rM2 _ id (fst (coe PathOverType α) x)) ×
                                            ((x : _) → redP rM2 _ id x → redP rM1 _ id (IsEquiv.g (snd (coe PathOverType α)) x))
  QOver rδ (proof M) rM1 rM2 α = Unit
  QOver {Γ* = Γ*} {rθ1 = rθ1} {rθ2 = rθ2} rδ (Π A* B*) rM1 rM2 α = 
    ∀ {N1 N2 β} (rN1 : R _ A* _ N1) (rN2 : R _ A* _ N2)
      (rβ : QOver rδ A* rN1 rN2 β) →
      QOver {Γ* = Γ* , A*} {rθ1 = rθ1 , rN1} {rθ2 = rθ2 , rN2} (_ , _ , id , rδ , rβ) B* (fst rM1 _ rN1) (fst rM2 _ rN2) (coe PathOverΠ α _ _ β)
  QOver rδ (pathOver _ _ _ _) rM1 rM2 α = Unit
  QOver {δ = δ} rδ (subst {A = A} A* θ'*) rM1 rM2 α = QOver (fund-aps _ θ'* _ _ rδ) A* rM1 rM2 {!!}
  QOver (δ1 , α1 , eq , rδ1 , rα1) (w A* A*₁) rM1 rM2 α = QOver rδ1 A*₁ rM1 rM2 {!!}
  QOver {δ = δ} rδ (subst1 {B = B} A*₁ M) rM1 rM2 α = QOver (_ , _ , id , rδ , fund-ap _ M _ _ rδ) A*₁ rM1 rM2 {!!}

  -- ----------------------------------------------------------------------
  -- transport for R/Q

  postulate
    transportR : ∀ {Γ A θ M M'} (Γ* : Ctx Γ) (A* : Ty Γ* A) (rθ : RC Γ* θ) → M == M' → 
               R Γ* A* rθ M → R Γ* A* rθ M'
    transportQOver : ∀ {Γ θ1 θ2 δ A M1 M2} {Γ* : Ctx Γ} {rθ1 : RC Γ* θ1} {rθ2 : RC Γ* θ2} 
          (rδ : QC Γ* rθ1 rθ2 δ)
          (A* : Ty Γ* A) → (rM : R Γ* A* rθ1 M1) → (rN : R Γ* A* rθ2 M2) → {α α' : PathOver A δ M1 M2} (p : α == α')
          → QOver rδ A* rM rN α → QOver rδ A* rM rN α'
{-  EDIT
    transportRQ : ∀ {Γ A θ M1 M2} {α : M1 == M2} (Γ* : Ctx Γ) (A* : Ty Γ* A) (rθ : RC Γ* θ) (rM1 : R Γ* A* rθ M1) 
              → Q Γ* A* rθ (transportR Γ* A* rθ α rM1) rM1 (! α)
-}

  {- PERF
  transportR Γ* bool rθ p (Inl x) = Inl (x ∘ ! p)
  transportR Γ* bool rθ p (Inr x) = Inr (x ∘ ! p)
  transportR Γ* prop rθ p rφ = cand (λ φ' q x → redP rφ φ' (q ∘ p) x) 
                                    (λ {Q1}{Q2}{α1}{α2}{p2}{p2} propo path elt rp1 → 
                                       transportPfull rφ propo (propo ∘ α1 ∘ p ≃〈 ap (λ x → x ∘ p) path ∘ ∘-assoc propo α1 p 〉 (α2 ∘ p ∎)) 
                                                      elt rp1)
  transportR Γ* (proof M) rθ p rM = transportP (fund Γ* prop rθ M) _ id _ _ p rM 
  transportR Γ* (Π A* B*) rθ p rM = (λ N rn → transportR (Γ* , A*) B* (rθ , rn) (ap≃ p) (fst rM N rn)) , {!!}
  transportR ._ (w {Γ* = Γ*} A1* A2*) rθ p rM = transportR Γ* A2* (fst rθ) p rM
  transportR Γ* (subst1{Γ}{A0}{B}{._}{A0*} B* M0) rθ p rM = transportR (Γ* , A0*) B* (rθ , _) p rM
  transportR Γ* (id A* M* N*) rθ p rα = transportQ Γ* A* rθ (fund Γ* A* rθ M*) (fund Γ* A* rθ N*) p rα
  transportR Γ* (subst{Γ}{Γ'}{B}{._}{Γ'*} B* θ'*) rθ p rM = transportR Γ'* B* (funds Γ* Γ'* rθ θ'*) p rM

  transportQ Γ* bool rθ rM rN p q = <>
  transportQ Γ* prop rθ rM rN p q = (λ x rx → transportP rN _ id _ _ (ap (λ z → transport (λ x₁ → x₁) z x) p) (fst q _ rx)) , 
                                   (λ y ry → transportP rM _ id _ _ (ap (λ z → transport (λ x₁ → x₁) (! z) y) p) (snd q _ ry))
  transportQ Γ* (proof M) rθ rM rN p q = <>
  transportQ Γ* (Π A* B*) rθ rM rN p q = (λ x rx → transportQ (Γ* , A*) B* (rθ , rx) (fst rM _ rx) (fst rN _ rx) (ap (λ z → ap≃ z {x}) p) (q x rx))
  transportQ Γ* (id A* M N) rθ rM rN p q = <>
  transportQ ._ (w{Γ* = Γ*} A* B*) rθ rM rN p q = transportQ Γ* B* (fst rθ) rM rN p q
  transportQ .Γ* (subst1{_}{_}{_}{Γ*}{A0*} B* M) rθ rM rN p q = transportQ (Γ* , A0*) B* (rθ , fund Γ* A0* rθ M) rM rN p q
  transportQ .Γ* (subst{_}{_}{_}{Γ*}{Γ'*} B* θ'*) rθ rM rN p q = transportQ Γ'* B* (funds Γ* Γ'* rθ θ'*) rM rN p q

  transportRQ Γ* bool rθ rM1 = <>
  transportRQ {M1 = P} {M2 = Q} {α = α} Γ* prop rθ rP = (λ q rq → transportPfull rP (! α) (!-inv-l α ∘ ∘-assoc (! α) id α) id rq) , (λ p rp → transportPfull rP α (! (∘-unit-l α)) (ap (λ x → coe x p) (! (!-invol α))) rp)
  transportRQ Γ* (proof M) rθ rM1 = <>
  transportRQ {α = α} Γ* (Π A* A*₁) rθ rM1 = λ x rx → transportQ (Γ* , A*) A*₁ (rθ , rx) _ _ (! (ap-! (λ f → f x) α))
                                                        (transportRQ {α = ap (λ f → f x) α} (Γ* , A*) A*₁ (rθ , rx)
                                                         (fst rM1 x rx))
  transportRQ Γ* (id A* M N) rθ rM1 = <>
  transportRQ .(Γ* , A*) (w {Γ} {A} {B} {Γ*} A* A*₁) rθ rM1 = transportRQ Γ* A*₁ (fst rθ) rM1
  transportRQ Γ* (subst1 {A* = A*} B* M) rθ rM1 = transportRQ (Γ* , A*) B* (rθ , fund Γ* A* rθ M) rM1
  transportRQ _ (subst B* θ) rθ rM1 = transportRQ _ B* (funds _ _ rθ θ) rM1
  -}

  -- definitionally equal types give coercable R's
  -- FIXME it's no longer true that these are actually definitionally equal,
  -- because of the Q components of R_Pi---e.g. there are transportR's in different places
  -- for different definitionally equal types (see the case for unlam, e.g.).  
  -- But maybe we can still get a coercion here?
  postulate
    R-deq : ∀ {Γ A θ M} (Γ* : Ctx Γ) (A* A1* : Ty Γ* A) (rθ : RC Γ* θ) → R Γ* A* rθ M → R Γ* A1* rθ M
    -- R-deq Γ* A* A1* rθ = lib.PrimTrustMe.unsafe-cast

  -- ----------------------------------------------------------------------

  fund-refl-over Γ* bool rθ1 rN = <>
  fund-refl-over Γ* prop rθ1 rN = (λ x rx → transportP rN _ _ _ _ {!!} rx) , (λ y ry → {!!})
  fund-refl-over Γ* (proof M) rθ1 rN = <>
  fund-refl-over Γ* (Π C* C*₁) rθ1 rN = λ {N1} {N2} {β} rN1 rN2 rβ → transportQOver _ C*₁ _ _ {!!} (snd rN (fund-refls Γ* rθ1) rN1 rN2 rβ)
  fund-refl-over Γ* (pathOver C* δ* M N) rθ1 rN = <>
  fund-refl-over Γ* (subst C* θ'*) rθ1 rN = {!fund-refl-over _ C* ? rN!}
  fund-refl-over .(Γ* , C*) (w {Γ} {A} {B} {Γ*} C* C*₁) rθ1 rN = {!!}
  fund-refl-over Γ* (subst1 C*₁ M) rθ1 rN = {!!}

  -- ----------------------------------------------------------------------
  -- fundamental theorem

{-PERF
  fund-<> : ∀ {Γ θ} → (Γ* : Ctx Γ) (rθ : RC Γ* θ) → R Γ* (proof unit) rθ <>
  fund-<>⁺ : ∀ {Γ θ} → (Γ* : Ctx Γ) (rθ : RC Γ* θ) → R Γ* (proof unit⁺) rθ <>⁺
  fund-abort : ∀ {Γ θ C} → (Γ* : Ctx Γ) (rθ : RC Γ* θ) → Tm Γ* (proof void) → C
-}

{- FIXME later
  fund-lam= : ∀ {Γ A B} (Γ* : Ctx Γ) (A* : Ty Γ* A) (B* : Ty (Γ* , A*) B)
              (f g : Tm Γ* (Π A* B*))
              (α : Tm (Γ* , A*) (id B* (unlam f) (unlam g)))
              {θ : Γ} (rθ : RC Γ* θ)
            → (x : _) (rx : _) → _
-}

{-
  fund-split1 : ∀ {Γ θ} (Γ* : Ctx Γ) {C : _} (C* : Ty (Γ* , proof unit⁺) C)
          → (M1 : Tm Γ* (subst1 C* <>⁺) )
          → (M : Tm Γ* (proof unit⁺))
          → (rθ : RC Γ* θ)
          → R Γ* (subst1 C* M) rθ (interp (split1 C* M1 M) θ)
-}


  fund-transport-left : ∀ {Γ C θ1 θ2 δ N} (Γ* : Ctx Γ) (C* : Ty Γ* C) 
           (rθ1 : RC Γ* θ1) (rθ2 : RC Γ* θ2) (rδ : QC Γ* rθ1 rθ2 δ)
           (rN : R Γ* C* rθ2 N) 
         → QOver rδ C* (fund-transport! Γ* C* rθ1 rθ2 rδ rN) rN (PathOver-transport-left C δ)

{- edit
  fund-sym : ∀ {Γ A θ M N α} (Γ* : Ctx Γ) (A* : Ty Γ* A) (rθ : RC Γ* θ)
               (rM : R Γ* A* rθ M) (rN : R Γ* A* rθ N)
           → Q Γ* A* rθ rM rN α
           → Q Γ* A* rθ rN rM (! α)
-}

  fund-transport-proof : ∀ {Γ' θ1 θ2 δ} (Γ'* : Ctx Γ') (P* : Tm Γ'* prop) 
          (rθ1 : RC Γ'* θ1) (rθ2 : RC Γ'* θ2) 
          (rδ : QC Γ'* rθ1 rθ2 δ) {N : _}
          (rN : R Γ'* (proof P*) rθ1 N) 
        → R Γ'* (proof P*) rθ2 (transport (interp P*) δ N)

  fund-transport {δ = δ} Γ'* bool rθ1 rθ2 rδ (Inl x) = Inl (x ∘ ap≃ (transport-constant δ))
  fund-transport {δ = δ} Γ'* bool rθ1 rθ2 rδ (Inr x) = Inr (x ∘ ap≃ (transport-constant δ))
  fund-transport {δ = δ} Γ'* prop rθ1 rθ2 rδ rN = transportCand _ _ (! (ap≃ (transport-constant δ))) rN
  fund-transport {δ = δ} {N = N} Γ'* (proof M) rθ1 rθ2 rδ rN = fund-transport-proof Γ'* M rθ1 rθ2 rδ rN
  fund-transport {δ = δ} {N = f} Γ'* (Π {A = A} {B = B}A* B*) rθ1 rθ2 rδ rf = 
    (λ x rx → transportR (Γ'* , A*) B* (rθ2 , rx) {!!}
                (fund-transport (Γ'* , A*) B*
                   (rθ1 , fund-transport! Γ'* A* rθ1 rθ2 rδ rx) (rθ2 , rx)
                   (δ , _ , id , rδ , fund-transport-left Γ'* A* rθ1 rθ2 rδ rx)
                   (fst rf _ (fund-transport! Γ'* A* rθ1 rθ2 rδ rx)))) , 
    {!!}
  fund-transport {δ = δ} {N = β} Γ* (pathOver C* δ'* M N) rθ1 rθ2 rδ rβ = {!!}
{- FIXME
    transportQ Γ* C* rθ2 (fund Γ* C* rθ2 M) (fund Γ* C* rθ2 N)
               (! (transport-Path-d (interp M) (interp N) δ β))
               (fund-trans Γ* C* rθ2 _ _ _ (fund-trans Γ* C* rθ2 _ _ _ !rMα aprβ) rNα) where
          rMα : Q Γ* C* rθ2
                 (fund-transport Γ* C* rθ1 rθ2 rδ (fund Γ* C* rθ1 M))
                 (fund Γ* C* rθ2 M) (apd (interp M) δ)
          rMα = {!fund-ap Γ* M rθ1 rθ2 rδ!} -- NOW fund-ap Γ* {C*} M rθ1 rθ2 rδ

          !rMα : Q Γ* C* rθ2
                 (fund Γ* C* rθ2 M)
                 (fund-transport Γ* C* rθ1 rθ2 rδ (fund Γ* C* rθ1 M)) (! (apd (interp M) δ))
          !rMα = fund-sym Γ* C* rθ2 _ _ rMα

          rNα : Q Γ* C* rθ2
                 (fund-transport Γ* C* rθ1 rθ2 rδ (fund Γ* C* rθ1 N))
                 (fund Γ* C* rθ2 N) (apd (interp N) δ)
          rNα = {!!} -- NOW fund-ap Γ* {C*} N rθ1 rθ2 rδ

          aprβ : Q Γ* C* rθ2
                 (fund-transport Γ* C* rθ1 rθ2 rδ (fund Γ* C* rθ1 M))
                 (fund-transport Γ* C* rθ1 rθ2 rδ (fund Γ* C* rθ1 N))
                 (ap (transport C δ) β)
          aprβ = fund-aptransport Γ* C* rθ1 rθ2 rδ (fund Γ* C* rθ1 M) (fund Γ* C* rθ1 N) rβ
-}
  fund-transport {δ = δ} Γ* (subst {A = A} {Γ'* = Γ'*} C* θ'*) rθ1 rθ2 rδ rN = transportR Γ'* C* (funds Γ* Γ'* rθ2 θ'*) (! (ap≃ (transport-ap-assoc' A (interps θ'*) δ))) (fund-transport Γ'* C* _ _ (fund-aps Γ* θ'* rθ1 rθ2 rδ) rN) 
  fund-transport {δ = δ} .(Γ* , A*) (w {Γ} {A} {B} {Γ*} A* B*) rθ1 rθ2 (δ' , α' , eq , rδ' , rα') rN = 
    transportR Γ* B* (fst rθ2) {!!} 
                  (fund-transport Γ* B* _ _ rδ' rN) 
  fund-transport {δ = δ} Γ'* (subst1 {B = B} {A* = A*} C* M) rθ1 rθ2 rδ rN = {!!}
{-
    transportR (Γ'* , A*) C* (rθ2 , fund Γ'* A* rθ2 M) (transport-apd-assoc δ (interp M) B) 
               (fund-transport (Γ'* , A*) C* _ _ (_ , _ , id , rδ , fund-ap Γ'* M _ _ rδ) rN)
-}

  fund-transport-proof {δ = δ} Γ'* M rθ1 rθ2 rδ {N = N} rN = transportP (fund Γ'* prop rθ2 M) _ _ _ _ {!coh!}
                                                               (fst (fund-ap Γ'* M rθ1 rθ2 rδ) N rN)

  fund-transport-left Γ* bool rθ1 rθ2 rδ rN = <>
  fund-transport-left Γ* prop rθ1 rθ2 rδ rN = (λ x rx → {!transportPfull rN!}) , {!!}
  fund-transport-left Γ* (proof M) rθ1 rθ2 rδ rN = <>
  fund-transport-left Γ* (Π C* C*₁) rθ1 rθ2 rδ rN = {!!}
  fund-transport-left Γ* (pathOver C* δ* M* N*) rθ1 rθ2 rδ rN = <>
  fund-transport-left Γ* (subst C* θ'*) rθ1 rθ2 rδ rN = {!!}
  fund-transport-left .(Γ* , C*) (w {Γ} {A} {B} {Γ*} C* C*₁) rθ1 rθ2 rδ rN = {!!}
  fund-transport-left Γ* (subst1 C*₁ M) rθ1 rθ2 rδ rN = {!!}

{-
  fund-tr1-bool : ∀ {Γ C θ M1 M2 α N} (Γ* : Ctx Γ) (C* : Ty (Γ* , bool) C) (rθ : RC Γ* θ)
          (rM1 : R Γ* bool rθ M1) (rM2 : R Γ* bool rθ M2) 
          (rα : Q Γ* bool rθ rM1 rM2 α) 
          (rN : R (Γ* , bool) C* (rθ , rM1) N)
        → R (Γ* , bool) C* (rθ , rM2) (transport (\ x → C (θ , x)) α N)
  fund-tr1-bool {C = C} {α = α} Γ* C* rθ rM1 rM2 rα rN = 
    transportR (Γ* , bool) C* (rθ , rM2) (transport-pair≃-assoc α C)
      (fund-transport (Γ* , bool) C* (rθ , rM1) (rθ , rM2) (id , α , id , fund-refls Γ* rθ , <>) rN)
-}
{- PERF
  fund-tr1-unit⁺ : ∀ {Γ C θ M1 M2 α N} (Γ* : Ctx Γ) (C* : Ty (Γ* , (proof unit⁺)) C) (rθ : RC Γ* θ)
          (rM1 : R Γ* (proof unit⁺) rθ M1) (rM2 : R Γ* (proof unit⁺) rθ M2) 
          (rα : Q Γ* (proof unit⁺) rθ rM1 rM2 α) 
          (rN : R (Γ* , (proof unit⁺)) C* (rθ , rM1) N)
        → R (Γ* , (proof unit⁺)) C* (rθ , rM2) (transport (\ x → C (θ , x)) α N)
  fund-tr1-unit⁺ {C = C} {α = α} Γ* C* rθ rM1 rM2 rα rN = {!!}
  {-
    transportR (Γ* , proof unit⁺) C* (rθ , rM2) (transport-pair≃-assoc α C)
      (fund-transport (Γ* , proof unit⁺) C* (rθ , rM1) (rθ , rM2) 
               (transportQC Γ* rθ rθ (! (Σ≃β1 id α)) (fund-refls Γ* rθ) , <>)  -- easy because Q_unit⁺ is Unit
               rN) 
  -}
-}

  fund .(Γ* , A*) .(w A* A*) (rθ , rM) (v {Γ} {A} {Γ*} {A*}) = rM
  fund .(Γ* , A*) .(w A* B*) (rθ , rM) (w {Γ} {A} {B} {Γ*} {A*} {B*} M) = fund Γ* B* rθ M
{-
  fund Γ* .bool rθ true = Inl id
  fund Γ* .bool rθ false = Inr id
  fund Γ* .prop rθ unit = cand (λ _ _ _ → Unit) (λ propo path elt x → <>) 
  fund Γ* .prop rθ unit⁺ = cand (λ ψ p x → coe (! p) x == <>⁺) 
                                (λ {Q1} {Q2} {α1} {α2} {p1} {p2} prop₁ path elt red1 → 
                                   red1 ∘ (coh α1 prop₁ ∘ ap (λ x → coe (! x) (coe prop₁ p1)) (! path)) ∘ ap (coe (! α2)) (! elt)) where
       coh : {x y z : Type} (p : x == y) (q : y == z) {m : _} →
           coe (! (q ∘ p)) (coe q m) == coe (! p) m
       coh id id = id
  fund Γ* .prop rθ void = cand (λ _ _ _ → Void) (λ propo path elt x → x) 
  --   fund {θ = θ} Γ* .prop rθ (`∀ φ ψ) = 
  --     cand (λ φ' p x → (y : interp φ θ) → (ry : redP (fund Γ* prop rθ φ) _ id y) → redP (fund (Γ* , proof φ) prop (rθ , ry) ψ) _ id (coe (! p) x y)) 
  --          {!!} 
  --         (λ φ' α p1 p2 q w y ry → transportP (fund (Γ* , proof φ) prop (rθ , ry) ψ) (interp ψ (θ , y)) id (coe (! α) p1 y) (coe (! α) p2 y) (ap (λ z → coe (! α) z y) q) (w y ry))
  fund Γ* .(proof unit) rθ <> = fund-<> Γ* rθ
  fund Γ* A* rθ (abort M) = fund-abort Γ* rθ M
  fund {θ = θ} .Γ* .(subst1 C* M) rθ (if {Γ} {C} {Γ*} {C*} M1 M2 M) with interp M θ | (fund Γ* bool rθ M)
  ... | i | Inl x = transportR (Γ* , bool) C* (rθ , Inl x) (path-induction
                                                              (λ i₁ x₁ →
                                                                 transport (λ x₂ → C (θ , x₂)) x₁ (interp M1 θ) ==
                                                                 if (λ x₂ → C (θ , x₂)) / i₁ then interp M1 θ else (interp M2 θ))
                                                              id (! x)) 
                               (fund-tr1-bool{_}{_}{_}{_}{_}{ ! x }{_}  Γ* C* rθ (fund Γ* bool rθ true) (Inl x) <>  (fund Γ* _ rθ M1)) 
                -- see split1 for a cleaner version
  ... | i | Inr x = transportR (Γ* , bool) C* (rθ , Inr x) (path-induction
                                                              (λ i₁ x₁ →
                                                                 transport (λ x₂ → C (θ , x₂)) x₁ (interp M2 θ) ==
                                                                 if (λ x₂ → C (θ , x₂)) / i₁ then interp M1 θ else (interp M2 θ))
                                                              id (! x)) 
                               (fund-tr1-bool{_}{_}{_}{_}{_}{ ! x }{_} Γ* C* rθ (fund Γ* bool rθ false) (Inr x) <>  (fund Γ* _ rθ M2)) 
-}
  fund .Γ* .(Π A* B*) rθ (lam {Γ} {A} {B} {Γ*} {A*} {B*} M) =
    (λ N rN → fund (Γ* , A*) B* (rθ , rN) M) , 
    (λ rid {N1} {N2} {α} rN1 rN2 rα → transportQOver _ B* _ _ {!!} (fund-ap (Γ* , A*) M (rθ , rN1) (rθ , rN2) (id , α , id , rid , rα))) 
  fund .Γ* .(subst1 B* N) rθ (app {Γ} {A} {B} {Γ*} {A*} {B*} M N) = fst (fund Γ* (Π A* B*) rθ M) _ (fund Γ* A* rθ N)
{-
  fund .Γ* .(id A* M* M*) rθ (refl{_}{_}{Γ*}{A*} M*) = fund-refl Γ* A* rθ (fund Γ* A* rθ M*)
-}
  fund .Γ* ._ rθ (tr{Γ}{A}{C}{Γ*}{Γ'*} C* {θ1}{θ2} δ N) = fund-transport Γ'* C* (funds Γ* Γ'* rθ θ1) (funds Γ* Γ'* rθ θ2) (fundps Γ* Γ'* rθ θ1 θ2 δ) (fund Γ* _ rθ N) 
{-PERF
  fund {θ = θ} .Γ* ._ rθ (uap{Γ}{Γ*}{P}{Q} f* g*) = 
       (λ x rx → transportP (fund Γ* prop rθ Q) _ id (interp f* (θ , x)) (coe (interp (uap{P = P}{Q = Q} f* g*) θ) x) 
                     (! (ap≃ (type≃β (interp-uap-eqv{P = P}{Q = Q} f* g* θ))))
                     (fund (Γ* , proof P) (w (proof P) (proof Q)) (rθ , rx) f*)) , 
       (λ x rx → transportP (fund Γ* prop rθ P) _ id (interp g* (θ , x)) (coe (! (interp (uap{P = P}{Q = Q} f* g*) θ)) x) 
                     (! (ap≃ (type≃β! (interp-uap-eqv{P = P}{Q = Q} f* g* θ))))
                     (fund (Γ* , proof Q) (w (proof Q) (proof P)) (rθ , rx) g*)) 
-}
--  fund Γ* ._ rθ (lam={A* = A*}{B* = B*} f* g* α*) = λ x rx → fund-lam= Γ*  A* B* f* g* α* rθ x rx
{-PERF
  fund .Γ* .A* rθ (deq{Γ}{A}{Γ*}{A1*}{A*} M) = R-deq Γ* A1* A* rθ (fund Γ* A1* rθ M) 
  fund Γ* ._ rθ <>⁺ = fund-<>⁺ Γ* rθ
  fund Γ* ._ rθ (split1 C* M1 M) = fund-split1 Γ* C* M1 M rθ 
-}
  fund ._ B* rθ (unlam {Γ* = Γ*} {A* = A*} M) = fst (fund Γ* (Π A* B*) (fst rθ) M) _ (snd rθ)
  fund _ _ _ _ = {!!}

{-PERF
  fund-<> Γ* rθ = <>
  fund-<>⁺ Γ* rθ = id
  fund-abort Γ* rθ M = Sums.abort (fund Γ* (proof void) rθ M)
-}
  -- fund-lam= Γ* A* B* f* g* α* rθ x rx = transportQ (Γ* , A*) B* (rθ , rx) (fst (fund Γ* (Π A* B*) rθ f*) x rx)
  --                                        (fst (fund Γ* (Π A* B*) rθ g*) x rx) (! (Π≃β (λ x₁ → interp α* (_ , x₁)))) 
  --                                        (fund (Γ* , A*) _ (rθ , rx) α*) 

{- PERF
  fund-split1 {θ = θ} Γ* {C} C* M1 M rθ = transportR (Γ* , proof unit⁺) C* (rθ , (fund Γ* (proof unit⁺) rθ M)) (apd (split1⁺ (λ x → C (θ , x)) (interp M1 θ)) (! (fund Γ* (proof unit⁺) rθ M))) 
                                          (fund-tr1-unit⁺ {α = ! (fund Γ* (proof unit⁺) rθ M)}
                                                  Γ* C* rθ id (fund Γ* (proof unit⁺) rθ M) <>  -- uses the fact that all paths are reducible in Prooff(-)
                                                  (fund Γ* (subst1 C* <>⁺) rθ M1))
-}

  data LikeRefls where 
    Like· : LikeRefls · <> <> 
    Like, : ∀ {Γ A θ1 M} {Γ* : Ctx Γ} {rθ1 : RC Γ* θ1} {A* : Ty Γ* A} {rM : R Γ* A* rθ1 M}
              {rδ1 : QC Γ* rθ1 rθ1 id}  {rα1 : _} 
          → LikeRefls Γ* rθ1 rδ1 
          → LikeRefls (Γ* , A*) (rθ1 , rM) (id , id , id , rδ1 , rα1)

  fund-refls · rθ = <>
  fund-refls (Γ* , A*) rθ = id , id , id , fund-refls Γ* (fst rθ) , fund-refl-over Γ* A* (fst rθ) (snd rθ)

  funds Γ* .· rθ · = <>
  funds Γ* ._ rθ (θ'* , M) = funds Γ* _ rθ θ'* , fund _ _ rθ M

  fundps Γ* · rθ θ1* θ2* δ = <>
  fundps Γ* (Γ'* , A) rθ (θ1* , M1) (θ2* , M2) (δ* , α*) = 
    _ , _ , id , fundps Γ* Γ'* rθ θ1* θ2* δ* , fund Γ* (pathOver A δ* M1 M2) rθ α*
  fundps Γ* Γ'* rθ θ1* ._ refls = fund-refls Γ'* (funds Γ* Γ'* rθ θ1*)

  fund-aps Γ* · rθ1 rθ2 rδ = <>
  fund-aps Γ* (_,_ {Γ'* = Γ'*} {A* = A*} θ'* M) rθ1 rθ2 rδ = _ , _ , {!coh!} , fund-aps Γ* θ'* rθ1 rθ2 rδ , fund-ap _ M rθ1 rθ2 rδ

  fund-ap .(Γ* , A*) (v {Γ} {A} {Γ*} {A*}) rθ1 rθ2 (δ1 , α , eq , rδ1 , rα) = transportQOver _ A* _ _ {!!} rα 
  fund-ap .(Γ* , A*) (w {Γ} {A} {B} {Γ*} {A*} {B*} f) rθ1 rθ2 (δ1 , α , eq , rδ1 , rα) = 
    transportQOver _ B* _ _ {!!} (fund-ap Γ* f (fst rθ1) (fst rθ2) rδ1)
{-PERF
  fund-ap Γ* true rθ1 rθ2 rδ = <>
  fund-ap Γ* false rθ1 rθ2 rδ = <>
  fund-ap Γ* unit rθ1 rθ2 rδ = (λ x x₁ → <>) , (λ y x → <>) 
  fund-ap Γ* unit⁺ rθ1 rθ2 rδ = {!!}
  {-
  fund-ap {α = α} Γ* unit⁺ rθ rM1 rM2 rα = (λ x x₁ → coh α x₁) , {!!} where
    coh : {M1 M2 : _} (α : M1 == M2)  {x : transport (λ x₂ → Set) α Unit⁺} 
          (x₁ : Path (transport (λ x₂ → x₂) (! (id ∘ ! (ap (λ f → f Unit⁺) (transport-constant α)))) x) <>⁺)
        → Path (transport (λ x₂ → x₂) (apd (λ x₂ → Unit⁺) α) x) <>⁺
    coh id x₁ = x₁
  -}
  fund-ap Γ* void rθ1 rθ2 rδ = (λ x x₁ → x₁) , (λ y x → x) -- PERF 
  -- fund-ap Γ* (`∀ f f₁) rθ1 rθ2 rδ = {!!}
  fund-ap Γ* <> rθ1 rθ2 rδ = <>
  fund-ap Γ* <>⁺ rθ1 rθ2 rδ = <>
  fund-ap Γ* (split1 C* f f₁) rθ1 rθ2 rδ = {!!}
  fund-ap Γ* (abort f) rθ1 rθ2 rδ = Sums.abort (fund Γ* (proof void) rθ1 f) -- PERF 
  -- fund-ap Γ* (plam f₂) rθ1 rθ2 rδ = <>
  -- fund-ap Γ* (papp f₂ f₃) rθ1 rθ2 rδ = <>
  fund-ap Γ* (if f f₁ f₂) rθ1 rθ2 rδ = {!!}
  fund-ap {δ = δ} Γ* (lam {A = A} {A* = A*} {B* = B*} f) rθ1 rθ2 rδ = 
    (λ x rx → transportQ (Γ* , A*) B* (rθ2 , rx) _ _ {!!} (fund-trans (Γ* , A*) B* (rθ2 , rx) _ _ _ (transportRQ (Γ* , A*) B* (rθ2 , rx) _) (fund-ap (Γ* , A*) f (rθ1 , fund-transport! Γ* A* rθ1 rθ2 rδ rx) (rθ2 , rx) (δ , transport-inv-2' A δ , id , rδ , fund-transport-inv-2 Γ* A* rθ1 rθ2 rδ rx))))
-}
  fund-ap Γ* (app {A* = A*} {B* = B*} f f₁) rθ1 rθ2 rδ = 
    transportQOver _ B* _ _ {!!} (fund-ap Γ* f _ _ rδ _ _ (fund-ap Γ* f₁ _ _ rδ))
  fund-ap Γ* (tr C* α f) rθ1 rθ2 rδ = {!!}
{-
  fund-ap Γ* (refl f) rθ1 rθ2 rδ = <>
  fund-ap Γ* (uap f₂ f₃) rθ1 rθ2 rδ = <>
-}
{-
  fund-ap ._ (unlam {Γ* = Γ*} {A* = A*} {B* = B*} M) (rθ1 , rM1) (rθ2 , rM2) (δ1 , α1 , eq , rδ1 , rα1) = ?
    transportQ (Γ* , A*) B* rθ2 _ _ {!!} 
      (fund-trans (Γ* , A*) B* rθ2 _ _ _ (fund-trans (Γ* , A*) B* rθ2 _ _ _ (coe {!!}
                                                                              (fund-sym (Γ* , A*) B* _ _ _ 
                                                                               (snd (fund Γ* (Π A* B*) (fst rθ1) M) (fund-refls Γ* (fst rθ1))
                                                                                (fund-transport! Γ* A* (fst rθ1) (fst rθ2) rδ1 (snd rθ2)) (snd rθ1)
                                                                                (fund-trans Γ* A* (fst rθ1) _ _ _ (fund-transport-id Γ* A* (fst rθ1) (fund-refls Γ* (fst rθ1)) {!!}
                                                                                                                     (fund-transport! Γ* A* (fst rθ1) (fst rθ2) rδ1 (snd rθ2)))
                                                                                   (fund-sym Γ* A* (fst rθ1) _ _
                                                                                    (fund-transport-adjunction Γ* A* (fst rθ1) (fst rθ2) rδ1 (snd rθ1)
                                                                                     (snd rθ2) rα1))))))
                                            (fund-sym (Γ* , A*) B* rθ2 _ _ (transportRQ (Γ* , A*) B* rθ2 _)))
         (fund-ap Γ* M (fst rθ1) (fst rθ2) rδ1 _ (snd rθ2)))
-}

  fund-ap Γ* (deq f) rθ1 rθ2 rδ = {!fund-ap Γ* f rθ1 rθ2 rδ!}
  fund-ap Γ* _ rθ1 rθ2 rδ = {!!}
{-
  fund-ap Γ* (lam= f f₁ f₂) rθ1 rθ2 rδ = <>
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
