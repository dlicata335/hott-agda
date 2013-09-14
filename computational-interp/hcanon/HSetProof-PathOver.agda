{-# OPTIONS --type-in-type --no-termination-check  #-}

{- BIG ISSUES:
   (1) What to do about definitional equality.
       What's an example where it doesn't come out on the nose?
   (2) Status of the uses of == in the proof...
       What type theory is this about?  Why can we do path induction for δ?
   (3) When do/don't we need consistency?
-}
   
open import lib.Prelude 
open import lib.PathOver
open BoolM 
import lib.PrimTrustMe
open import computational-interp.hcanon.HSetLang-PathOver

module computational-interp.hcanon.HSetProof-PathOver where

  transport-apd-assoc : {A : Type} {a1 a2 : A} 
                        {B : A → Type} 
                        (C : Σ B → Type) (α : a1 == a2) (f : (x : A) → B x) {N : C (a1 , f a1)}
       → transport C (pair= α (apdo f α)) N == transport (\ a -> C (a , f a)) α N
  transport-apd-assoc _ id _ = id

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
  -- types 

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

  fund-refls : ∀ {Γ θ} → (Γ* : Ctx Γ) (rθ : RC Γ* θ) → QC Γ* rθ rθ id

  postulate
    fund-refl : ∀ {Γ C θ1 N} (Γ* : Ctx Γ) (C* : Ty Γ* C) 
               (rθ1 : RC Γ* θ1) (rN : R Γ* C* rθ1 N) 
               → QOver (fund-refls _ rθ1) C* rN rN id
  
    fund-!s : ∀ {Γ θ1 θ2 δ} (Γ* : Ctx Γ)  
               (rθ1 : RC Γ* θ1) (rθ2 : RC Γ* θ2) 
               → QC Γ* rθ1 rθ2 δ
               → QC Γ* rθ2 rθ1 (! δ)
  
    fund-! : ∀ {Γ θ1 θ2 δ C M1 M2 α} {Γ* : Ctx Γ} {rθ1 : RC Γ* θ1} {rθ2 : RC Γ* θ2} (rδ : QC Γ* rθ1 rθ2 δ)
             → (C* : Ty Γ* C) 
               (rM1 : R Γ* C* rθ1 M1) (rM2 : R Γ* C* rθ2 M2) 
               (rα : QOver rδ C* rM1 rM2 α) 
             → QOver (fund-!s Γ* rθ1 rθ2 rδ) C* rM2 rM1 (!o α)
  
    fund-∘s : ∀ {Γ θ1 θ2 θ3 δ2 δ1} (Γ* : Ctx Γ)  
               (rθ1 : RC Γ* θ1) (rθ2 : RC Γ* θ2) (rθ3 : RC Γ* θ3)
               → QC Γ* rθ2 rθ3 δ2 → QC Γ* rθ1 rθ2 δ1
               → QC Γ* rθ1 rθ3 (δ2 ∘ δ1)
    
    fund-∘ : ∀ {Γ θ1 θ2 θ3 δ2 δ1 C M1 M2 M3 α2 α1} {Γ* : Ctx Γ} {rθ1 : RC Γ* θ1} {rθ2 : RC Γ* θ2} {rθ3 : RC Γ* θ3}
                 (rδ2 : QC Γ* rθ2 rθ3 δ2) (rδ1 : QC Γ* rθ1 rθ2 δ1)
                 (C* : Ty Γ* C) 
                 {rM1 : R Γ* C* rθ1 M1} {rM2 : R Γ* C* rθ2 M2} {rM3 : R Γ* C* rθ3 M3}
                 (rα2 : QOver rδ2 C* rM2 rM3 α2) (rα1 : QOver rδ1 C* rM1 rM2 α1) 
               → QOver (fund-∘s Γ* rθ1 rθ2 rθ3 rδ2 rδ1) C* rM1 rM3 (α2 ∘o α1)
    
    fund-changeover : ∀ {Γ θ1 θ2 δ δ' A M1 M2 α} {Γ* : Ctx Γ} {rθ1 : RC Γ* θ1} {rθ2 : RC Γ* θ2} 
              (rδ : QC Γ* rθ1 rθ2 δ) (rδ' : QC Γ* rθ1 rθ2 δ') 
              (A* : Ty Γ* A) (rM1 : R Γ* A* rθ1 M1) (rM2 : R Γ* A* rθ2 M2)
              (eq : δ == δ')
              (rα : QOver rδ A* rM1 rM2 α)
              → QOver rδ' A* rM1 rM2 (changeover A eq α)
  postulate 
    fund-transport : ∀ {Γ' C θ1 θ2 δ N} (Γ'* : Ctx Γ') (C* : Ty Γ'* C) 
              (rθ1 : RC Γ'* θ1) (rθ2 : RC Γ'* θ2) 
              (rδ : QC Γ'* rθ1 rθ2 δ) 
              (rN : R Γ'* C* rθ1 N) 
            → R Γ'* C* rθ2 (transport C δ N)
  
    fund-transport! : ∀ {Γ' C θ1 θ2 δ N} (Γ'* : Ctx Γ') (C* : Ty Γ'* C) 
              (rθ1 : RC Γ'* θ1) (rθ2 : RC Γ'* θ2) 
              (rδ : QC Γ'* rθ1 rθ2 δ) 
              (rN : R Γ'* C* rθ2 N) 
            → R Γ'* C* rθ1 (transport C (! δ) N)
  
    fund-PathOver∘-transport : ∀ {Γ θ1 θ2 θ3 δ2 δ1 A M1 M3 α} {Γ* : Ctx Γ} (A* : Ty Γ* A)
                 {rθ1 : RC Γ* θ1} {rθ2 : RC Γ* θ2} {rθ3 : RC Γ* θ3}
                 (rδ2 : QC Γ* rθ2 rθ3 δ2) (rδ1 : QC Γ* rθ1 rθ2 δ1) {rM1 : R Γ* A* rθ1 M1} {rM3 : R Γ* A* rθ3 M3}
               → QOver (fund-∘s Γ* rθ1 rθ2 rθ3 rδ2 rδ1) A* rM1 rM3 α
               → QOver rδ2 A* (fund-transport Γ* A* rθ1 rθ2 rδ1 rM1) rM3 (coe (PathOver∘-transport A δ1) α)
    
    fund-transport-right : ∀ {Γ C θ1 θ2 δ M} (Γ* : Ctx Γ) (C* : Ty Γ* C) 
               (rθ1 : RC Γ* θ1) (rθ2 : RC Γ* θ2) (rδ : QC Γ* rθ1 rθ2 δ)
               (rM : R Γ* C* rθ1 M) 
             → QOver rδ C* rM (fund-transport Γ* C* rθ1 rθ2 rδ rM) (PathOver-transport-right C δ)
  
    fund-transport-left : ∀ {Γ C θ1 θ2 δ N} (Γ* : Ctx Γ) (C* : Ty Γ* C) 
               (rθ1 : RC Γ* θ1) (rθ2 : RC Γ* θ2) (rδ : QC Γ* rθ1 rθ2 δ)
               (rN : R Γ* C* rθ2 N) 
             → QOver rδ C* (fund-transport! Γ* C* rθ1 rθ2 rδ rN) rN (PathOver-transport-left C δ)
  
  fund-aps : ∀ {Γ Γ' θ1 θ2 δ} (Γ* : Ctx Γ) {Γ'* : Ctx Γ'} (θ'* : Subst Γ* Γ'*)
             (rθ1 : RC Γ* θ1) (rθ2 : RC Γ* θ2) (rδ : QC Γ* rθ1 rθ2 δ)
             → QC Γ'* (funds Γ* Γ'* rθ1 θ'*) (funds Γ* Γ'* rθ2 θ'*) (ap (interps θ'*) δ)
  
  fund-ap : ∀ {Γ' B θ1 θ2 δ} 
             (Γ'* : Ctx Γ') {B* : Ty Γ'* B} (f : Tm Γ'* B*) (rθ1 : RC Γ'* θ1) (rθ2 : RC Γ'* θ2)
             (rδ : QC Γ'* rθ1 rθ2 δ)
            → QOver rδ B* (fund Γ'* B* rθ1 f) (fund Γ'* B* rθ2 f) (apdo (interp f) δ)

{-
  postulate
    -- ap transport to a homogeneous path
    fund-aptransport : ∀ {Γ θ1 θ2 δ C M1 M2 α} {Γ* : Ctx Γ} {rθ1 : RC Γ* θ1} {rθ2 : RC Γ* θ2} (rδ : QC Γ* rθ1 rθ2 δ)
             → (C* : Ty Γ* C) 
               (rM1 : R Γ* C* rθ1 M1) (rM2 : R Γ* C* rθ1 M2) 
               (rα : QOver (fund-refls Γ* rθ1) C* rM1 rM2 α) 
             → QOver (fund-refls Γ* rθ2) C* (fund-transport Γ* C* rθ1 rθ2 rδ rM1)
                                            (fund-transport Γ* C* rθ1 rθ2 rδ rM2) 
                                            {!apdo1 (transport C δ) α!}
-}

  -- ----------------------------------------------------------------------
  -- definition of the relation

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
   Σ \ (rM : (N : (A θ)) (rN : R Γ* A* rθ N) → R (Γ* , A*) B* (rθ , rN) (M N)) →
       ({N1 N2 : (A θ)} {α : PathOver A id N1 N2} (rN1 : R Γ* A* rθ N1) (rN2 : R Γ* A* rθ N2) 
        (rα : QOver (fund-refls Γ* rθ) A* rN1 rN2 α) 
        → QOver {Γ* = (Γ* , A*)} (id , α , id , (fund-refls Γ* rθ) , rα) B* (rM _ rN1) (rM _ rN2) (apdo1 M α))
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
  QOver {δ = δ}{Γ* = Γ*} _ prop rM1 rM2 α = ((x : _) → redP rM1 _ id x → redP rM2 _ id (fst (coe PathOverType α) x)) ×
                                            ((x : _) → redP rM2 _ id x → redP rM1 _ id (IsEquiv.g (snd (coe PathOverType α)) x))
  QOver rδ (proof M) rM1 rM2 α = Unit
  QOver {Γ* = Γ*} {rθ1 = rθ1} {rθ2 = rθ2} rδ (Π A* B*) rM1 rM2 α = 
    ∀ {N1 N2 β} (rN1 : R _ A* _ N1) (rN2 : R _ A* _ N2)
      (rβ : QOver rδ A* rN1 rN2 β) →
      QOver {Γ* = Γ* , A*} {rθ1 = rθ1 , rN1} {rθ2 = rθ2 , rN2} (_ , _ , id , rδ , rβ) B* (fst rM1 _ rN1) (fst rM2 _ rN2) (coe PathOverΠ α _ _ β)
  QOver rδ (pathOver _ _ _ _) rM1 rM2 α = Unit
  QOver {δ = δ} rδ (subst {A = A} A* θ'*) rM1 rM2 α = QOver (fund-aps _ θ'* _ _ rδ) A* rM1 rM2 (over-o-ap A α)
  QOver (δ1 , α1 , eq , rδ1 , rα1) (w {B = B} A* A*₁) rM1 rM2 α = QOver rδ1 A*₁ rM1 rM2 (changeover B (Σ=β1 δ1 α1 ∘ ap (ap fst) eq) (over-o-ap B {fst} α))
  QOver {δ = δ} rδ (subst1 {B = B} A*₁ M) rM1 rM2 α = QOver (_ , _ , id , rδ , fund-ap _ M _ _ rδ) A*₁ rM1 rM2 (over-apd-inverse B δ (interp M) α)

  -- ----------------------------------------------------------------------
  -- transport for R/Q

  -- need this early
  fund-refls · rθ = <>
  fund-refls (Γ* , A*) rθ = id , id , id , fund-refls Γ* (fst rθ) , fund-refl Γ* A* (fst rθ) (snd rθ)

  abstract
    transportR : ∀ {Γ A θ M M'} (Γ* : Ctx Γ) (A* : Ty Γ* A) (rθ : RC Γ* θ) → M == M' → 
               R Γ* A* rθ M → R Γ* A* rθ M'
    transportQOver : ∀ {Γ θ1 θ2 δ A M1 M2} {Γ* : Ctx Γ} {rθ1 : RC Γ* θ1} {rθ2 : RC Γ* θ2} 
          (rδ : QC Γ* rθ1 rθ2 δ)
          (A* : Ty Γ* A) → (rM : R Γ* A* rθ1 M1) → (rN : R Γ* A* rθ2 M2) → {α α' : PathOver A δ M1 M2} (p : α == α')
          → QOver rδ A* rM rN α → QOver rδ A* rM rN α'
    transportRQ : ∀ {Γ A θ M1 M2} {α : M1 == M2} (Γ* : Ctx Γ) (A* : Ty Γ* A) (rθ : RC Γ* θ) (rM1 : R Γ* A* rθ M1) 
              → QOver (fund-refls Γ* rθ) A* (transportR Γ* A* rθ α rM1) rM1 (path-to-pathover A (! α))
  
    QOver-irrel : ∀ {Γ θ1 θ2 δ A M1 M2} {Γ* : Ctx Γ} {rθ1 : RC Γ* θ1} {rθ2 : RC Γ* θ2} 
                (rδ rδ' : QC Γ* rθ1 rθ2 δ)
                (A* : Ty Γ* A) (rM1 : R Γ* A* rθ1 M1) (rM2 : R Γ* A* rθ2 M2) {α : PathOver A δ M1 M2}
              → QOver rδ A* rM1 rM2 α
              → QOver rδ' A* rM1 rM2 α

    transportR Γ* bool rθ p (Inl x) = Inl (x ∘ ! p)
    transportR Γ* bool rθ p (Inr x) = Inr (x ∘ ! p)
    transportR Γ* prop rθ p rφ = cand (λ φ' q x → redP rφ φ' (q ∘ p) x) 
                                      (λ {Q1}{Q2}{α1}{α2}{p2}{p2} propo path elt rp1 → 
                                         transportPfull rφ propo (propo ∘ α1 ∘ p ≃〈 ap (λ x → x ∘ p) path ∘ ∘-assoc propo α1 p 〉 (α2 ∘ p ∎)) 
                                                        elt rp1)
    transportR Γ* (proof M) rθ p rM = transportP (fund Γ* prop rθ M) _ id _ _ p rM 
    transportR {M = M} {M' = M'} Γ* (Π {B = B} A* B*) rθ p rM = 
     (λ N rn → transportR (Γ* , A*) B* (rθ , rn) (ap≃ p) (fst rM N rn)) ,  
     (λ {N1} {_}{α} rn1 rn2 rα → transportQOver _ B* _ _ 
      (path-induction-homo (λ N2 α₁ → transport (λ x → x) (changeover= B (∘-unit-l (pair= id α₁))) (!o (path-to-pathover B (! (ap (λ f → f N2) p))) ∘o path-induction-homo'' (λ x p₁ → PathOver B (pair= id p₁) (M N1) (M x)) id α₁ ∘o path-to-pathover B (! (ap (λ f → f N1) p))) == path-induction-homo'' (λ x p₁ → PathOver B (pair= id p₁) (M' N1) (M' x)) id α₁)
                           (path-induction (λ _ p₁ → !o (path-to-pathover B (! (ap (λ f → f N1) p₁))) ∘o id ∘o path-to-pathover B (! (ap (λ f → f N1) p₁)) == id) 
                                           id p)
                           α)
      (fund-changeover _ _ B* _ _ (∘-unit-l (pair= id _))
                                      (fund-∘ _ _ B* (fund-! _ B* _ _ (transportRQ {α = ap≃ p} _ B* _ (fst rM _ rn2)))
                                       (fund-∘ _ _ B* (snd rM _ _ rα)
                                         (transportRQ {α = ap≃ p} _ B* _ (fst rM _ rn1))))))
    transportR ._ (w {Γ* = Γ*} A1* A2*) rθ p rM = transportR Γ* A2* (fst rθ) p rM
    transportR Γ* (pathOver A* δ* M* N*) rθ p rα = transportQOver _ A* _ _ p rα
    transportR Γ* (subst1{Γ}{A0}{B}{._}{A0*} B* M0) rθ p rM = transportR (Γ* , A0*) B* (rθ , fund Γ* A0* rθ M0) p rM
    transportR Γ* (subst{Γ}{Γ'}{B}{._}{Γ'*} B* θ'*) rθ p rM = transportR Γ'* B* (funds Γ* Γ'* rθ θ'*) p rM
  
    transportQOver rδ bool rM rN p q = <>
    transportQOver rδ prop rM rN p q = (λ x rx → transportP rN _ _ _ _ (ap (λ z → fst (coe PathOverType z) x) p) (fst q _ rx)) ,
                                       (λ x rx → transportP rM _ _ _ _ (ap (λ z → IsEquiv.g (snd (coe PathOverType z)) x) p) (snd q _ rx))
    transportQOver rδ (proof M) rM rN p q = <>
    transportQOver rδ (Π A* A*₁) rM rN p q = λ rn1 rn2 rβ → transportQOver _ A*₁ _ _ (ap (λ z → coe PathOverΠ z _ _ _) p) (q _ _ rβ)
    transportQOver rδ (pathOver A* δ* M* N*) rM rN p q = <>
    transportQOver rδ (subst {A = A} A* θ'*) rM rN p q = transportQOver _ A* _ _ (ap (over-o-ap A) p) q
    transportQOver rδ (w {B = B} A* A*₁) rM rN p q = transportQOver _ A*₁ _ _ (ap
                                                                                 (λ z →
                                                                                    transport (λ x → x)
                                                                                    (changeover= B
                                                                                     (Σ=β1 (fst rδ) (fst (snd rδ)) ∘ ap (ap fst) (fst (snd (snd rδ)))))
                                                                                    (over-o-ap B z))
                                                                                 p) q
    transportQOver {δ = δ} rδ (subst1 {B = B} A*₁ M) rM rN p q = transportQOver _ A*₁ _ _ (ap (over-apd-inverse B δ (interp M)) p) q

    transportRQ Γ* bool rθ rM1 = <>
    transportRQ {M1 = P} {M2 = Q} {α = α} Γ* prop rθ rM1 =
      (λ x rx → transportPfull rM1 (! α) (!-inv-l α ∘ ∘-assoc (! α) id α)
                (path-induction
                   (λ Q' α₁ →
                      (x₁ : _) →
                      transport (λ x₂ → x₂) (! α₁) x₁ ==
                      fst
                      (transport (λ x₂ → x₂) PathOverType
                       (path-to-pathover (λ _ → Set) (! α₁)))
                      x₁)
                   (λ _ → ap≃ (! (ap fst PathOverType-id))) α x) rx) , 
      (λ x rx → transportPfull rM1 α (! (∘-unit-l α)) 
         (path-induction (λ Q₁ α₁ → (x₁ : _) → transport (λ x₂ → x₂) α₁ x₁ == IsEquiv.g (snd (transport (λ x₂ → x₂) PathOverType (path-to-pathover (λ _ → Set) (! α₁)))) x₁)
                         (λ _ → ap≃ (! (ap (λ z → IsEquiv.g (snd z)) PathOverType-id))) α x) rx)
    transportRQ Γ* (proof M) rθ rM1 = <>
    transportRQ {M1 = M1} {α = α} Γ* (Π {B = B} A* B*) rθ rM1 = 
     λ{N1}{_}{β} rn1 rn2 rβ → transportQOver _ B* _ _ (path-induction-homo
                                                         (λ N2 β₁ →
                                                            path-induction-homo''
                                                            (λ x p → PathOver B (pair= id p) (M1 N1) (M1 x)) id β₁
                                                            ∘o path-to-pathover B (! (ap (λ f → f N1) α))
                                                            ==
                                                            transport (λ x → x) PathOverΠ
                                                            (path-to-pathover (λ θ → (x : _) → B (θ , x)) (! α)) N1 N2 β₁)
                                                         (path-induction
                                                            (λ _ α₁ →
                                                               id ∘o path-to-pathover B (! (ap (λ f → f N1) α₁)) ==
                                                               transport (λ x → x) PathOverΠ
                                                               (path-to-pathover (λ θ → (x : _) → B (θ , x)) (! α₁)) N1 N1 id)
                                                            (! (PathOverΠ-id M1)) α) β)
                                                        (QOver-irrel _ _ B* _ _
                                                         (fund-∘ _ _ B* (snd rM1 _ _ rβ)
                                                          (transportRQ _ B* (rθ , rn1) (fst rM1 _ rn1))))
    transportRQ Γ* (pathOver A* δ* M* N*) rθ rM1 = <>
    transportRQ {α = α} Γ* (subst {A = A} A* θ'*) rθ rM1 = transportQOver _ A* _ _ (path-induction
                                                                                      (λ _ α₁ →
                                                                                         path-to-pathover A (! α₁) ==
                                                                                         over-o-ap A (path-to-pathover (λ θ → A (interps θ'* θ)) (! α₁)))
                                                                                      id α)
                                             (QOver-irrel _ _ A* _ _ (transportRQ _ A* _ rM1))
    transportRQ {α = α} .(Γ* , A*) (w {Γ} {A} {B} {Γ*} A* A*₁) rθ rM1 = transportQOver _ A*₁ _ _ (path-induction
                                                                                                    (λ _ α₁ →
                                                                                                       path-to-pathover B (! α₁) ==
                                                                                                       over-o-ap B (path-to-pathover (λ θ → B (fst θ)) (! α₁)))
                                                                                                    id α)
                                                                  (QOver-irrel _ _ A*₁ _ _ (transportRQ _ A*₁ _ rM1))
    transportRQ {α = α} Γ* (subst1 {B = B} B* M) rθ rM1 = 
      transportQOver _ B* _ _ (path-induction
                                 (λ _ α₁ →
                                    path-to-pathover B (! α₁) ==
                                    over-o-ap B (path-to-pathover (λ θ → B (θ , interp M θ)) (! α₁)))
                                 id α)
      (QOver-irrel _ _ B* _ _ (transportRQ _ B* _ rM1)) 

  -- ----------------------------------------------------------------------
  -- definitionally equal types give coercable R's
  -- FIXME it's no longer true that these are actually definitionally equal,
  -- because of the Q components of R_Pi---e.g. there are transportR's in different places
  -- for different definitionally equal types (see the case for unlam, e.g.).  
  -- But maybe we can still get a coercion here?

  {-
  R-deq-bool : ∀ {Γ A θ M} (Γ* : Ctx Γ) (A1* : Ty Γ* A) → (eq : A == \ _ -> Bool) -- really only need equality, not paths
                           (rθ : RC Γ* θ) → R Γ* bool rθ M → R Γ* A1* rθ (coe (! (ap≃ eq)) M)
  R-deq-bool Γ* bool eq rθ rM = {!!}
  R-deq-bool Γ* prop eq rθ rM = {!!}
  R-deq-bool Γ* (proof M₁) eq rθ rM = {!!}
  R-deq-bool {θ = θ} Γ* (Π A1* A1*₁) eq rθ rM = {!ap≃ eq {θ}!}
  R-deq-bool Γ* (subst A1* θ'*) eq rθ rM = {!!}
  R-deq-bool Γ* (pathOver A1* δ* M* N*) eq rθ rM = {!!}
  R-deq-bool .(Γ* , A1*) (w {Γ} {A} {B} {Γ*} A1* A1*₁) eq rθ rM = {!!}
  R-deq-bool Γ* (subst1 A1*₁ M₁) eq rθ rM = {!!}
  -}

  postulate
    R-deq : ∀ {Γ A θ M} (Γ* : Ctx Γ) (A* A1* : Ty Γ* A) (rθ : RC Γ* θ) → R Γ* A* rθ M → R Γ* A1* rθ M
    -- R-deq Γ* A* A1* rθ = lib.PrimTrustMe.unsafe-cast

    Q-deq : ∀ {Γ A θ1 θ2 δ M1 M2 α} 
              {Γ* : Ctx Γ} {rθ1 : RC Γ* θ1} {rθ2 : RC Γ* θ2} (rδ : QC Γ* rθ1 rθ2 δ)
              (A* A1* : Ty Γ* A) {rM1 : R Γ* A* rθ1 M1} {rM2 : R Γ* A* rθ2 M2}
            → QOver rδ A* rM1 rM2 α
            → QOver rδ A1* (R-deq _ A* A1* rθ1 rM1) (R-deq _ A* A1* rθ2 rM2) α

  QOver-irrel rδ rδ' A* rM1 rM2 rα = fund-changeover rδ rδ' A* rM1 rM2 id rα

  -- ----------------------------------------------------------------------
  -- proofs of the QOver operations and properties

{-PERF: Just some path inductions left to do here

  fund-changeover rδ rδ' bool rM1 rM2 eq rα = <>
  fund-changeover rδ rδ' prop rM1 rM2 eq rα = 
    (λ x rx → transportP rM2 _ _ _ _ (ap (λ y → fst y x) (PathOverType-changeover eq _)) (fst rα x rx)) , 
    (λ x rx → transportP rM1 _ _ _ _ (ap (λ y → IsEquiv.g (snd y) x) (PathOverType-changeover eq _)) (snd rα x rx))
  fund-changeover rδ rδ' (proof M) rM1 rM2 eq rα = <>
  fund-changeover {δ = δ} {δ' = δ'} {α = α} rδ rδ' (Π {A = A} {B = B} A* A*₁) rM1 rM2 eq rα = 
    λ {_}{_}{β} rn1 rn2 rβ → transportQOver _ A*₁ _ _ (coh eq α β )
      (fund-changeover _ _ A*₁ _ _ (path-induction (λ δ'' eq₁ → (n1 : _) (n2 : _) (β₁ : PathOver A δ'' n1 n2) → pair= δ (transport (λ x → x) (changeover= A (! eq₁)) β₁) == pair= δ'' β₁) (λ _ _ _ → id) eq _ _ β)
                                  (rα _ _ (fund-changeover rδ' rδ A* _ _ (! eq) rβ))) where
     coh : {δ : _} {δ' : _} (eq : δ == δ') {M1 : _} {M2 : _} (α : PathOver (λ θ → (x : A θ) → B (θ , x)) δ M1 M2)
           {n1 : _} {n2 : _} (β : PathOver A δ' n1 n2) → 
           Id (transport (λ x → x) (changeover= B (path-induction (λ δ'' eq₁ → (n1 : A _) (n2 : A _) (β₁ : PathOver A δ'' n1 n2) → Id (pair= δ (transport (λ x → x) (changeover= A (! eq₁)) β₁)) (pair= δ'' β₁)) (λ _ _ _ → id) eq n1 n2 β)) (transport (λ x → x) PathOverΠ α n1 n2 (transport (λ x → x) (changeover= A (! eq)) β))) (transport (λ x → x) PathOverΠ (transport (λ x → x) (changeover= (λ θ → (x : A θ) → B (θ , x)) eq) α) n1 n2 β)
     coh id α β = id
  fund-changeover rδ rδ' (pathOver A* δ* M* N*) rM1 rM2 eq rα = <>
  fund-changeover {δ' = δ'} {α = α} rδ rδ' (subst {A = A} A* θ'*) rM1 rM2 eq rα = 
    transportQOver _ A* _ _ (coh {eq = eq} α) (fund-changeover (fund-aps _ θ'* _ _ rδ) (fund-aps _ θ'* _ _ rδ')
       A* rM1 rM2 (ap (ap (interps θ'*)) eq) rα) where
          coh : ∀ {δ M1 M2} → {eq : δ == δ'} (α : PathOver (λ θ → A (interps θ'* θ)) δ M1 M2) →
            (transport (λ x → x) (changeover= A (ap (ap (interps θ'*)) eq))
             (over-o-ap A α)) ==
            (over-o-ap A
             (transport (λ x → x) (changeover= (λ θ → A (interps θ'* θ)) eq) α))
          coh {eq = id} α = id
  fund-changeover {α = α} (δ1 , α1 , δeq , rδ1 , rα1) (δ1' , α1' , δeq' , rδ1' , rα1')  (w {B = B} A* A*₁) rM1 rM2 eq rα = 
    transportQOver _ A*₁ _ _ (path-induction
                                (λ δ' eq₁ →
                                   (δ1'' : _) (α1'' : _) (δeq'' : _) →
                                   transport (λ x → x)
                                   (changeover= B
                                    (Σ=β1 δ1'' α1'' ∘
                                     ap (ap fst) (δeq'' ∘ eq₁ ∘ ! δeq) ∘ ! (Σ=β1 δ1 α1)))
                                   (transport (λ x → x) (changeover= B (Σ=β1 δ1 α1 ∘ ap (ap fst) δeq))
                                    (over-o-ap B α))
                                   ==
                                   transport (λ x → x)
                                   (changeover= B (Σ=β1 δ1'' α1'' ∘ ap (ap fst) δeq''))
                                   (over-o-ap B
                                    (transport (λ x → x) (changeover= (λ θ → B (fst θ)) eq₁) α)))
                                (λ δ1'' → {!coh!}) eq δ1' α1' δeq') 
      (fund-changeover _ _ A*₁ _ _ (Σ=β1 δ1' α1' ∘ ap (ap fst) (δeq' ∘ eq ∘ ! δeq) ∘ ! (Σ=β1 δ1 α1)) rα) 
  fund-changeover {δ = δ} {α = α} rδ rδ' (subst1 {B = A₁} A*₁ M) rM1 rM2 eq rα = 
    transportQOver _ A*₁ _ _ (path-induction (λ δ' eq₁ → Id (transport (λ x → x) (changeover= A₁ (ap (λ x → pair= x (apdo (interp M) x)) eq₁)) (over-apd-inverse A₁ δ (interp M) α)) (over-apd-inverse A₁ δ' (interp M) (transport (λ x → x) (changeover= (λ θ → A₁ (θ , interp M θ)) eq₁) α))) id eq) 
       (fund-changeover _ _ A*₁ _ _ (ap (λ x → pair= x (apdo (interp M) x)) eq) rα)

  fund-refl Γ* bool rθ1 rN = <>
  fund-refl Γ* prop rθ1 rN = (λ x rx → transportP rN _ _ _ _ (! (ap≃ (ap fst PathOverType-id))) rx) , (λ y ry → transportP rN _ _ _ _ (! (ap≃ (ap (λ x → IsEquiv.g (snd x)) PathOverType-id))) ry)
  fund-refl Γ* (proof M) rθ1 rN = <>
  fund-refl {N = N} Γ* (Π {B = C₁} C* C*₁) rθ1 rN = 
    λ {N1} {N2} {β} rN1 rN2 rβ → transportQOver _ C*₁ _ _ (path-induction-homo
                                                             (λ N3 β₁ →
                                                                path-induction-homo''
                                                                (λ x p → PathOver C₁ (pair= id p) (N N1) (N x)) id β₁
                                                                == transport (λ x → x) PathOverΠ id N1 N3 β₁)
                                                             (! (PathOverΠ-id N)) β) (snd rN rN1 rN2 rβ)
  fund-refl Γ* (pathOver C* δ* M N) rθ1 rN = <>
  fund-refl Γ* (subst C* θ'*) rθ1 rN = (fund-changeover _ _ C* _ _ id (fund-refl _ C* _ rN))
  fund-refl .(Γ* , C*) (w {Γ} {A} {B} {Γ*} C* C*₁) rθ1 rN = fund-refl _ C*₁ _ rN
  fund-refl Γ* (subst1 C*₁ M) rθ1 rN = QOver-irrel _ _ C*₁ _ _ (fund-refl _ C*₁ _ rN)

  fund-!s · rθ1 rθ2 rδ = <>
  fund-!s (Γ* , A*) rθ1 rθ2 (δ1 , α1 , eq , rδ1 , rα1)  = ! δ1 , !o α1 , (!Σ δ1 α1 ∘ ap ! eq) , fund-!s Γ* _ _ rδ1 , fund-! rδ1 A* _ _ rα1
  
  fund-! rδ bool rM1 rM2 rα = <>
  fund-! rδ prop rM1 rM2 rα = (λ x rx → transportP rM1 _ _ _ _ (ap≃ (! (ap fst PathOverType-!))) (snd rα x rx)) , 
                             (λ x rx → transportP rM2 _ _ _ _ (ap≃ (! (ap (λ x₁ → IsEquiv.g (snd x₁)) PathOverType-!))) (fst rα x rx)) -- OK
  fund-! rδ (proof M) rM1 rM2 rα = <>
  fund-! {δ = δ} rδ (Π {A = C} C* C*₁) rM1 rM2 rα = 
    λ rn1 rn2 rβ → 
       (transportQOver _ C*₁ _ _ {!coh!}
       (fund-changeover _ _ C*₁ _ _ (path-induction
                                       (λ _ δ₁ →
                                          (N1 : _) (N2 : _) (β : PathOver C (! δ₁) N1 N2) →
                                          Id
                                          (!
                                           (pair= δ₁
                                            (transport (λ x → x) (changeover= C (!-invol δ₁)) (!o β))))
                                          (pair= (! δ₁) β))
                                       (λ _ _ β → path-induction-homo (λ _ β₁ → Id (! (pair= id (!o β₁))) (pair= id β₁)) id β) δ _ _ _) 
        (fund-! _ C*₁ _ _ (rα _ _ (fund-changeover _ _ C* _ _ (!-invol δ) (fund-! _ C* _ _ rβ))))))
  fund-! rδ (pathOver C* δ* M* N*) rM1 rM2 rα = <>
  fund-! {δ = δ} rδ (subst {A = C} C* θ'*) rM1 rM2 rα = 
    transportQOver _ C* _ _ (path-induction
                               (λ _ δ₁ →
                                  (M1 : _) (M2 : _) (α : PathOver (C o interps θ'*) δ₁ M1 M2) →
                                  transport (λ x → x) (changeover= C (! (ap-! (interps θ'*) δ₁)))
                                  (!o (over-o-ap C α))
                                  == over-o-ap C (!o α))
                               (λ M1 M2 α →
                                     path-induction-homo
                                     (λ M3 α → Id (!o (over-o-ap C α)) (over-o-ap C (!o α)))
                                  id α) δ _ _ _)
    (fund-changeover _ _ C* _ _ (! (ap-! (interps θ'*) _)) 
      (fund-! _ C* rM1 rM2 rα))
  fund-! rδ (w C* C*₁) rM1 rM2 rα = transportQOver _ C*₁ _ _ {!coh!} (fund-! _ C*₁ _ _ rα)
  fund-! rδ (subst1 C*₁ M) rM1 rM2 rα = transportQOver _ C*₁ _ _ {!coh!}
                                          (fund-changeover _ _ C*₁ _ _ {!coh!} (fund-! _ C*₁ _ _ rα))

  fund-∘s · rθ1 rθ2 rθ3 rδ2 rδ1 = <>
  fund-∘s (Γ* , A*) rθ1 rθ2 rθ3 (δ21 , α21 , eq2 , rδ21 , rα21) (δ11 , α11 , eq1 , rδ11 , rα11) = 
      δ21 ∘ δ11 , α21 ∘o α11 , (∘Σ δ21 δ11 α21 α11 ∘ ap∘ eq2 eq1) , fund-∘s Γ* _ _ _ rδ21 rδ11 , fund-∘ rδ21 rδ11 A* rα21 rα11
  
  fund-∘ rδ2 rδ1 bool rα2 rα1 = <>
  fund-∘ {M1 = M1} {M3 = M3} {α2 = α2} {α1 = α1} rδ2 rδ1 prop {rM1 = rM1} {rM3 = rM3} rα2 rα1 = 
    (λ x rx → transportP rM3 _ _ _ _ (ap≃ (ap fst (PathOverType-∘ α2 α1))) (fst rα2 _ (fst rα1 x rx))) , 
    (λ x rx → transportP rM1 _ _ _ _ (ap≃ (ap (λ z → IsEquiv.g (snd z)) (PathOverType-∘ α2 α1))) (snd rα1 _ (snd rα2 x rx)))
  fund-∘ rδ2 rδ1 (proof M) rα2 rα1 = <>
  fund-∘ rδ2 rδ1 (Π A* B*) rα2 rα1 = 
    λ rn1 rn2 rβ → transportQOver _ B* _ _ {!coh!}
          (fund-changeover _ _ B* _ _ {!coh!} (fund-∘ _ _ B* (rα2 _ _ (fund-PathOver∘-transport A* rδ2 rδ1 rβ)) (rα1 _ _ (fund-transport-right _ A* _ _ rδ1 rn1))))
  fund-∘ rδ2 rδ1 (pathOver A* δ* M* N*) rα2 rα1 = <>
  fund-∘ {δ2 = δ2} {δ1 = δ1} rδ2 rδ1 (subst A* θ'*) rα2 rα1 = 
    transportQOver _ A* _ _ {!coh!}
      (fund-changeover _ _ A* _ _ (! (ap-∘ (interps θ'*) δ2 δ1)) (fund-∘ _ _ A* rα2 rα1))
  fund-∘ rδ2 rδ1 (w A* A*₁) rα2 rα1 = transportQOver _ A*₁ _ _ {!coh!} (fund-∘ _ _ A*₁ rα2 rα1)
  fund-∘ rδ2 rδ1 (subst1 A*₁ M) rα2 rα1 = transportQOver _ A*₁ _ _ {!coh!}
                                            (fund-changeover _ _ A*₁ _ _ {!coh!} (fund-∘ _ _ A*₁ rα2 rα1))
-}

  -- ----------------------------------------------------------------------
  -- transport and properties

{- PERF 
  look at ap part of transportΠ
  also a few structural properties cases left, but not too worried
  then lots of coh

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
    (λ x rx → transportR (Γ'* , A*) B* (rθ2 , rx) (ap≃ (! (transport-Πo A (λ x₁ y → B (x₁ , y)) δ f)))
                (fund-transport (Γ'* , A*) B*
                   (rθ1 , fund-transport! Γ'* A* rθ1 rθ2 rδ rx) (rθ2 , rx)
                   (δ , _ , id , rδ , fund-transport-left Γ'* A* rθ1 rθ2 rδ rx)
                   (fst rf _ (fund-transport! Γ'* A* rθ1 rθ2 rδ rx)))) , 
    (λ rn1 rn2 rα → {!FIXME!})
  fund-transport {δ = δ} {N = β} Γ* (pathOver C* {θ1* = θ1*} {θ2* = θ2*} δ'* M N) rθ1 rθ2 rδ rβ = 
    transportQOver _ C* _ _ {!coh!}
      (fund-changeover _ _ C* _ _ (apd (interpps δ'*) δ ∘ ! (transport-Path (interps θ1*) (interps θ2*) δ (interpps δ'* _)))
       (fund-∘ _ _ C* (fund-ap Γ* N rθ1 rθ2 rδ)
        (fund-∘ _ _ C* rβ (fund-! _ C* _ _ (fund-ap Γ* M rθ1 rθ2 rδ)))))
  fund-transport {δ = δ} Γ* (subst {A = A} {Γ'* = Γ'*} C* θ'*) rθ1 rθ2 rδ rN = transportR Γ'* C* (funds Γ* Γ'* rθ2 θ'*) (! (ap≃ (transport-ap-assoc' A (interps θ'*) δ))) (fund-transport Γ'* C* _ _ (fund-aps Γ* θ'* rθ1 rθ2 rδ) rN) 
  fund-transport {δ = δ} .(Γ* , A*) (w {Γ} {A} {B} {Γ*} A* B*) rθ1 rθ2 (δ' , α' , eq , rδ' , rα') rN = 
    transportR Γ* B* (fst rθ2) (ap≃ (! (transport-ap-assoc' B fst δ)) ∘ ! (ap≃ (ap (λ x → transport B x) (Σ=β1 δ' α' ∘ ap (ap fst) eq)))) 
                  (fund-transport Γ* B* _ _ rδ' rN) 
  fund-transport {δ = δ} Γ'* (subst1 {B = B} {A* = A*} C* M) rθ1 rθ2 rδ rN = 
    transportR _ C* _ (transport-apd-assoc B δ (interp M))
      (fund-transport (Γ'* , A*) C* _ _
       (δ , _ , id , rδ , fund-ap Γ'* M _ _ rδ) rN)

  fund-transport-proof {δ = δ} Γ'* M rθ1 rθ2 rδ {N = N} rN = 
    transportP (fund Γ'* prop rθ2 M) _ _ _ _ 
               (path-induction
                  (λ _ δ₁ →
                     fst (transport (λ x → x) PathOverType (apdo (interp M) δ₁)) N ==
                     transport (interp M) δ₁ N)
                  (ap≃ (ap fst PathOverType-id)) δ)
               (fst (fund-ap Γ'* M rθ1 rθ2 rδ) N rN)

  fund-transport-right Γ* bool rθ1 rθ2 rδ rM = <>
  fund-transport-right {δ = δ} {M = M} Γ* prop rθ1 rθ2 rδ rM = 
    (λ x rx → transportPfull rM (! (ap≃ (transport-constant δ))) (! (∘-unit-l (! (ap≃ (transport-constant δ))))) (path-induction
                                                                                                                    (λ _ δ₁ →
                                                                                                                       transport (λ x₁ → x₁) (! (ap≃ (transport-constant δ₁))) x ==
                                                                                                                       fst
                                                                                                                       (transport (λ x₁ → x₁) PathOverType
                                                                                                                        (PathOver-transport-right (λ _ → Set) δ₁))
                                                                                                                       x)
                                                                                                                    (ap≃ (! (ap fst PathOverType-id))) δ) rx) ,
    (λ x rx → transportPfull rM (ap≃ (transport-constant δ)) (!-inv-r (ap≃ (transport-constant δ)) ∘ ∘-assoc (ap≃ (transport-constant δ)) id (! (ap≃ (transport-constant δ)))) 
                                (coh δ x) rx) where
    coh : {θ1 : _} {θ2 : _} (δ : θ1 == θ2) (x : transport (λ _ → Set) δ M) → 
       (transport (λ x₁ → x₁) (ap (λ f → f M) (transport-constant δ)) x) ==
       (IsEquiv.g
        (snd
        (transport (λ x₁ → x₁) PathOverType
         (PathOver-transport-right (λ _ → Set) δ)))
        x) 
    coh id x = ! (ap≃ (ap (λ x₁ → IsEquiv.g (snd x₁)) PathOverType-id))
  fund-transport-right Γ* (proof M) rθ1 rθ2 rδ rM = <>
  fund-transport-right {δ = δ} Γ* (Π A* B*) rθ1 rθ2 rδ rM = 
    λ rn1 rn2 rβ → transportQOver _ B* _ _ {!coh!}
                     (fund-changeover _ _ B* _ _ {!coh!}
                      (fund-∘ _ _ B*
                       (fund-∘ _ _ B* (fund-! _ B* _ _
                                         (transportRQ _ B* (rθ2 , rn2)
                                          (fund-transport (Γ* , A*) B*
                                           (rθ1 , fund-transport! Γ* A* rθ1 rθ2 rδ rn2) (rθ2 , rn2)
                                           (_ , _ , id , rδ , fund-transport-left Γ* A* rθ1 rθ2 rδ rn2)
                                           (fst rM _ (fund-transport! Γ* A* rθ1 rθ2 rδ rn2)))))
                        (fund-transport-right _ B* _ _
                         (_ , _ , id , rδ , fund-transport-left _ A* _ _ rδ rn2)
                         (fst rM _ (fund-transport! Γ* A* rθ1 rθ2 rδ rn2))))
                       (snd rM _ _
                         (fund-changeover _ _ A* _ _ (!-inv-l δ)
                          (fund-∘ _ _ A*
                           (fund-! _ A* _ _ (fund-transport-left _ A* _ _ rδ rn2)) rβ)))))
  fund-transport-right Γ* (pathOver C* δ* M* N*) rθ1 rθ2 rδ rM = <>
  fund-transport-right {δ = δ} Γ* (subst C* θ'*) rθ1 rθ2 rδ rM = 
    transportQOver _ C* _ _ {!coh!} (fund-changeover _ _ C* _ _ (∘-unit-l (ap (interps θ'*) δ)) 
      (fund-∘ _ _ C* ((fund-! _ C* _ _ (transportRQ _ C* _
                                                                 (fund-transport _ C* (funds Γ* _ rθ1 θ'*) (funds Γ* _ rθ2 θ'*)
                                                                  (fund-aps Γ* θ'* rθ1 rθ2 rδ) rM)))) 
                     (fund-transport-right _ C* _ _ (fund-aps _ θ'* _ _ rδ) rM)))
  fund-transport-right .(Γ* , C*) (w {Γ} {A} {B} {Γ*} C* C*₁) rθ1 rθ2 rδ rM = {!FIXME!}
  fund-transport-right Γ* (subst1 C*₁ M) rθ1 rθ2 rδ rM = {!FIXME!}

  -- these can be implemented as derived forms using symmetry
  abstract
    fund-transport! Γ* A* rθ1 rθ2 rδ rM = fund-transport Γ* A* rθ2 rθ1 (fund-!s Γ* _ _ rδ) rM

    fund-transport-left  {C = C} {δ = δ} Γ* A* rθ1 rθ2 rδ rM =
      transportQOver _ A* _ _ (path-induction
                                 (λ _ δ₁ →
                                    transport (λ x → x) (changeover= C (!-invol δ₁))
                                    (!o (PathOver-transport-right C (! δ₁)))
                                    == PathOver-transport-left C δ₁)
                                 id δ)
        (fund-changeover _ _ A* _ _ (!-invol δ)
          (fund-! _ A* _ _ (fund-transport-right Γ* A* rθ2 rθ1 (fund-!s Γ* _ _ rδ) rM)))

  fund-PathOver∘-transport bool rδ2 rδ1 rα = <>
  fund-PathOver∘-transport {δ1 = δ1} prop rδ2 rδ1 {rM1 = rM1} {rM3 = rM3} rα = 
    (λ x rx → transportP rM3 _ _ _ _ (path-induction
                                        (λ θ2 δ2 → (δ3 : _) (M1 : _) (M3 : _) (α : PathOver (λ _ → Type) (δ3 ∘ δ2) M1 M3) (x₁ : _) → fst (transport (λ x₂ → x₂) PathOverType α) (transport (λ x₂ → x₂) (ap (λ f → f M1) (transport-constant δ2)) x₁) == fst (transport (λ x₂ → x₂) PathOverType (transport (λ x₂ → x₂) (PathOver∘-transport (λ _ → Set) δ2) α)) x₁)
                                        (λ _ _ _ _ _ → id) δ1 _ _ _ _ x) 
              (fst rα _ (transportPfull rM1 (ap≃ (transport-constant δ1)) (!-inv-r (ap≃ (transport-constant δ1)) ∘ ∘-assoc (ap≃ (transport-constant δ1)) id (! (ap≃ (transport-constant δ1)))) id 
                                        rx))) ,
    (λ x rx → transportPfull rM1 (! (ap≃ (transport-constant δ1))) (! (∘-unit-l (! (ap≃ (transport-constant δ1))))) 
                                 (path-induction (λ θ2 δ2 → (δ3 : _) (M1 : _) (M3 : _) (α : PathOver (λ _ → Type) (δ3 ∘ δ2) M1 M3) (x₁ : _) → transport (λ x₂ → x₂) (! (ap (λ f → f M1) (transport-constant δ2))) (IsEquiv.g (snd (transport (λ x₂ → x₂) PathOverType α)) x₁) == IsEquiv.g (snd (transport (λ x₂ → x₂) PathOverType (transport (λ x₂ → x₂) (PathOver∘-transport (λ _ → Set) δ2) α))) x₁) (λ _ _ _ _ _ → id) δ1 _ _ _ _ x) (snd rα _ rx))
  fund-PathOver∘-transport (proof M) rδ2 rδ1 rα = <>
  fund-PathOver∘-transport {Γ} {θ1} {θ2} {θ3} {δ2} {δ1} {._} {M1} {M3} {α}{Γ* = Γ*} (Π {A = A} {B = B} A* A*₁) rδ2 rδ1 {rM1 = rM1} {rM3 = rM3} rα = λ {_}{_}{β} rn1 rn2 rβ →
      transportQOver (_ , _ , id , rδ2 , rβ) A*₁ _ _ {!coh!}
      (QOver-irrel _ _ A*₁ _ _ 
      (fund-∘ _ _ A*₁ (fund-PathOver∘-transport A*₁ (_ , _ , id , rδ2 , rβ)
                         (_ , _ , id , rδ1 , fund-transport-left _ A* _ _ rδ1 rn1)
                         {rM1 =
                          fst rM1 (transport A (! δ1) _) (fund-transport! Γ* A* _ _ rδ1 rn1)}
                         {rM3 = fst rM3 _ rn2}
                         (fund-changeover _ _ A*₁ _ _ (! (∘Σ δ2 δ1 β (PathOver-transport-left A δ1)))
                            (rα _ _ (fund-∘ _ _ A* rβ (fund-transport-left _ A* _ _ rδ1 rn1)))))
         (transportRQ
          {α = ap≃ (! (transport-Πo A (λ x₁ y → B (x₁ , y)) δ1 M1))} _ A*₁ _
          (fund-transport (Γ* , A*) A*₁ _ _
           (δ1 ,
            PathOver-transport-left A δ1 ,
            id , rδ1 , fund-transport-left Γ* A* _ _ rδ1 rn1)
           (fst rM1 (transport A (! δ1) _)
            (fund-transport! Γ* A* _ _ rδ1 rn1))))))
  fund-PathOver∘-transport (pathOver A* δ* M* N*) rδ2 rδ1 rα = <>
  fund-PathOver∘-transport (subst A* θ'*) rδ2 rδ1 rα = {!FIXME!}
  fund-PathOver∘-transport (w A* A*₁) rδ2 rδ1 rα = {!FIXME!}
  fund-PathOver∘-transport (subst1 A*₁ M) rδ2 rδ1 rα = {! FIXME transportQOver _ A*₁ _ _ {!coh!} (fund-PathOver∘-transport A*₁ (_ , _ , _ , rδ2 , fund-ap _ M _ _ rδ2) (_ , _ , _ , rδ1 , fund-ap _ M _ _ rδ1) rα) !}
-}

  -- ----------------------------------------------------------------------
  -- fundamental theorem

  funds Γ* .· rθ · = <>
  funds Γ* ._ rθ (θ'* , M) = funds Γ* _ rθ θ'* , fund _ _ rθ M

  fundps Γ* · rθ θ1* θ2* δ = <>
  fundps Γ* (Γ'* , A) rθ (θ1* , M1) (θ2* , M2) (δ* , α*) = 
    _ , _ , id , fundps Γ* Γ'* rθ θ1* θ2* δ* , fund Γ* (pathOver A δ* M1 M2) rθ α*
  fundps Γ* Γ'* rθ θ1* ._ refls = fund-refls Γ'* (funds Γ* Γ'* rθ θ1*)

  fund-<> : ∀ {Γ θ} → (Γ* : Ctx Γ) (rθ : RC Γ* θ) → R Γ* (proof unit) rθ <>
  fund-<>⁺ : ∀ {Γ θ} → (Γ* : Ctx Γ) (rθ : RC Γ* θ) → R Γ* (proof unit⁺) rθ <>⁺
  fund-abort : ∀ {Γ θ C} → (Γ* : Ctx Γ) (rθ : RC Γ* θ) → Tm Γ* (proof void) → C

{- later
  fund-lam= : ∀ {Γ A B} (Γ* : Ctx Γ) (A* : Ty Γ* A) (B* : Ty (Γ* , A*) B)
              (f g : Tm Γ* (Π A* B*))
              (α : Tm (Γ* , A*) (id B* (unlam f) (unlam g)))
              {θ : Γ} (rθ : RC Γ* θ)
            → (x : _) (rx : _) → _
-}

  fund-split1 : ∀ {Γ θ} (Γ* : Ctx Γ) {C : _} (C* : Ty (Γ* , proof unit⁺) C)
          → (M1 : Tm Γ* (subst1 C* <>⁺) )
          → (M : Tm Γ* (proof unit⁺))
          → (rθ : RC Γ* θ)
          → R Γ* (subst1 C* M) rθ (interp (split1 C* M1 M) θ)

  fund-tr1-bool : ∀ {Γ C θ M1 M2 α N} (Γ* : Ctx Γ) (C* : Ty (Γ* , bool) C) (rθ : RC Γ* θ)
          (rM1 : R Γ* bool rθ M1) (rM2 : R Γ* bool rθ M2) 
          (rα : QOver (fund-refls Γ* rθ) bool rM1 rM2 α) 
          (rN : R (Γ* , bool) C* (rθ , rM1) N)
        → R (Γ* , bool) C* (rθ , rM2) (transport C (pair= id α) N)
  fund-tr1-bool {C = C} {α = α} Γ* C* rθ rM1 rM2 rα rN = 
      (fund-transport (Γ* , bool) C* (rθ , rM1) (rθ , rM2) (id , α , id , fund-refls Γ* rθ , <>) rN)

  fund-tr1-unit⁺ : ∀ {Γ C θ M1 M2 α N} (Γ* : Ctx Γ) (C* : Ty (Γ* , (proof unit⁺)) C) (rθ : RC Γ* θ)
          (rM1 : R Γ* (proof unit⁺) rθ M1) (rM2 : R Γ* (proof unit⁺) rθ M2) 
          (rα : QOver (fund-refls Γ* rθ) (proof unit⁺) rM1 rM2 α) 
          (rN : R (Γ* , (proof unit⁺)) C* (rθ , rM1) N)
        → R (Γ* , (proof unit⁺)) C* (rθ , rM2) (transport C (pair= id α)  N)
  fund-tr1-unit⁺ {C = C} {α = α} Γ* C* rθ rM1 rM2 rα rN = 
      (fund-transport (Γ* , proof unit⁺) C* (rθ , rM1) (rθ , rM2) (id , α , id , fund-refls Γ* rθ , <>) rN)

  fund .(Γ* , A*) .(w A* A*) (rθ , rM) (v {Γ} {A} {Γ*} {A*}) = rM
  fund .(Γ* , A*) .(w A* B*) (rθ , rM) (w {Γ} {A} {B} {Γ*} {A*} {B*} M) = fund Γ* B* rθ M
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
  fund Γ* .(proof unit) rθ <> = fund-<> Γ* rθ
  fund Γ* A* rθ (abort M) = fund-abort Γ* rθ M
  fund {θ = θ} .Γ* .(subst1 C* M) rθ (if {Γ} {C} {Γ*} {C*} M1 M2 M) with interp M θ | (fund Γ* bool rθ M)
  ... | i | Inl x = transportR (Γ* , bool) C* (rθ , Inl x) (path-induction
                                                              (λ i₁ x₁ →
                                                                 transport (λ x₂ → C (θ , x₂)) x₁ (interp M1 θ) ==
                                                                 if (λ x₂ → C (θ , x₂)) / i₁ then interp M1 θ else (interp M2 θ))
                                                              id (! x)) 
                               (transportR _ C* _ {!coh!}
                                  (fund-tr1-bool {_} {_} {_} {_} {_}
                                   {path-to-pathover (λ _ → Bool) (! x)} {_} Γ* C* rθ
                                   (fund Γ* bool rθ true) (Inl x) <> (fund Γ* _ rθ M1))) 
                -- see split1 for a cleaner version
  ... | i | Inr x = transportR (Γ* , bool) C* (rθ , Inr x) (path-induction
                                                              (λ i₁ x₁ →
                                                                 transport (λ x₂ → C (θ , x₂)) x₁ (interp M2 θ) ==
                                                                 if (λ x₂ → C (θ , x₂)) / i₁ then interp M1 θ else (interp M2 θ))
                                                              id (! x)) 
                               (transportR _ C* _ {!coh!}
                                  (fund-tr1-bool {_} {_} {_} {_} {_}
                                   {path-to-pathover (λ _ → Bool) (! x)} {_} Γ* C* rθ
                                   (fund Γ* bool rθ false) (Inr x) <> (fund Γ* _ rθ M2))) 

  fund .Γ* .(Π A* B*) rθ (lam {Γ} {A} {B} {Γ*} {A*} {B*} M) =
    (λ N rN → fund (Γ* , A*) B* (rθ , rN) M) , 
    (λ {N1} {N2} {α} rN1 rN2 rα → transportQOver _ B* _ _ {!coh!} (fund-ap (Γ* , A*) M (rθ , rN1) (rθ , rN2) (id , α , id , (fund-refls Γ* rθ) , rα))) 
  fund .Γ* .(subst1 B* N) rθ (app {Γ} {A} {B} {Γ*} {A*} {B*} M N) = fst (fund Γ* (Π A* B*) rθ M) _ (fund Γ* A* rθ N)
  fund _ ._ rθ (refl{A* = A*}{θ* = θ*} M*) = QOver-irrel _ _ A* _ _
                                               (fund-refl _ (subst A* θ*) _ (fund _ (subst A* θ*) _ M*))
  fund .Γ* ._ rθ (tr{Γ}{A}{C}{Γ*}{Γ'*} C* {θ1}{θ2} δ N) = fund-transport Γ'* C* (funds Γ* Γ'* rθ θ1) (funds Γ* Γ'* rθ θ2) (fundps Γ* Γ'* rθ θ1 θ2 δ) (fund Γ* _ rθ N) 

  fund {θ = θ} .Γ* ._ rθ (uap{Γ}{Γ*}{P}{Q} f* g*) = coe {!!} -- make lemma
    (Q-deq _ prop (subst prop ·) {fund _ prop rθ P} {fund _ prop rθ Q} ((λ x rx → transportP (fund Γ* prop rθ Q) _ _ _ _ {!univalenceβ!} (fund _ _ (rθ , rx) f*)) , 
     {!FIXME symmetric!}))
  fund .Γ* .A* rθ (deq{Γ}{A}{Γ*}{A1*}{A*} M) = R-deq Γ* A1* A* rθ (fund Γ* A1* rθ M) 
  fund Γ* ._ rθ <>⁺ = fund-<>⁺ Γ* rθ
  fund Γ* ._ rθ (split1 C* M1 M) = fund-split1 Γ* C* M1 M rθ 
  -- fund ._ B* rθ (unlam {Γ* = Γ*} {A* = A*} M) = fst (fund Γ* (Π A* B*) (fst rθ) M) _ (snd rθ)
  -- later fund Γ* ._ rθ (lam={A* = A*}{B* = B*} f* g* α*) = λ x rx → fund-lam= Γ*  A* B* f* g* α* rθ x rx

  fund-<> Γ* rθ = <>
  fund-<>⁺ Γ* rθ = id
  fund-abort Γ* rθ M = Sums.abort (fund Γ* (proof void) rθ M)
  -- fund-lam= Γ* A* B* f* g* α* rθ x rx = transportQ (Γ* , A*) B* (rθ , rx) (fst (fund Γ* (Π A* B*) rθ f*) x rx)
  --                                        (fst (fund Γ* (Π A* B*) rθ g*) x rx) (! (Π≃β (λ x₁ → interp α* (_ , x₁)))) 
  --                                        (fund (Γ* , A*) _ (rθ , rx) α*) 

  fund-split1 {θ = θ} Γ* {C} C* M1 M rθ = transportR _ C* _ (apd (split1⁺ (λ x → C (θ , x)) (interp M1 θ))
                                                               (! (fund Γ* (proof unit⁺) rθ M))
                                                               ∘ {!coh!})
                                            (fund-tr1-unit⁺ {α = path-to-pathover (λ _ → Unit⁺) (! (fund Γ* (proof unit⁺) rθ M))} Γ* C* rθ id (fund Γ* (proof unit⁺) rθ M) <>
                                             (fund Γ* (subst1 C* <>⁺) rθ M1))

  -- ----------------------------------------------------------------------
  -- ap 

  fund-aps Γ* · rθ1 rθ2 rδ = <>
  fund-aps Γ* (_,_ {Γ'* = Γ'*} {A* = A*} θ'* M) rθ1 rθ2 rδ = _ , _ , {!coh!} , fund-aps Γ* θ'* rθ1 rθ2 rδ , fund-ap _ M rθ1 rθ2 rδ

  fund-ap .(Γ* , A*) (v {Γ} {A} {Γ*} {A*}) rθ1 rθ2 (δ1 , α , eq , rδ1 , rα) = transportQOver _ A* _ _ {!coh!} rα 
  fund-ap .(Γ* , A*) (w {Γ} {A} {B} {Γ*} {A*} {B*} f) rθ1 rθ2 (δ1 , α , eq , rδ1 , rα) = 
    transportQOver _ B* _ _ {!coh!} (fund-ap Γ* f (fst rθ1) (fst rθ2) rδ1)
  fund-ap Γ* true rθ1 rθ2 rδ = <>
  fund-ap Γ* false rθ1 rθ2 rδ = <>
  fund-ap Γ* unit rθ1 rθ2 rδ = (λ x x₁ → <>) , (λ y x → <>) 
  fund-ap {δ = δ} Γ* unit⁺ rθ1 rθ2 rδ = (λ x eq → path-induction
                                                    (λ _ δ₁ →
                                                       fst (transport (λ x₁ → x₁) PathOverType (apdo (λ θ → Unit⁺) δ₁)) x
                                                       == <>⁺)
                                                    (eq ∘ ap≃ (ap fst PathOverType-id)) δ) ,
                                       {!FIXME symmetric!}
  fund-ap Γ* void rθ1 rθ2 rδ = (λ x x₁ → x₁) , (λ y x → x) 
  fund-ap Γ* <> rθ1 rθ2 rδ = <>
  fund-ap Γ* <>⁺ rθ1 rθ2 rδ = <>
  fund-ap Γ* (split1 C* f f₁) rθ1 rθ2 rδ = {!fund _ (proof unit⁺) rθ1 f₁ !}
  fund-ap Γ* (abort f) rθ1 rθ2 rδ = Sums.abort (fund Γ* (proof void) rθ1 f) 
  fund-ap Γ* (if f f₁ f₂) rθ1 rθ2 rδ = {!FIXME!}
  fund-ap {δ = δ} Γ* (lam {A = A} {A* = A*} {B* = B*} f) rθ1 rθ2 rδ = 
    λ rn1 rn2 rβ → transportQOver _ B* _ _ {!coh!} (fund-ap _ f (rθ1 , rn1) (rθ2 , rn2) (_ , _ , id , rδ , rβ)) 
  fund-ap Γ* (app {A* = A*} {B* = B*} f f₁) rθ1 rθ2 rδ = 
    transportQOver _ B* _ _ {!coh!} (fund-ap Γ* f _ _ rδ _ _ (fund-ap Γ* f₁ _ _ rδ))

  fund-ap {δ = δ} Γ* (tr {Γ'* = Γ'*} C* {θ1 = θ1*} {θ2 = θ2*} α* f*) rθ1 rθ2 rδ = 
    transportQOver _ C* _ _ {!coh!}
    (fund-changeover _ _ C* _ _ (coe
                                   (!
                                    (rotate3≃ (interpps α* _) (ap (interps θ1*) δ) (interpps α* _)
                                     (ap (interps θ2*) δ)))
                                   (apd (interpps α*) δ ∘
                                    ! (transport-Path (interps θ1*) (interps θ2*) δ (interpps α* _))))
        (fund-∘ _ _ C*
           (fund-transport-right _ C* _ _ (fundps Γ* Γ'* rθ2 _ _ α*) (fund Γ* (subst C* _) rθ2 f*))
         (fund-∘ _ _ C* 
           (fund-ap _ f* _ _ rδ)
           (fund-! _ C* _ _
            (fund-transport-right _ C* _ _ (fundps Γ* Γ'* rθ1 _ _ α*) (fund Γ* (subst C* _) rθ1 f*))))))
  fund-ap Γ* (refl f) rθ1 rθ2 rδ = <>
  fund-ap Γ* (uap f₂ f₃) rθ1 rθ2 rδ = <>

{- later
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
  fund-ap Γ* (lam= f f₁ f₂) rθ1 rθ2 rδ = <>
-}
  fund-ap Γ* (deq{A* = A*} {A'* = A'*} f) rθ1 rθ2 rδ = Q-deq _ A* A'* (fund-ap Γ* f rθ1 rθ2 rδ) 

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
