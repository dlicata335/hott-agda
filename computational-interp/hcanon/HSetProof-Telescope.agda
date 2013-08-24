{-# OPTIONS --type-in-type --no-termination-check #-}

open import lib.Prelude 
open BoolM 
import lib.PrimTrustMe
open import computational-interp.hcanon.HSetLang-Telescope2

module computational-interp.hcanon.HSetProof-Telescope2 where

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

  -- definition and proof of reducibility

  RC : ∀ {Γ} → (Γ* : Ctx Γ) (θ : Γ) → MetaType
  R : ∀ {Γ A} (Γ* : Ctx Γ) (A* : Ty Γ* A) → {θ : Γ} → RC Γ* θ → (A θ) → MetaType
  Q : ∀ {Γ A} (Γ* : Ctx Γ) (A* : Ty Γ* A) → {θ : Γ} → (rθ : RC Γ* θ) 
     → {M N : A θ} → R Γ* A* rθ M → R Γ* A* rθ N → (α : M == N) → MetaType
  fund : ∀ {Γ A θ} (Γ* : Ctx Γ) (A* : Ty Γ* A) (rθ : RC Γ* θ) (M : Tm Γ* A*) → R Γ* A* rθ (interp M θ)

  RC · θ = Unit
  RC (Γ* , A*) (θ , M) = Σ (λ (sθ : RC Γ* θ) → R Γ* A* sθ M)

  -- workaround scoping rules
  R-proof : ∀ {Γ} (Γ* : Ctx Γ) (φ : Tm Γ* prop) {θ : Γ} (rθ : RC Γ* θ) (pf : interp φ θ) → MetaType
  R-ex    : ∀ {Γ A B C} (Γ* : Ctx Γ) (A* : Ty Γ* A) (B* : Ty Γ* B) 
            → (C* : Ty ((Γ* , A*) , w A* B*) C) 
            → {θ : Γ} {a : A θ} {b : B θ} → (rθ : RC Γ* θ) -> (rb :  R Γ* B* rθ b) (ra : R (Γ* , B*) (w B* A*) (rθ , rb) a) → C ((θ , a) , b) 
            → MetaType

  RC-middle : {Γ : _} {Γ* : Ctx Γ} {A : _} {A* : Ty Γ* A} {M : Tm Γ* A*} → ∀ {Γ' Γ''} {Γ'* : Ctx Γ'} {Δ* : TelescopeTy (Γ* , A*) Γ'*} {Γ''* : Ctx Γ''}
            → (st : SubstTele M Δ* Γ''*) 
            → {θ : _} → RC Γ''* θ
            → RC Γ'* (semsubstmiddle M Δ* Γ''* st θ)

  R _ bool rθ M = Either (M == True) (M == False)
  R Γ* prop rθ P = Candidate P
  R Γ* (proof M) rθ pf = R-proof Γ* M rθ pf
  R Γ* (Π{Γ}{A}{B} A* B*) {θ} rθ M = (N : (A θ)) (rN : R Γ* A* rθ N) → R (Γ* , A*) B* (rθ , rN) (M N)
  R Γ* (id A* M N) rθ α = Q Γ* A* rθ (fund Γ* A* rθ M) (fund Γ* A* rθ N) α
  R ._ (w{Γ* = Γ*} A* B*) {θ , _} (rθ , _) M = 
    R Γ* B* rθ M
  R .Γ* (subst1{Γ}{A0}{B}{Γ*}{A0*} B* M0) {θ} rθ M = 
    R (Γ* , A0*) B* (rθ , fund _ A0* rθ M0) M
  R ._ (ex {Γ* = Γ*} A* B* C*) ((rθ , rb) , ra) M = R-ex Γ* A* B* C* rθ rb ra M
  R Γ''* (subst {Γ* = Γ*} {A* = A*} M Δ* B* st) rθ p = R _ B* (RC-middle st rθ) p

  RC-middle {M = M} ST-· rθ = rθ , fund _ _ rθ M
  RC-middle (ST-, Δ* Γ''* B* st) rθ = RC-middle st (fst rθ) , snd rθ

  R-ex Γ* A* B* C* rθ rb ra M = R ((Γ* , A*) , w A* B*) C* ((rθ , ra) , rb) M
  R-proof Γ* φ rθ pf = redP (fund Γ* prop rθ φ) _ id pf

  -- is this an hprop in the metalanguage?
  Q Γ* bool rθ rM rN α = Unit  -- FIXME: should we insist that it's refl?
  Q Γ* prop rθ rM rN α = ((x : _) → redP rM _ id x → redP rN _ id (coe α x)) × ((y : _) → redP rN _ id y → redP rM _ id (coe (! α) y))
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
  transportQ Γ* prop rθ rM rN p q = (λ x rx → transportP rN _ id _ _ (ap (λ z → transport (λ x₁ → x₁) z x) p) (fst q _ rx)) , 
                                   (λ y ry → transportP rM _ id _ _ (ap (λ z → transport (λ x₁ → x₁) (! z) y) p) (snd q _ ry))
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
  transportR Γ* prop rθ p rφ = cand (λ φ' q x → redP rφ φ' (q ∘ p) x) 
                                    (λ {Q1}{Q2}{α1}{α2}{p2}{p2} propo path elt rp1 → 
                                       transportPfull rφ propo (propo ∘ α1 ∘ p ≃〈 ap (λ x → x ∘ p) path ∘ ∘-assoc propo α1 p 〉 (α2 ∘ p ∎)) 
                                                      elt rp1)
  transportR Γ* (proof M) rθ p rM = transportP (fund Γ* prop rθ M) _ id _ _ p rM 
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
          (rα : Q Γ* A* rθ rM1 rM2 α) 
          (rN : R (Γ* , A*) C* (rθ , rM1) N)
        → R (Γ* , A*) C* (rθ , rM2) (transport (\ x → C (θ , x)) α N)

  RC-++-fst : {Γ : _} {Γ* : Ctx Γ} {A : _} {A* : Ty Γ* A} {M : Tm Γ* A*} → ∀ {Γ' Γ''} {Γ'* : Ctx Γ'} {Δ* : TelescopeTy (Γ* , A*) Γ'*} {Γ''* : Ctx Γ''}
            → (st : SubstTele M Δ* Γ''*) → {θ'' : _} → RC Γ''* θ'' → Σ \ θ → RC Γ* θ
  RC-++-fst ST-· rθ'' = _ , rθ''
  RC-++-fst (ST-, Δ* Γ''* B* st) rθ'' = _ , snd (RC-++-fst st (fst rθ''))

  RC-tr : ∀ {Γ A Γ' Γ1 Γ2} (Γ* : Ctx Γ) {Γ'* : Ctx Γ'} {Γ1* : Ctx Γ1} {Γ2* : Ctx Γ2} {A* : Ty Γ* A} {M1 M2 : Tm Γ* A*} 
          (Δ* : TelescopeTy (Γ* , A*) Γ'*) 
          (s1 : SubstTele M1 Δ* Γ1*) (s2 : SubstTele M2 Δ* Γ2*)
          {θ1 : _} (rθ1 : RC Γ1* θ1) 
          {α : _} (rα : Q Γ* A* (snd (RC-++-fst s1 rθ1)) (fund Γ* A* _ M1) (fund Γ* A* _ M2) α) 
        → Σ \ θ2 → RC Γ2* θ2 

  RC-tr-back : ∀ {Γ A Γ' Γ1 Γ2} (Γ* : Ctx Γ) {Γ'* : Ctx Γ'} {Γ1* : Ctx Γ1} {Γ2* : Ctx Γ2} {A* : Ty Γ* A} {M1 M2 : Tm Γ* A*} 
          (Δ* : TelescopeTy (Γ* , A*) Γ'*) 
          (s1 : SubstTele M1 Δ* Γ1*) (s2 : SubstTele M2 Δ* Γ2*)
          {θ2 : _} (rθ2 : RC Γ2* θ2) 
          {α : _} (rα : Q Γ* A* (snd (RC-++-fst s2 rθ2)) (fund Γ* A* _ M1) (fund Γ* A* _ M2) α) 
        → Σ \ θ1 → RC Γ1* θ1

  sempathmiddle : ∀ {Γ A Γ' Γ1 Γ2} {Γ* : Ctx Γ} {Γ'* : Ctx Γ'} {Γ1* : Ctx Γ1} {Γ2* : Ctx Γ2} {A* : Ty Γ* A} {M1 M2 : Tm Γ* A*} 
          {Δ* : TelescopeTy (Γ* , A*) Γ'*}
          (s1 : SubstTele M1 Δ* Γ1*) (s2 : SubstTele M2 Δ* Γ2*)
          {θ : _} (rθ : RC Γ1* θ) 
          {α : _} (rα : Q Γ* A* (snd (RC-++-fst s1 rθ)) (fund Γ* A* _ M1) (fund Γ* A* _ M2) α) 
          →    (semsubstmiddle M1 Δ* Γ1* s1 θ)
            == (semsubstmiddle M2 Δ* Γ2* s2 (fst (RC-tr Γ* Δ* s1 s2 rθ rα)))

  sempathmiddle-back : ∀ {Γ A Γ' Γ1 Γ2} {Γ* : Ctx Γ} {Γ'* : Ctx Γ'} {Γ1* : Ctx Γ1} {Γ2* : Ctx Γ2} {A* : Ty Γ* A} {M1 M2 : Tm Γ* A*} 
          {Δ* : TelescopeTy (Γ* , A*) Γ'*}
          (s1 : SubstTele M1 Δ* Γ1*) (s2 : SubstTele M2 Δ* Γ2*)
          {θ2 : _} (rθ2 : RC Γ2* θ2) 
          {α : _} (rα : Q Γ* A* (snd (RC-++-fst s2 rθ2)) (fund Γ* A* _ M1) (fund Γ* A* _ M2) α) 
          →    (semsubstmiddle M2 Δ* Γ2* s2 θ2)
            == (semsubstmiddle M1 Δ* Γ1* s1 (fst (RC-tr-back Γ* Δ* s1 s2 rθ2 rα)))

  fund-tr' : ∀ {Γ A Γ' Γ1 Γ2} {Γ* : Ctx Γ} {Γ'* : Ctx Γ'} {Γ1* : Ctx Γ1} {Γ2* : Ctx Γ2} {A* : Ty Γ* A} {M1 M2 : Tm Γ* A*} 
          (Δ* : TelescopeTy (Γ* , A*) Γ'*) 
          (s1 : SubstTele M1 Δ* Γ1*) (s2 : SubstTele M2 Δ* Γ2*)
          {C : _} (C* : Ty Γ'* C) 
          {θ : _} (rθ : RC Γ1* θ) 
          {α : _} (rα : Q Γ* A* (snd (RC-++-fst s1 rθ)) (fund Γ* A* _ M1) (fund Γ* A* _ M2) α) 
          {N : _} (rN : R Γ'* C* (RC-middle s1 rθ) N)
        → R Γ'* C* (RC-middle s2 (snd (RC-tr _ _ s1 s2 rθ rα))) (transport C (sempathmiddle s1 s2 rθ rα) N)

  fund-tr- : ∀ {Γ A Γ' Γ1 Γ2} {Γ* : Ctx Γ} {Γ'* : Ctx Γ'} {Γ1* : Ctx Γ1} {Γ2* : Ctx Γ2} {A* : Ty Γ* A} {M1 M2 : Tm Γ* A*} 
          (Δ* : TelescopeTy (Γ* , A*) Γ'*) 
          (s1 : SubstTele M1 Δ* Γ1*) (s2 : SubstTele M2 Δ* Γ2*)
          {C : _} (C* : Ty Γ'* C) 
          {θ2 : _} (rθ2 : RC Γ2* θ2) 
          {α : _} (rα : Q Γ* A* (snd (RC-++-fst s2 rθ2)) (fund Γ* A* _ M1) (fund Γ* A* _ M2) α) 
          {N : _} (rN : R Γ'* C* (RC-middle s1 (snd (RC-tr-back _ _ s1 s2 rθ2 rα))) N)
        → R Γ'* C* (RC-middle s2 rθ2) (transport C {!! (sempathmiddle-back s1 s2 rθ2 rα)!} N)
  fund-tr- = {!!}

  fund-tr-back' : ∀ {Γ A Γ' Γ1 Γ2} {Γ* : Ctx Γ} {Γ'* : Ctx Γ'} {Γ1* : Ctx Γ1} {Γ2* : Ctx Γ2} {A* : Ty Γ* A} {M1 M2 : Tm Γ* A*} 
          (Δ* : TelescopeTy (Γ* , A*) Γ'*) 
          (s1 : SubstTele M1 Δ* Γ1*) (s2 : SubstTele M2 Δ* Γ2*)
          {C : _} (C* : Ty Γ'* C) 
          {θ : _} (rθ : RC Γ2* θ) 
          {α : _} (rα : Q Γ* A* (snd (RC-++-fst s2 rθ)) (fund Γ* A* _ M1) (fund Γ* A* _ M2) α) 
          {N : _} (rN : R Γ'* C* (RC-middle s2 rθ) N)
        → R Γ'* C* (RC-middle s1 (snd (RC-tr-back _ _ s1 s2 rθ rα))) (transport C (sempathmiddle-back s1 s2 rθ rα) N)
  fund-tr-back' = {!!}

  RC-tr ._ .· ST-· ST-· rθ1 rα = _ , rθ1
  RC-tr Γ* .(Δ* , B*) (ST-, Δ* Γ''* B* s1) (ST-, .Δ* Γ''*₁ .B* s2) rθ1 rα = _ , (snd (RC-tr Γ* Δ* s1 s2 (fst rθ1) rα) , fund-tr' _ s1 s2 B* (fst rθ1) rα (snd rθ1)) 

  RC-tr-back ._ .· ST-· ST-· rθ1 rα = _ , rθ1
  RC-tr-back Γ* .(Δ* , B*) (ST-, Δ* Γ''* B* s1) (ST-, .Δ* Γ''*₁ .B* s2) rθ1 rα = _ , (snd (RC-tr-back Γ* Δ* s1 s2 (fst rθ1) rα) , fund-tr-back' _ s1 s2 B* (fst rθ1) rα (snd rθ1)) 

  sempathmiddle ST-· ST-· rθ {α} rα = pair≃ id α
  sempathmiddle (ST-, Δ* Γ''* B* s1) (ST-, .Δ* Γ''*₁ .B* s2) rθ rα = pair≃ (sempathmiddle s1 s2 (fst rθ) rα) id

  sempathmiddle-back ST-· ST-· rθ {α} rα = pair≃ id (! α)
  sempathmiddle-back (ST-, Δ* Γ''* B* s1) (ST-, .Δ* Γ''*₁ .B* s2) rθ rα = pair≃ (sempathmiddle-back s1 s2 (fst rθ) rα) id

  fund-tr' Δ* s1 s2 bool rθ rα rN = {!!}
  fund-tr' Δ* s1 s2 prop rθ rα rN = {!!}
  fund-tr' Δ* s1 s2 (proof M) rθ rα rN = {!!}
  fund-tr' Δ* s1 s2 (Π A* B*) rθ rα rN = λ x rx → coe {!!}
                                                    (fund-tr- (Δ* , A*) (ST-, _ _ _ s1) (ST-, _ _ _ s2) B* (snd (RC-tr _ Δ* s1 s2 rθ rα) , _) {!!}
                                                     (rN _ (fund-tr-back' Δ* s1 s2 A* {!!} rα rx)))
  fund-tr' Δ* s1 s2 (id C* M N) rθ rα rN = {!!}
  fund-tr' Δ* s1 s2 (w C* C*₁) rθ rα rN = {!!}
  fund-tr' Δ* s1 s2 (subst M Δ*₁ C*₁ st) rθ rα rN = {!!}
  fund-tr' Δ* s1 s2 (subst1 C*₁ M) rθ rα rN = {!!}
  fund-tr' Δ* s1 s2 (ex C* C*₁ C*₂) rθ rα rN = {!!}

  fund .(Γ* , A*) .(w A* A*) (rθ , rM) (v {Γ} {A} {Γ*} {A*}) = rM
  fund .(Γ* , A*) .(w A* B*) (rθ , rM) (w {Γ} {A} {B} {Γ*} {A*} {B*} M) = fund Γ* B* rθ M
  fund Γ* .bool rθ true = Inl id
  fund Γ* .bool rθ false = Inr id
  fund Γ* .prop rθ unit = cand (λ _ _ _ → Unit) (λ propo path elt x → <>) 
  fund Γ* .prop rθ unit⁺ = cand (λ ψ p x → coe (! p) x == <>⁺) {!!} -- (λ {_}{_}{α1} propo path elt x → ({!!} ∘ ap (coe (! (propo ∘ α1))) elt) ∘ ! (ap (λ x₁ → coe (! x₁) _) path)) -- (λ φ' α p1 p2 α₁ r1 → r1 ∘ ap (λ z → coe (! α) z) (! α₁)) 
  fund Γ* .prop rθ void = cand (λ _ _ _ → Void) (λ propo path elt x → x) -- (λ φ' α p1 p2 x x₁ → x₁) 
  fund {θ = θ} Γ* .prop rθ (`∀ φ ψ) = 
    cand (λ φ' p x → (y : interp φ θ) → (ry : redP (fund Γ* prop rθ φ) _ id y) → redP (fund (Γ* , proof φ) prop (rθ , ry) ψ) _ id (coe (! p) x y)) 
         {!!} 
--         (λ φ' α p1 p2 q w y ry → transportP (fund (Γ* , proof φ) prop (rθ , ry) ψ) (interp ψ (θ , y)) id (coe (! α) p1 y) (coe (! α) p2 y) (ap (λ z → coe (! α) z y) q) (w y ry))
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
       (λ x rx → transportP (fund Γ* prop rθ Q) _ id (interp f* (θ , x)) (coe (interp (uap{P = P}{Q = Q} f* g*) θ) x) 
                     (! (ap≃ (type≃β (interp-uap-eqv{P = P}{Q = Q} f* g* θ))))
                     (fund (Γ* , proof P) (w (proof P) (proof Q)) (rθ , rx) f*)) , 
       (λ x rx → transportP (fund Γ* prop rθ P) _ id (interp g* (θ , x)) (coe (! (interp (uap{P = P}{Q = Q} f* g*) θ)) x) 
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
  fund-refl Γ''* (subst Δ* B* M st) rθ rM = {!!}

  fund-sym : ∀ {Γ A θ M N α} (Γ* : Ctx Γ) (A* : Ty Γ* A) (rθ : RC Γ* θ)
               (rM : R Γ* A* rθ M) (rN : R Γ* A* rθ N)
           → Q Γ* A* rθ rM rN α
           → Q Γ* A* rθ rN rM (! α)
  fund-sym Γ* bool rθ rM rN rα = <>
  fund-sym {α = α} Γ* prop rθ rM rN rα = snd rα , (λ x rx → transportP rN _ id _ _ (ap (λ z → coe z x) (! (!-invol α))) (fst rα x rx))
  fund-sym Γ* (proof M) rθ rM rN rα = <>
  fund-sym {α = α} Γ* (Π A* B*) rθ rM rN rα = λ x rx → transportQ (Γ* , A*) B* (rθ , rx) _ _ (! (ap-! (λ f → f x) α))
                                               (fund-sym (Γ* , A*) B* (rθ , rx) (rM x rx) (rN x rx) (rα x rx))
  fund-sym Γ* (id A* M N) rθ rM rN rα = <>
  fund-sym ._ (w {Γ* = Γ*} A* B*) rθ rM rN rα = fund-sym Γ* B* (fst rθ) rM rN rα
  fund-sym Γ* (subst1{_}{_}{_}{._}{A*} B* M) rθ rM rN rα = fund-sym (Γ* , A*) B* (rθ , _) rM rN rα
  fund-sym ._ (ex _ _ C*) rθ rM rN rα = fund-sym _ C* _ rM rN rα
  fund-sym Γ''* (subst Δ* B* M st) rθ rM rN rα = {!!}

  fund-trans : ∀ {Γ A θ M N O α β} (Γ* : Ctx Γ) (A* : Ty Γ* A) (rθ : RC Γ* θ)
               (rM : R Γ* A* rθ M) (rN : R Γ* A* rθ N) (rO : R Γ* A* rθ O) 
             → Q Γ* A* rθ rM rN α
             → Q Γ* A* rθ rN rO β
             → Q Γ* A* rθ rM rO (β ∘ α)
  fund-trans Γ* bool rθ rM rN rO qMN qNO = <>
  fund-trans {α = α} {β = β} Γ* prop rθ rM rN rO qMN qNO = 
    (λ x rx → transportP rO _ id _ _ (! (ap≃ (transport-∘ (λ x₁ → x₁) β α))) (fst qNO _ (fst qMN x rx))) , 
    (λ y ry → transportP rM _ id _ _ (ap (λ z → coe z y) (! (!-∘ β α)) ∘ ! (ap≃ (transport-∘ (λ x₁ → x₁) (! α) (! β)))) (snd qMN _ (snd qNO y ry)))
  fund-trans Γ* (proof M) rθ rM rN rO qMN qNO = <>
  fund-trans {α = α} {β = β} Γ* (Π A* B*) rθ rM rN rO qMN qNO = λ x rx → transportQ (Γ* , A*) B* (rθ , rx) _ _ (! (ap-∘ (λ f → f x) β α))
                                                           (fund-trans (Γ* , A*) B* (rθ , rx) (rM x rx) (rN x rx) (rO x rx)
                                                            (qMN x rx) (qNO x rx))
  fund-trans Γ* (id A* M N) rθ rM rN rO qMN qNO = <>
  fund-trans ._ (w {Γ* = Γ*} A*  B*) rθ rM rN rO qMN qNO = fund-trans Γ* B* (fst rθ) rM rN rO qMN qNO
  fund-trans Γ* (subst1{_}{_}{_}{._}{A*} B* M) rθ rM rN rO qMN qNO = fund-trans (Γ* , A*) B* (rθ , _) rM rN rO qMN qNO
  fund-trans ._ (ex _ _ C*) rθ rM rN rO qMN qNO = fund-trans _ C* _ rM rN rO qMN qNO
  fund-trans Γ''* (subst Δ* B* M st) rθ rM rN rO qMN qNO = {!!}

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
  transportRQ {M1 = P} {M2 = Q} {α = α} Γ* prop rθ rP = (λ q rq → transportPfull rP (! α) (!-inv-l α ∘ ∘-assoc (! α) id α) id rq) , (λ p rp → transportPfull rP α (! (∘-unit-l α)) (ap (λ x → coe x p) (! (!-invol α))) rp)
  transportRQ Γ* (proof M) rθ rM1 = <>
  transportRQ {α = α} Γ* (Π A* A*₁) rθ rM1 = λ x rx → transportQ (Γ* , A*) A*₁ (rθ , rx) _ _ (! (ap-! (λ f → f x) α))
                                                        (transportRQ {α = ap (λ f → f x) α} (Γ* , A*) A*₁ (rθ , rx)
                                                         (rM1 x rx))
  transportRQ Γ* (id A* M N) rθ rM1 = <>
  transportRQ .(Γ* , A*) (w {Γ} {A} {B} {Γ*} A* A*₁) rθ rM1 = transportRQ Γ* A*₁ (fst rθ) rM1
  transportRQ Γ* (subst1 {A* = A*} B* M) rθ rM1 = transportRQ (Γ* , A*) B* (rθ , fund Γ* A* rθ M) rM1
  transportRQ ._ (ex {Γ} {A} {B} {C} {Γ*} A* B* C*) ((rθ , rb) , ra) rM1 = transportRQ ((Γ* , A*) , w A* B*) C* ((rθ , ra) , rb) rM1
  transportRQ _ _ _ _ = {!!}

  fund-aptransport : ∀ {Γ A C θ M1 M2 α N1 N2 β} (Γ* : Ctx Γ) {A* : Ty Γ* A} (C* : Ty (Γ* , A*) C) (rθ : RC Γ* θ)
          (rM1 : R Γ* A* rθ M1) (rM2 : R Γ* A* rθ M2) 
          (rα : Q Γ* A* rθ rM1 rM2 α) 
          (rN1 : R (Γ* , A*) C* (rθ , rM1) N1) (rN2 : R (Γ* , A*) C* (rθ , rM1) N2)
          (rβ : Q (Γ* , A*) C* (rθ , rM1) rN1 rN2 β)
        → Q (Γ* , A*) C* (rθ , rM2) (fund-tr Γ* C* rθ rM1 rM2 rα rN1) (fund-tr Γ* C* rθ rM1 rM2 rα rN2) (ap (transport (λ x → C (θ , x)) α) β)
  fund-aptransport = {!!}
{-
  fund-aptransport Γ* bool rθ rM1 rM2 rα rN1 rN2 rβ = <>
  fund-aptransport {Γ}{A}{._}{θ}{M1}{M2}{α}{N1}{N2}{β} Γ* prop rθ rM1 rM2 rα rN1 rN2 rβ = 
                   (λ x rx → transportPfull rN2 (! (ap≃ (transport-constant α))) (! (∘-unit-l (! (ap (λ f → f N2) (transport-constant α))))) {!OK!}
                               (fst rβ (coe (ap≃ (transport-constant α)) x) (transportPfull rN1 (ap≃ (transport-constant α)) {!OK!} id rx))) , 
                   {!!}
  fund-aptransport Γ* (proof M) rθ rM1 rM2 rα rN1 rN2 rβ = <>
  fund-aptransport Γ* (Π C* C*₁) rθ rM1 rM2 rα rN1 rN2 rβ = {!!}
  fund-aptransport Γ* (id C* M N) rθ rM1 rM2 rα rN1 rN2 rβ = <>
  fund-aptransport Γ* {A*} (w .A* C*) rθ rM1 rM2 rα rN1 rN2 rβ = {!!}
  fund-aptransport Γ* (subst1 C*₁ M) rθ rM1 rM2 rα rN1 rN2 rβ = {!!}
  fund-aptransport .(Γ* , C*₁) (ex {Γ} {A} {B} {C} {Γ*} C* C*₁ C*₂) rθ rM1 rM2 rα rN1 rN2 rβ = {!!}
-}

{-
  -- FIXME: why doesn't this work in --without-K? 
  fund-tr {α = α} Γ* bool rθ rM1 rM2 rα (Inl x) = Inl (x ∘ ap≃ (transport-constant α))
  fund-tr {α = α} Γ* bool rθ rM1 rM2 rα (Inr x) = Inr (x ∘ ap≃ (transport-constant α))
  fund-tr {α = α} Γ* prop rθ rM1 rM2 rα rN = cand (λ φ' p x' → redP rN φ' (p ∘ ! (ap≃ (transport-constant α))) x') 
                                                  {!!} --  (λ φ' p x1' x2' eq rx1 → transportP rN φ' _ x1' x2' eq rx1) 
  fund-tr {α = α} Γ* (proof M) rθ rM1 rM2 rα rN = transportP (fund (Γ* , _) prop (rθ , rM2) M) _ id _ _ (! (ap≃ (transport-ap-assoc (λ x → interp M (_ , x)) α))) 
                                                            (fst ap-is-reducible _ rN) where
          -- FIXME: abstract out what happens at function type!
          ap-is-reducible : Q Γ* prop rθ (fund (Γ* , _) prop (rθ , rM1) M) (fund (Γ* , _) prop (rθ , rM2) M) (ap (\ x -> interp M (_ , x)) α)
          ap-is-reducible with fund-ap Γ* M rθ rM1 rM2 rα
          ... | (left , right) = (λ x rx → transportPfull (fund (Γ* , _) prop (rθ , rM2) M) id id {!!} 
                                           (left (coe (! (ap≃ (transport-constant α))) x) 
                                                 {!!})) -- (transportPfull (fund (Γ* , _) prop (rθ , rM1) M) (! (ap≃ (transport-constant α))) (! (∘-unit-l (! (ap≃ (transport-constant α))))) id rx))) 
                                , {!!} 
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
          aprβ = fund-aptransport Γ* C* rθ rM1 rM2 rα (fund (Γ* , A*) C* (rθ , rM1) M) (fund (Γ* , A*) C* (rθ , rM1) N) rβ
--  fund-tr Γ* (subst Γ'* θ'* A₂) rθ rM1 rM2 rα M = {!!}
  fund-tr {α = α} Γ* {A*} (w .A* B*) rθ rM1 rM2 rα rN = transportR Γ* B* rθ (! (ap≃ (transport-constant α))) rN
  fund-tr Γ* (subst1 A₃ M) rθ rM1 rM2 rα M₁ = {!!}
  fund-tr ._ (ex _ _ _) rθ rM1 rM2 rα M₁ = {!!}
  fund-tr ._ (subst Δ* B M) rθ rM1 rM2 rα M₁ = ?
-}
  fund-tr Γ* C* rM1 rM2 rα rN = {!C*!}

  fund-ap = {!!}
{-
  fund-ap {α = α} Γ* {A* = A*} v rθ rM1 rM2 rα = transportQ Γ* A* rθ _ _ (coh α)
                                                   (fund-trans Γ* A* rθ _ _ _
                                                    (transportRQ {α = ! (ap≃ (transport-constant α))} Γ* A* rθ rM1) rα) where
    coh : ∀ {A} {M1 M2 : A} (α : M1 == M2)→ (α ∘ !( ! (ap (λ f → f M1) (transport-constant α)))) == (apd (λ x → x) α)
    coh id = id
  fund-ap Γ* (w f) rθ rM1 rM2 rα = {!fund-ap _ f !}
  fund-ap Γ* true rθ rM1 rM2 rα = <>
  fund-ap Γ* false rθ rM1 rM2 rα = <>
  fund-ap Γ* unit rθ rM1 rM2 rα = (λ x x₁ → <>) , (λ y x → <>)
  fund-ap {α = α} Γ* unit⁺ rθ rM1 rM2 rα = (λ x x₁ → coh α x₁) , {!!} where
    coh : {M1 M2 : _} (α : M1 == M2)  {x : transport (λ x₂ → Set) α Unit⁺} 
          (x₁ : Path (transport (λ x₂ → x₂) (! (id ∘ ! (ap (λ f → f Unit⁺) (transport-constant α)))) x) <>⁺)
        → Path (transport (λ x₂ → x₂) (apd (λ x₂ → Unit⁺) α) x) <>⁺
    coh id x₁ = x₁
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