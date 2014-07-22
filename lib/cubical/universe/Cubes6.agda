{-# OPTIONS --type-in-type --without-K  #-}

open import lib.BasicTypes 
open import lib.cubical.PathOver

module lib.cubical.Cubes6 where


  module Sigmas where

    -- FIXME use a universe to avoid large indexing

--  data Ctx : Type 
    data Ty : Type → Type 
    data Tm : (Γ : Type) → (Γ → Type) → Type 
    data Ctx : Type 
    data Subst : (Γ : Type) → Type → Type 
    interpc : Ctx → Type
    interpTy : ∀ {Γ} → Ty Γ → Γ → Type
    interpSubst : ∀ {Γ Δ} → Subst Γ Δ → (x : Γ) → Δ 
    interpTm : ∀ {Γ} {A : Γ → Type} → Tm Γ A → (x : Γ) → A x

    CtxPath : {Γ : Type} {Γ' : Ctx} → (θ1 θ2 : Subst Γ (interpc Γ')) → Ty Γ
    CtxPath' : (Γ' : Ctx) → Ty (interpc Γ' × interpc Γ')
    TmPath : {Γ : Type} (Γ' : Ctx) (A : Ty (interpc Γ')) → (θ1 θ2 : Subst Γ (interpc Γ'))
         → Tm Γ (interpTy (CtxPath θ1 θ2))
         → (M1 : Tm Γ (interpTy A o interpSubst θ1))
            (M2 : Tm Γ (interpTy A o interpSubst θ2))
         → Ty Γ
    TmPath' : {Γ : Type} (Γ' : Ctx) (A : Ty (interpc Γ')) → (θ1 θ2 : Subst Γ (interpc Γ'))
         → Tm Γ (interpTy (CtxPath θ1 θ2))
         → Ty (Σ (\ (θ : Γ) → (interpTy A (interpSubst θ1 θ)) × (interpTy A (interpSubst θ2 θ))))

    TmPath'' : (Γ : Ctx) (A : Ty (interpc Γ)) 
         → Ty (Σ (\ (x : (Σ \ (θ12 : (interpc Γ) × (interpc Γ)) → (interpTy (CtxPath' Γ) θ12))) → 
              (interpTy A (fst (fst x)) × (interpTy A (snd (fst x))))))

    data Ctx where
      · : Ctx
      _,_ : (Γ : Ctx) (A : Ty (interpc Γ)) → Ctx
      _,nd_ : Ctx → Ctx → Ctx

    interpc · = Unit
    interpc (Γ , A) = Σ (λ (x : interpc Γ) → interpTy A x)
    interpc (Γ ,nd Γ') = interpc Γ × interpc Γ'

    data Subst  where
      · : ∀ {Γ} → Subst Γ (interpc ·)
      _,_ : ∀ {Γ Γ' A} → (θ : Subst Γ Γ') → Tm Γ (A o interpSubst θ) → Subst Γ (Σ A)
      p : ∀ {Γ} {A : Γ → Type} → Subst (Σ A) Γ
      idsubst : ∀ {Γ} → Subst Γ Γ
      _osubst_ : ∀ {Γ1 Γ2 Γ3} → Subst Γ2 Γ3 → Subst Γ1 Γ2 → Subst Γ1 Γ3
      _,subst_ : ∀ {Γ Γ1' Γ2'} → Subst Γ Γ1' → Subst Γ Γ2' → Subst Γ (Γ1' × Γ2')
      q : ∀ {Γ1 Γ2} → Subst (Γ1 × Γ2) Γ2

    _×subst_ : ∀ {Γ1 Γ1' Γ2 Γ2'} → Subst Γ1 Γ1' → Subst Γ2 Γ2' → Subst (Γ1 × Γ2) (Γ1' × Γ2')
    θ1 ×subst θ2 = (θ1 osubst p) ,subst (θ2 osubst q)
  
    data Ty where
      1t : ∀ {Γ} → Ty Γ
      _×t_ : ∀ {Γ} → Ty Γ → Ty Γ → Ty Γ
      Σt : ∀ {Γ} → (A : Ty Γ) → (B : Ty (Σ (interpTy A))) → Ty Γ
      substTy : ∀ {Γ} → (Γ' : Ctx) → Ty (interpc Γ') → (θ : Subst Γ (interpc Γ')) → Ty Γ 
      substTy1 : ∀ {Γ} → (A : Ty Γ) → Ty (Σ (interpTy A)) → (M : Tm Γ (interpTy A)) → Ty Γ 
      substTy1' : ∀ {Γ Γr A} → (B : Ty Γ) 
                → Ty (Σ (interpTy B))
                → (M : Tm (Σ A) (interpTy B o fst))
                → Γr == (Σ A) 
                → Ty Γr
--      weakenTy1 : ∀ {Γ} → (A : Ty Γ) → Ty Γ → Ty (Σ (interpTy A))

    data Tm where
      i0 : ∀ {Γ} {A : Γ → Type} → Tm (Σ A) (A o fst)
      iS : ∀ {Γ A B} → Tm Γ B → Tm (Σ A) (B o fst) 
      · : ∀ {Γ} → Tm Γ (\ _ -> Unit)
      _,d_ : ∀ {Γ} → {Δ : Γ → Type} 
          {Δ' : Σ Δ → Type} 
        → (θ : Tm Γ Δ) → Tm Γ (λ θ₁ → Δ' (θ₁ , interpTm θ θ₁))  → Tm Γ (λ θ₁ → Σ \ (x : Δ θ₁) → (Δ' (θ₁ , x)))
      fstd : ∀ {Γ} → {Δ : Γ → Type} 
             {Δ' : Σ Δ → Type} 
           → (θ1 : Tm Γ (\ θ → Σ \ x → Δ' (θ , x)))
           → Tm Γ Δ
      sndd : ∀ {Γ} → {Δ : Γ → Type} 
             {Δ' : Σ Δ → Type} 
           → (θ1 : Tm Γ (\ θ → Σ \ x → Δ' (θ , x)))
           → Tm Γ (\ θ → Δ' (θ , fst (interpTm θ1 θ))) 
      sndnd : ∀ {Γ} → {Δ : Γ → Type} 
            {Δ' : Γ → Type} 
            → (θ1 : Tm Γ (\ θ → Δ θ × Δ' θ ))
            → Tm Γ (\ θ → Δ' θ)
      _,nd_ : ∀ {Γ} → {Δ : Γ → Type} 
              {Δ' : Γ → Type} 
            → (θ : Tm Γ Δ) → Tm Γ Δ'  → Tm Γ (λ θ₁ → Δ θ₁ × Δ' θ₁)
      substtm : ∀ {Γ Γ' A} → Tm (interpc Γ') A → (θ : Subst Γ (interpc Γ')) → Tm Γ (A o interpSubst θ)

    interpTy 1t x = Unit
    interpTy (Σt Δ Δ') θ = Σ (λ (x : interpTy Δ θ) → interpTy Δ' (θ , x)) 
    interpTy (Δ ×t Δ') θ = interpTy Δ θ × interpTy Δ' θ
    interpTy (substTy _ A θ) θ' = interpTy A (interpSubst θ θ')
    interpTy (substTy1 A0 A M) θ' = interpTy A (θ' , interpTm M θ') 
    interpTy (substTy1' B C M id) θ' = interpTy C (fst θ' , interpTm M θ')
--    interpTy (weakenTy1 A0 A) θ' = interpTy A (fst θ')

    interpTm i0 θ = snd θ
    interpTm (iS M) θ = interpTm M (fst θ)
    interpTm · θ' = <>
    interpTm (θ ,d x) θ' = interpTm θ θ' , interpTm x θ'
    interpTm (fstd x) θ' = fst (interpTm x θ')
    interpTm (sndd x) θ' = snd (interpTm x θ')
    interpTm (substtm M θ) θ' = interpTm M (interpSubst θ θ')
    interpTm (M1 ,nd M2) θ' = interpTm M1 θ' , interpTm M2 θ'
    interpTm (sndnd M) θ' = snd (interpTm M θ')

    CtxPath' · = 1t
    CtxPath' (Γ' , A) = Σt (substTy (Γ' ,nd Γ') (CtxPath' Γ') (p ×subst p))
                           {!!}
    CtxPath' (Γ1 ,nd Γ2) = substTy (Γ1 ,nd Γ1) (CtxPath' Γ1) (p ×subst p) ×t substTy (Γ2 ,nd Γ2) (CtxPath' Γ2) (q ×subst q)

    CtxPath = {!!}
{-
    CtxPath {Γ' = ·} θ1 θ2 = 1t
    CtxPath {Γ' = Γ' , A₁} θ1 θ2 = 
            Σt (CtxPath {Γ' = Γ'} (p osubst θ1) (p osubst θ2))
               (TmPath Γ' A₁ (p osubst (θ1 osubst p)) (p osubst (θ2 osubst p)) {!i0!} {!iS i0!} {!!})
-}
    interpSubst · θ' = <>
    interpSubst (θ , x) θ' = interpSubst θ θ' , interpTm x θ'
    interpSubst p θ' = fst θ'
    interpSubst q θ' = snd θ'
    interpSubst idsubst θ' = θ'
    interpSubst (θ1 osubst θ2) θ' = interpSubst θ1 (interpSubst θ2 θ')
    interpSubst (θ1 ,subst θ2) θ' = (interpSubst θ1 θ' , interpSubst θ2 θ')

    TmPath {Γ} Γ' AA θ1 θ2 δ M1 M2 = substTy1 (substTy Γ' AA θ1 ×t substTy Γ' AA θ2)
                                              (TmPath' Γ' AA θ1 θ2 δ)
                                              (M1 ,nd M2)
    
    TmPath' Γ' 1t θ1 θ2 δ = 1t
    TmPath' Γ' (A' ×t A'') θ1 θ2 δ = substTy1' (substTy Γ' A' θ1 ×t substTy Γ' A' θ2)
                                             (TmPath' Γ' A' θ1 θ2 δ)
                                             (fstd (fstd i0) ,nd fstd (sndnd i0))
                                             id
                                    ×t
                                    substTy1' (substTy Γ' A'' θ1 ×t substTy Γ' A'' θ2)
                                             (TmPath' Γ' A'' θ1 θ2 δ)
                                             (sndnd (fstd i0) ,nd sndnd (sndnd i0))
                                             id
    TmPath' Γ' (Σt A' A'') θ1 θ2 δ = {!!} 
    TmPath' Γ' (substTy Γ'' A θ) θ1 θ2 δ = TmPath' Γ'' A (θ osubst θ1) (θ osubst θ2) δ
    TmPath' Γ' (substTy1 A0 A M) θ1 θ2 δ = {!!}
    TmPath' Γ' (substTy1' B C M pp) θ1 θ2 δ = TmPath' (Γ' , {!B!}) {!!} {!!} {!!} {!!}

    TmPath'' Γ' 1t = 1t
    TmPath'' Γ' (A' ×t A'') = substTy1' {!!} (TmPath'' Γ' A') {!!} id ×t {!!}
    TmPath'' Γ' (Σt AA AA₁) = {!!}
    TmPath'' Γ' (substTy Γ'' AA θ) = {!!}
    TmPath'' Γ' (substTy1 AA AA₁ M) = {!!}
    TmPath'' Γ' (substTy1' B C M pp) = {!pp!}
