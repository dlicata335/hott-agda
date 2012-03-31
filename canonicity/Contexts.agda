{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open Paths
open import canonicity.Reducibility 

module canonicity.Contexts where

  mid : {A : Set} (As : ValuableTy A) -> Map As As (\ x -> x)
  mid As = smap (λ vM → valuable _ vM (coe-inv-2 (evty As)) FIXMEEval) 
                (λ {_}{_}{α} vα → valuable≃ _ vα FIXMEChecked FIXMEEval) -- massage using resp-by-id coe-inv-2 


  -- WARNING: never use subst/resp on these

  -- both Σ itself is lazy,
  -- and values of Σ type are lazy

  data ΣValue {Γ : Set} (vΓ : ValuableTy Γ) {A : Γ -> Set} (sA : Ty vΓ A) : (Σ A) -> Set where
    cpair : {M : _} 
            -> (vM : Valuable vΓ M) -> {N : _} -> Valuable (tred' sA vM) N 
            -> ΣValue vΓ sA (M , N)

  data ΣValue≃ {Γ : Set} (vΓ : ValuableTy Γ) {A : Γ -> Set} (sA : Ty vΓ A) 
               : {M N : (Σ A)} (vM : ΣValue vΓ sA M) (vN : ΣValue vΓ sA N) (α : M ≃ N) -> Set where
    cpair≃ : ∀ {M1 M2 α} {vM1 : Valuable vΓ M1} {vM2 : Valuable vΓ M2} 
            -> (vα : Valuable≃ vΓ vM1 vM2 α)
            -> ∀ {N1 N2 β} {vN1 : Valuable (tred' sA vM1) N1} {vN2 : Valuable (tred' sA vM2) N2 }
            -> Valuable≃ (tred' sA vM2) (mred' (ssubst' sA vα) vN1)
                                        vN2
                                        β
            -> ΣValue≃ vΓ sA (cpair vM1 vN1) (cpair vM2 vN2) (pair≃ α β) 

  Σval : {Γ : Set} (vΓ : ValuableTy Γ) {A : Γ -> Set} (sA : Ty vΓ A) -> ValueTy (Σ A)
  Σval vΓ sA = record { Value = ΣValue vΓ sA; 
                        Value≃ = ΣValue≃ vΓ sA; 
                        vRefl = FIXMETodo; v! = FIXMETodo; v∘ = FIXMETodo }
  
  Σc : {Γ : Set} (vΓ : ValuableTy Γ) {A : Γ -> Set} (sA : Ty vΓ A) -> ValuableTy (Σ A)
  Σc {Γ} vΓ {A} sA = valuablety (Σ (\ (x : Γ) -> A x))
                                (Σval vΓ sA) Refl FIXMEEval


  mfst :  {Γ : Set} (sΓ : ValuableTy Γ) {A : Γ -> Set} (sA : Ty sΓ A) 
       -> Map (Σc sΓ sA) sΓ fst
  mfst sΓ sA = smap (λ {(cpair vM vN) → vM})
                    (λ { {._} (cpair≃{_}{_}{α} vα{_}{_}{β} vβ) → head-expand≃ vα (Σ≃β1 α β) FIXMEEval}) -- head-expand
                  

  svar : {Γ : Set} (sΓ : ValuableTy Γ) {A : Γ -> Set} (sA : Ty sΓ A) 
      -> Tm (Σc sΓ sA) (mto sA (mfst sΓ sA)) snd
  svar sΓ sA = tm (λ {(cpair vM vN) → vN})
                  (λ { {._} (cpair≃ vα vβ) → valuable≃ _ (val≃ vβ) 
                                             (ev≃ vβ ∘ FIXMETodo) FIXMEEval}) -- probably true; didn't check that all the adjustments work

  mpair : {Γ : Set} {sΓ : ValuableTy Γ} 
          {Δ : Set} {sΔ : ValuableTy Δ} 
          {A : Δ -> Set} {sA : Ty sΔ A}
          -> ∀ {θ} {M}
        -> (sθ : Map sΓ sΔ θ)
        -> Tm sΓ (mto sA sθ) M
        -> Map sΓ (Σc sΔ sA) (\ x -> θ x , M x)
  mpair {_}{sΓ} {M = M} sθ sM = smap (λ x → valuable _ (cpair (mred sθ x) (red sM x)) Refl FIXMEEval)
                         (λ {_}{_}{α}{_}{_} vα → valuable≃ _ 
                                           (cpair≃ (mresp sθ vα){_}{_}{respd M (resp (unmove sΓ) α) ∘ {!!}} 
                                                   (valuable≃ (v≃ (sresp sM vα)) (val≃ (sresp sM vα)) {!!} FIXMEEval))
                                           {!!} FIXMEEval) -- (cpair≃ (mresp sθ vα){_}{_}{v≃ (sresp sM vα)}{_}{_} (valuable≃ _ (val≃ (sresp sM vα)) {!!} FIXMEEval)) {!!} FIXMEEval)