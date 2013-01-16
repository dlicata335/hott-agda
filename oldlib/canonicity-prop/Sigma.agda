{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open Paths
open import canonicity.Reducibility
open import canonicity.Contexts

module canonicity.Sigma where

  ret : ∀ {Γ} (vΓ : ValuableTy Γ) -> ∀ {θ} -> Value (valty vΓ) θ -> Valuable vΓ (unmove vΓ θ)
  ret vΓ vθ = valuable _ vθ (coe-inv-2 (evty vΓ)) FIXMEEval

  ret≃ : ∀ {Γ} (vΓ : ValuableTy Γ) -> ∀ {θ1 θ2 α} -> (vθ1 : Value (valty vΓ) θ1) (vθ2 : Value (valty vΓ) θ2)
         (vα : Value≃ (valty vΓ) vθ1 vθ2 α) 
       -> Valuable≃ vΓ (ret vΓ vθ1) (ret vΓ vθ2) (resp (unmove vΓ) α)
  ret≃ vΓ vα = {!!}

  postulate
    ssubst-refl-cancels : 
         ∀ {Γ A} {vΓ : ValuableTy Γ} 
         -> (sA : Ty vΓ A)
         -> ∀ {θ}  (vθ : Value (valty vΓ) θ)
         -> ∀ {θ1} (vθ1 : Value (valty (tred sA vθ)) θ1)
         -> Value≃ (valty (tred sA vθ)) (val (mred (ssubst sA (val≃0 (vRefl (valty vΓ) vθ))) vθ1)) vθ1 
                   ((coe-inv-2 (evty (tred sA vθ)) ∘
                       !
                       (resp
                        (λ x →
                           subst (λ x' → x') (evty (tred sA vθ))
                           (subst A (resp (subst (λ x' → x') (! (evty vΓ))) x)
                            (subst (λ x' → x') (! (evty (tred sA vθ))) θ1)))
                        (ev≃0 (vRefl (valty vΓ) vθ)))) ∘ ! (ev (mred (ssubst sA (val≃0 (vRefl (valty vΓ) vθ))) vθ1)))

  apply1 : ∀ {Γ A B} {vΓ : ValuableTy Γ} 
         -> (sA : Ty vΓ A)
         -> (sB : Ty (Σc vΓ sA) B)
         -> ∀ {θ} (vθ : Value (valty vΓ) θ)
         -> Ty (tred sA vθ) (\ y -> B (unmove vΓ θ , y))
  apply1 {vΓ = vΓ} sA sB {θ} vθ = 
    ty (λ vθ' → tred sB (cpair (ret vΓ vθ) (valuable _ vθ' FIXMETodo FIXMEEval)))
       (λ { {θ1}{θ2}{α}{vθ1}{vθ2} vα → 
       smap (λ {M} vM → 
             valuable _ 
                     (val (mred (ssubst sB (cpair≃ (vRefl' (ret vΓ vθ)) {_}{_}{resp (unmove (tred sA vθ)) α} 
                                                   (valuable≃ _
                                                              {! vα !} -- (val≃0 (v∘ (valty (tred sA vθ)) vα (ssubst-refl-cancels sA vθ vθ1)))
                                                              (ev≃0 (v∘ (valty (tred sA vθ)) vα (ssubst-refl-cancels sA vθ vθ1))
                                                                 ∘ FIXMETodo) FIXMEEval))) -- doesn't mention ssubst-refl-cancels at least
                                                   vM))
                     FIXMEChecked -- contract α and then d:        
                     -- (ev
                     --    (mred
                     --     (ssubst sB
                     --      (cpair≃
                     --       (valuable≃ (v≃0 (vRefl (valty vΓ) vθ))
                     --        (val≃0 (vRefl (valty vΓ) vθ))
                     --        (ev≃0 (vRefl (valty vΓ) vθ) ∘ FIXMEChecked) FIXMEEval)
                     --       (valuable≃
                     --        (v≃0 (v∘ (valty (tred sA vθ)) vα (ssubst-refl-cancels sA vθ vθ1)))
                     --        (val≃0
                     --         (v∘ (valty (tred sA vθ)) vα (ssubst-refl-cancels sA vθ vθ1)))
                     --        (ev≃0 (v∘ (valty (tred sA vθ)) vα (ssubst-refl-cancels sA vθ vθ1))
                     --         ∘ FIXMETodo)
                     --        FIXMEEval)))
                     --     vM))
                     FIXMEEval)
                    {!!} })

{-
  sΣ : ∀ {Γ A B} {vΓ : ValuableTy Γ} 
     -> (sA : Ty vΓ A)
     -> (sB : Ty (Σc vΓ sA) B)
     -> Ty vΓ (\ x -> Σ \ (y : A x) -> B (x , y))
  sΣ = λ sA sB → ty (λ vθ → Σc (tred sA vθ) (apply1 sA sB vθ)) 
                    (λ vα → smap (λ { {._} (cpair vM1 vM2)  → valuable {!subst .A (resp (unmove .vΓ) .α) .M , _!} (cpair (mred' (ssubst sA vα) vM1) {!!}) {!!} {!!} }) {!!})
-}