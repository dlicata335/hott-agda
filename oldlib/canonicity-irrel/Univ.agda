{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open Paths
open import canonicity.Reducibility
open import canonicity.Contexts


module canonicity.Univ where

  U = Set -- FIXME level issues

  data Value≃U {A B : Set} (vA : ValuableTy A) (vB : ValuableTy B) : Id A B -> Set where
    univ : ∀ {f : A -> B} 
             -> {isa : IsAEq f}
             -> Map vA vB f  -- FIXME need this for the rest, too
             -> Value≃U vA vB (ua (f , isa)) 

  cU : ValuableTy U -- lazy
  cU = valuablety U (record { Value = ValuableTy; 
                              Value≃ = Value≃U; 
                              vRefl = {!!}; v! = {!!}; v∘ = {!!} })
                      Refl FIXMEEval

  sU : ∀ {Γ} {vΓ : ValuableTy Γ} -> Ty vΓ (\ _ -> U)
  sU {vΓ} = ty (λ _ → cU) (λ vα → smap (λ x → valuable _ x {!!} FIXMEEval) 
                                     (λ vα' → valuable≃ _ vα' {!!} FIXMEEval))

  sEl : ∀ {Γ} (vΓ : ValuableTy Γ) -> Ty (Σc vΓ sU) snd
  sEl = λ vΓ → ty (λ { {x , A} (cpair vx vA) → head-expand-ty (val vA) (ev vA ∘ {!!}) FIXMEEval })
                  (λ { {._} (cpair≃ vα (valuable≃ ._ (univ sf) eβ _)) → 
          smap (λ vA → valuable _ (val (mred sf vA)) (ev (mred sf vA) ∘ FIXMETodo) FIXMEEval) -- OK modulo adjustments
               (λ { {_}{_}{_}{_}{_} vα' → valuable≃ _ (val≃ (mresp sf vα')) (ev≃ (mresp sf vα') ∘ {!!}) FIXMEEval}) } ) -- easy if you J α'