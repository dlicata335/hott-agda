{-# OPTIONS --type-in-type  --without-K #-} 

open import lib.Prelude 
open Paths
open import canonicity-irrel.ReducibilityLazy 

module canonicity-irrel.Contexts where

  mid : {A : Set} (As : ValuableTy A) -> Map As As (\ x -> x)
  mid As = smap (λ vM → vM)
                (λ {_}{_}{α} vα → head-expand≃ As vα (resp-id α))

  record Squash (A : Set) : Set where
    constructor squash
    field
      .proof : A

  record EvalsTo {A : Set} (P : A -> Set) (M : A) : Set where
    field
      v   : A
      val : P v
      ev  : M ≃ v 

  ΣValue : {Γ : Set} (vΓ : ValuableTy Γ) {A : Γ -> Set} (sA : Ty vΓ A) (M : (Σ A)) -> Set 
  ΣValue vΓ sA M = Σ (λ (v1 : Valuable vΓ (fst M)) → Valuable (tred sA v1) (snd M))

  ΣValue≃ : {Γ : Set} (vΓ : ValuableTy Γ) {A : Γ -> Set} (sA : Ty vΓ A) 
          -> {M N : (Σ A)} (vM : (ΣValue vΓ sA M)) (vN : (ΣValue vΓ sA N)) (α : M ≃ N) -> Set 
  ΣValue≃ vΓ sA vM vN α = 
             Σ \ (vα : Valuable≃ vΓ (fst vM) (fst vN) (resp fst α)) -> 
               Valuable≃ (tred sA (fst vN)) (mred (ssubst sA vα) (snd vM))
                                            (snd vN)
                                            (snd≃ α)

  head-expand-test : ∀ {A} {B : A -> Set} 
                       (vA : ValuableTy A) (sB : Ty vA B)
                       (M N : Σ B) 
                   -> Id N M 
                   -> ΣValue vA sB M -> ΣValue vA sB N
  head-expand-test vA vB M N α vM = 
    head-expand vA (fst vM) (fst≃ α) , 
    {! head-expand (tred vB (fst vM)) (snd vM) (snd≃ α)!}
    -- head-expand (tred vB (head-expand vA (fst p) (resp fst α))) 
    --             {! (mred (ssubst vB{_}{_}{fst≃ α} {!!}) (snd p)) !} 
    --             (! (snd≃ (! α)))
  -- head-expand vA (fst p) (fst≃ α) : Valuable vA (fst N)
  -- snd p : Valuable (tred vB (fst p)) (snd M)
  -- snd≃ α : Id (subst .B (resp fst α) (snd N)) (snd M)
  -- Goal: Valuable (tred vB (head-expand vA (fst p) (resp fst α))) (snd N)


{-
  Σc : {Γ : Set} (vΓ : ValuableTy Γ) {A : Γ -> Set} (sA : Ty vΓ A) -> ValuableTy (Σ A)
  Σc {Γ} vΓ {A} sA = 
    record {
      Valuable = \ M -> (EvalsTo (ΣValue vΓ sA) M); -- FIXME squashing
      propv = FIXMEChecked;
      Valuable≃ = \ vM vN α -> (EvalsTo (ΣValue≃ vΓ sA vM vN α)); -- FIXME squashing
      propv≃ = FIXMEChecked;
      head-expand = λ {M} {N} vN e → ?;
      -- only admissible if subst works for e:
      -- (head-expand vΓ (fst vN) (fst≃ e)) , 
      --  head-expand (tred sA (head-expand vΓ (fst vN) (resp fst e)))
      --    (mred (ssubst sA {!! (fst≃ e)!})
      --     (head-expand (tred sA (fst vN)) (snd vN) (snd≃ e)))
      --   {!!};
      head-expand≃ = {!!};
      vRefl = λ vM → (vRefl vΓ (fst vM)) , retype≃1 (tred sA (fst vM)) (vRefl (tred sA (fst vM)) (snd vM));
      v! = {!!};
      v∘ = {!!} }
-}

{-

  mfst :  {Γ : Set} (sΓ : ValuableTy Γ) {A : Γ -> Set} (sA : Ty sΓ A) 
       -> Map (Σc sΓ sA) sΓ fst
  mfst sΓ sA = smap (λ {(cpair vM vN) → vM})
                    (λ { {._} (cpair≃{_}{_}{α} vα{_}{_}{β} vβ) → head-expand≃ vα (Σ≃β1 α β) FIXMEEval}) 
                  

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
  mpair {_}{sΓ} {A = A}{θ = θ}{M = M} sθ sM = smap (λ x → valuable _ (cpair (mred sθ x) (red sM x)) Refl FIXMEEval)
                         (λ { {M1}{M2}{α}{_}{_} vα → valuable≃ _ 
                                           (cpair≃ (mresp sθ vα){_}{_}{respd M (resp (unmove sΓ) α) ∘ !
                                                                                                        (app≃ (subst-o A θ (resp (subst (λ x → x) (! (evty sΓ))) α))
                                                                                                         {M (subst (λ x → x) (! (evty sΓ)) M1)})
                                                                                                        ∘ resp (λ x → subst A x (M (subst (λ x' → x') (! (evty sΓ)) M1)))
                                                                                                            (resp-o θ (λ x → subst (λ x' → x') (! (evty sΓ)) x) α)} 
                                                   (valuable≃ (v≃ (sresp sM vα)) (val≃ (sresp sM vα)) (ev≃ (sresp sM vα) ∘ FIXMETodo) FIXMEEval)) -- contract α; there's one FIXMEChecked that needs to disappear
                                           (lemma α vα) FIXMEEval }) -- contract α 
        where
          lemma : ∀ {M1}{M2}(α : Id M1 M2) -> ∀ {vM1}{vM2} (vα : Value≃ (valty sΓ) vM1 vM2 α) -> Id _ _ 
          lemma Refl _ = Refl

                                           -- (cpair≃ (mresp sθ vα){_}{_}{respd M (resp (unmove sΓ) α) ∘ !
                                           --                                                              (app≃ (subst-o A θ (resp (subst (λ x → x) (! (evty sΓ))) α))
                                           --                                                               {M (subst (λ x → x) (! (evty sΓ)) M1)})
                                           --                                                              ∘ resp (λ x → subst A x (M (subst (λ x' → x') (! (evty sΓ)) M1)))
                                           --                                                                  (resp-o θ (λ x → subst (λ x' → x') (! (evty sΓ)) x) α)} 
                                           --         (valuable≃ (v≃ (sresp sM vα)) (val≃ (sresp sM vα)) {!!} FIXMEEval))
                                           -- {!!} FIXMEEval }) 
-}

