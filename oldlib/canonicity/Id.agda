{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open Paths
open import canonicity.Reducibility


module canonicity.Id where

  -- lazy identity types:
  -- this makes the definitions work out better, and
  -- makes sense because type theory is missing the injection from paths to elements of the identity types;
  -- if that were there, the path sitting under it would be lazy by
  -- analogy to Σ
  -- 
  -- Never use subst/resp for this!
  Idc : {A : Set} {vA : ValuableTy A} {M N : A} (vM : Valuable vA M) (vN : Valuable vA N) -> ValueTy (Id M N)
  Idc {_}{vA} vM vN = record { Value = Valuable≃ vA vM vN ; 
                       Value≃ = λ _ _ _ → Unit; 
                       vRefl = λ vM' → valuable≃0 Refl <> Refl evRefl;
                       v∘ = λ vβ vα → valuable≃0 _ _ Refl evRefl;
                       v! = λ vα → valuable≃0 _ <> Refl evRefl}

  sId : {Γ : Set} {Γs : ValuableTy Γ}
         {A : Γ -> Set} {As : Ty Γs A} 
         {M N : (g : Γ) -> A g} (Ms : Tm Γs As M) (Ns : Tm Γs As N) 
         -> Ty Γs (\ x -> Id (M x) (N x))
  sId {Γ} {Γs} {A} {As} {M} {N} Ms Ns = 
               ty (λ θs → retty (Idc (red Ms θs) (red Ns θs))) 
                  (λ {θ1} {θ2} {α} {vθ1} {vθ2} vα → smap (λ {M'} vM' → valuable _ (v∘' (tred As vθ2) (v∘' (tred As vθ2) (sresp Ns vα) (mresp' (ssubst As vα) vM')) (v!' (tred As vθ2) (sresp Ms vα)))
                                                                                 ({!Refl!} ∘ subst-Id-d M N (resp (subst (λ x → x) (! (evty Γs))) α) M') FIXMEEval)
                                                         (λ vα' → valuable≃ _ _ Refl FIXMEEval))
                     --         ({!!} ∘ subst-Id-d M N α _) 
  
  sRefl : {Γ : Set} {Γs : ValuableTy Γ}
          {A : Γ -> Set} {As : Ty Γs A} 
          {M : (g : Γ) -> A g} (sM : Tm Γs As M) 
        -> Tm Γs (sId sM sM) (\ θ -> Refl{_}{M θ})
  sRefl {As = As} sM = tm (λ vθ → valuable _ (vRefl' (red sM vθ)) Refl FIXMEEval)
                          (λ vα → valuable≃ _ _ Refl FIXMEEval) -- there would need to be work here if the Value≃'s of Id didn't accept everything

--  sJ : 