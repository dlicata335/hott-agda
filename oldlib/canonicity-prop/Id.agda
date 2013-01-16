{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open Paths
open import canonicity-prop.Reducibility


module canonicity-prop.Id where

  Idc : {A : Set} (vA : CTy A) {M N : A} (vM : Red vA M) (vN : Red vA N) -> CTy (Id M N)
  Idc vA vM vN = record {
                        Red = λ x → Red≃ vA vM vN x;  -- OPTION: could squash this if Red≃ weren't already a prop
                        propr = propr≃ vA;
                        Red≃ = λ _ _ _ → Unit;
                        propr≃ = λ M' N' → Refl;
                        head-expand = λ rα E ev → head-expand≃ vA rα E ev;
                        head-expand≃ = λ x E x' → <>;
                        rRefl = λ rM → <>;
                        r! = λ rα → <>;
                        r∘ = λ rβ rα → <>;
                        eval-red≃ = λ α x → <> }

  sId : {Γ : Set} {Γs : CTy Γ}
         {A : Γ -> Set} {As : Ty Γs A} 
         {M N : (g : Γ) -> A g} (Ms : Tm Γs As M) (Ns : Tm Γs As N) 
         -> Ty Γs (\ x -> Id (M x) (N x))
  sId {Γ} {Γs} {A} {As} {M} {N} Ms Ns = 
    ty (λ rθ → Idc (tred As rθ) (red Ms rθ) (red Ns rθ)) 
       (λ {θ1}{θ2}{α}{rθ1}{rθ2} rα → 
         head-expand-map 
               (smap (λ {β} rβ → (r∘ (tred As rθ2) (sresp Ns rα)
                           (r∘ (tred As rθ2) (mresp (ssubst As rα) rβ)
                           (r! (tred As rθ2) (sresp Ms rα)))))
                     (λ rα' → <>))
               (λ≃ (subst-Id-d M N α)) 
               {!!})

  sRefl : {Γ : Set} {Γs : CTy Γ}
          {A : Γ -> Set} {As : Ty Γs A} 
          {M : (g : Γ) -> A g} (sM : Tm Γs As M) 
        -> Tm Γs (sId sM sM) (\ θ -> Refl{_}{M θ})
  sRefl {As = As} sM = tm (λ vθ → rRefl (tred As vθ) (red sM vθ))
                          (λ vα → <>) -- there would need to be work here if the Red≃'s of Id didn't accept everything

--  sJ : 