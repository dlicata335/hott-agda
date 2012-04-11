{-# OPTIONS --type-in-type  --without-K #-} 

open import lib.Prelude 
open Paths
open import canonicity-prop.Reducibility

module canonicity-prop.Contexts where

  mid : {A : Set} (As : CTy A) -> Map As As (\ x -> x)
  mid As = smap (λ rM → rM)
                (λ {_}{_}{α} rα → head-expand≃ As rα (resp-id α) FIXMEEval)

  ΣRed : {Γ : Set} (rΓ : CTy Γ) {A : Γ -> Set} (sA : Ty rΓ A) (M : (Σ A)) -> Set 
  ΣRed rΓ sA M = Σ (λ (r1 : Red rΓ (fst M)) → Red (tred sA r1) (snd M))

  ΣRed≃ : {Γ : Set} (rΓ : CTy Γ) {A : Γ -> Set} (sA : Ty rΓ A) 
          -> {M N : (Σ A)} (rM : (ΣRed rΓ sA M)) (rN : (ΣRed rΓ sA N)) (α : M ≃ N) -> Set 
  ΣRed≃ rΓ sA rM rN α = 
             Σ \ (rα : Red≃ rΓ (fst rM) (fst rN) (resp fst α)) -> 
               Red≃ (tred sA (fst rN)) (mred (ssubst sA rα) (snd rM))
                                             (snd rN)
                                             (snd≃ α)

  Σc : {Γ : Set} (rΓ : CTy Γ) {A : Γ -> Set} (sA : Ty rΓ A) -> CTy (Σ A)
  Σc {Γ} rΓ {A} sA = 
    record {
      Red = (ΣRed rΓ sA) ;
      propr = FIXMETodo; -- hprop is closed under Σ right?
      Red≃ = ΣRed≃ rΓ sA ; 
      propr≃ = FIXMEChecked;
      head-expand = λ {M} {N} rN α E → 
       (head-expand rΓ (fst rN) (fst≃ α) FIXMEEval , 
        head-expand (tred sA (head-expand rΓ (fst rN) (fst≃ α) FIXMEEval))
                    (mred (ssubst sA (eval-red≃ rΓ (! (fst≃ α)) FIXMEEval))
                    (head-expand (tred sA (fst rN)) (snd rN) (snd≃ α) FIXMEEval) )
                    FIXMEChecked FIXMEEval);
      head-expand≃ = λ x E x' → (head-expand≃ rΓ (fst x) (resp (resp fst) E) FIXMEEval) , 
                                {!head-expand≃ snd x!};
      rRefl = λ rM → (rRefl rΓ (fst rM)) , retype≃1 (tred sA (fst rM)) (rRefl (tred sA (fst rM)) (snd rM));
      r! = λ {M}{N}{α}{rM}{rN} rα → (head-expand≃ rΓ (r! rΓ (fst rα)) FIXMEChecked FIXMEEval) , 
                  {!r! (tred sA (fst rN)) (snd rα)!};
      r∘ = λ rβ rα → (head-expand≃ rΓ (r∘ rΓ (fst rβ) (fst rα)) FIXMEChecked FIXMEEval) , 
                    {!!};
      eval-red≃ = λ {M} {N} {rM} {rN} α E → (eval-red≃ rΓ (resp fst α) FIXMEEval) , 
                                            eval-red≃ (tred sA (fst rN)) (snd≃ α) FIXMEEval}

  mfst :  {Γ : Set} (sΓ : CTy Γ) {A : Γ -> Set} (sA : Ty sΓ A) 
       -> Map (Σc sΓ sA) sΓ fst
  mfst sΓ sA = smap (λ x → fst x)
                    (λ rα → fst rα)
                  
  svar : {Γ : Set} (sΓ : CTy Γ) {A : Γ -> Set} (sA : Ty sΓ A) 
      -> Tm (Σc sΓ sA) (mto sA (mfst sΓ sA)) snd
  svar sΓ sA = tm snd (λ {M}{N}{α} rα → {!respd snd α!})

-- snd≃ α : Id (subst .A (resp fst α) (snd M)) (snd N)
-- respd snd α: Id (subst (λ z → .A (fst z)) α (snd M)) (snd N)

                  
  mpair : {Γ : Set} {sΓ : CTy Γ} 
          {Δ : Set} {sΔ : CTy Δ} 
          {A : Δ -> Set} {sA : Ty sΔ A}
          -> ∀ {θ} {M}
        -> (sθ : Map sΓ sΔ θ)
        -> Tm sΓ (mto sA sθ) M
        -> Map sΓ (Σc sΔ sA) (\ x -> θ x , M x)
  mpair {_}{sΓ}{Δ}{sΔ} {A = A}{θ = θ}{M = M} sθ sM = 
    smap (λ x → (mred sθ x) , (red sM x))
         (λ rα → head-expand≃ sΔ (mresp sθ rα) {!!} {!!} , 
                 {!sresp sM rα !})

  apply1 : ∀ {Γ A B} {rΓ : CTy Γ} 
         -> (sA : Ty rΓ A)
         -> (sB : Ty (Σc rΓ sA) B)
         -> ∀ {θ} (rθ : Red rΓ θ)
         -> Ty (tred sA rθ) (\ y -> B (θ , y))
  apply1 {Γ}{A}{rΓ = rΓ} sA sB {θ} vθ = 
    ty (λ {θ'} vθ' → tred sB (vθ , vθ')) 
       (λ {θ1} {θ2} {α} {rθ1} {rθ2} rα → 
         head-expand-map (ssubst sB {θ , θ1}{θ , θ2}{pair≃ (Refl {_} {θ}) α}
                                    {_}{_}
                                    ( (head-expand≃ rΓ (rRefl rΓ vθ) (Σ≃β1 Refl α) FIXMEEval) , 
                                      head-expand≃ (tred sA vθ){_}{_}{_}{_}{α ∘ resp (λ x → subst A x θ1) (Σ≃β1 {_} {A} Refl α)}
                                                  (r∘ (tred sA vθ) rα 
                                                      (eval-red≃ (tred sA vθ) 
                                                         (resp (λ x → subst A x θ1) (Σ≃β1 {_} {A} Refl α)) 
                                                         FIXMEEval)) 
                                                  (Σ≃β2 {Γ} {A} {θ , θ1} {θ , θ2} Refl α) FIXMEEval))
                         FIXMEChecked FIXMEEval)


  sΣ : ∀ {Γ A B} {vΓ : CTy Γ} 
     -> (sA : Ty vΓ A)
     -> (sB : Ty (Σc vΓ sA) B)
     -> Ty vΓ (\ x -> Σ \ (y : A x) -> B (x , y))
  sΣ {Γ}{A}{B}{vΓ} sA sB =
    ty (λ vθ → Σc (tred sA vθ) (apply1 sA sB vθ)) 
       (λ {θ1} {θ2} {α} {rθ1} {rθ2} rα → 
         head-expand-map (smap (λ {P} rP → (mred (ssubst sA rα) (fst rP)) , coe {!!} (ssubst sB (rα , rRefl _ _))) 
                               {!!}) 
                         (λ≃ (subst-Σ α A (λ x y → B (x , y)))) FIXMEEval)
