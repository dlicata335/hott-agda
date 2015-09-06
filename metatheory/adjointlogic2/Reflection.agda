
open import adjointlogic2.Lib
open import adjointlogic2.Rules
open import adjointlogic2.Properties
open import adjointlogic2.General
open import adjointlogic2.TripleAdjunction 

module adjointlogic2.Reflection where

  -- for some reason the rewrites only work if we define the theory in that file
  open adjointlogic2.Rules.Reflection

  -- note that for this theory
  -- s ≥ s has only 1m
  -- c ≥ c has two maps, 1m and ∇m ∘m Δm, with 1m ⇒ ∇m ∘m Δm

  postulate
   adjeq1 : _==_ {∇m ⇒ ∇m} (∇Δunit ∘1cong 1⇒{_}{_}{∇m}) 1⇒
   adjeq2 : _==_ {Δm ⇒ Δm} (1⇒ {_} {_} {Δm} ∘1cong ∇Δunit) 1⇒

  module A = TripleAdjunction c s ∇m Δm ∇Δunit 1⇒ adjeq2 adjeq1
  open A

  {-
  -- we don't want the identity that collapses ♭ and ♯
  wrongdirection : ∀ {A} → A [ 1m ]⊢ ♭ A
  wrongdirection {A} = cut (cut {!NO!} (Ffunc∘2 {α = Δm} {β = ∇m})) (Ffunc {α = Δm} mergeFU)

  wrongdirection2 : ∀ {A} → ♯ A [ 1m ]⊢ A
  wrongdirection2 {A} = cut (Ufunc mergeFU) (cut Ufunc∘1 {!NO!}) 
  -}

  F∇Δcancel : NatIso (Ffunctor ∇m ∘Func Ffunctor Δm) 1Func
  F∇Δcancel = !natiso (F∘-natiso {α = ∇m} {β = Δm}) ·NatIso F1-natiso

  UΔ∇cancel : NatIso (Ufunctor Δm ∘Func Ufunctor ∇m) 1Func
  UΔ∇cancel = !natiso (U∘-natiso {α = ∇m} {β = Δm}) ·NatIso U1-natiso

  -- the monad for Δ and the comonad for ∇ are trivial

  collapseΔ : NatIso (◯functor Δm) 1Func
  collapseΔ = (mergeUF-natiso ∘Func-cong-iso 1NatIso (Ffunctor Δm)) ·NatIso F∇Δcancel 

  collapse∇ : NatIso 1Func (□functor ∇m)
  collapse∇ = !natiso UΔ∇cancel ·NatIso (mergeUF-natiso ∘Func-cong-iso 1NatIso (Ufunctor ∇m))

  -- ♯ and ♭ are idempotent

  ♯idempotent : NatIso ♯functor (♯functor ∘Func ♯functor)
  ♯idempotent = (1NatIso (Ufunctor ∇m) ∘Func-cong-iso !natiso (∘Func-unit-l-natiso {_} {_} {Ffunctor ∇m})) ·NatIso
                ((1NatIso (Ufunctor ∇m) ∘Func-cong-iso (collapse∇ ∘Func-cong-iso 1NatIso (Ffunctor ∇m))) ·NatIso
                 ((1NatIso (Ufunctor ∇m) ∘Func-cong-iso ∘Func-assoc-natiso (Ffunctor ∇m) (Ufunctor ∇m) (Ffunctor ∇m)) ·NatIso !natiso (∘Func-assoc-natiso ♯functor (Ffunctor ∇m) (Ufunctor ∇m))))

  ♭idempotent : NatIso (♭functor ∘Func ♭functor) ♭functor
  ♭idempotent = (∘Func-assoc-natiso (Ffunctor Δm ∘Func Ufunctor Δm) (Ufunctor Δm) (Ffunctor Δm) ·NatIso (1NatIso (Ffunctor Δm) ∘Func-cong-iso !natiso (∘Func-assoc-natiso (Ufunctor Δm) (Ffunctor Δm) (Ufunctor Δm)))) ·NatIso 
                 ((1NatIso (Ffunctor Δm) ∘Func-cong-iso (collapseΔ ∘Func-cong-iso 1NatIso (Ufunctor Δm))) ·NatIso
                  (1NatIso (Ffunctor Δm) ∘Func-cong-iso ∘Func-unit-l-natiso {_} {_} {Ufunctor Δm}))


  -- ♭ (♯ A) is equivalent to ♭ A  and   ♯ (♭ A) is equivalent to A

  ♭absorbs♯ : NatIso ♭functor (♭functor ∘Func ♯functor)
  ♭absorbs♯ = ♭'natiso ·NatIso (F∘-natiso {α = Δm} {β = ∇m} ·NatIso 
             ((1NatIso (Ffunctor Δm) ∘Func-cong-iso !natiso (∘Func-unit-l-natiso {_} {_} {Ffunctor ∇m})) ·NatIso
             ((1NatIso (Ffunctor Δm) ∘Func-cong-iso (!natiso UΔ∇cancel ∘Func-cong-iso 1NatIso (Ffunctor ∇m))) ·NatIso 
             ( (1NatIso (Ffunctor Δm) ∘Func-cong-iso ∘Func-assoc-natiso (Ffunctor ∇m) (Ufunctor ∇m) (Ufunctor Δm)) ·NatIso
             !natiso (∘Func-assoc-natiso ♯functor (Ufunctor Δm) (Ffunctor Δm))))))

  ♯absorbs♭ : NatIso ♯functor (♯functor ∘Func ♭functor)
  ♯absorbs♭ = ♯'natiso ·NatIso (U∘-natiso {α = Δm} {β = ∇m} ·NatIso 
             ((1NatIso (Ufunctor ∇m) ∘Func-cong-iso !natiso (∘Func-unit-l-natiso {_} {_} {Ufunctor Δm})) ·NatIso
             ((1NatIso (Ufunctor ∇m) ∘Func-cong-iso (!natiso F∇Δcancel ∘Func-cong-iso 1NatIso (Ufunctor Δm))) ·NatIso
             ((1NatIso (Ufunctor ∇m) ∘Func-cong-iso ∘Func-assoc-natiso (Ufunctor Δm) (Ffunctor Δm) (Ffunctor ∇m)) ·NatIso 
             !natiso (∘Func-assoc-natiso ♭functor (Ffunctor ∇m) (Ufunctor ∇m))))))

  {-
  -- FIXME: could also check that the maps are the same as the retraction in TripleAdjunction

  ♯absorbs♭-map1 : (Iso.f (♯absorbs♭ {P})) ≈ ♯absorbs♭1
  ♯absorbs♭-map1 = UR≈ {α = ∇m} {β = 1m} (UL≈ {γ = 1m} {e = 1⇒} (FR≈ {α = ∇m} {γ = Δm} {e = 1⇒} (FR≈' {γ = 1m} adjeq2 (!≈ (Uη _)))))

  ♯absorbs♭-map2 : (Iso.g (♯absorbs♭ {P})) ≈ ♯absorbs♭2
  ♯absorbs♭-map2 = UR≈ {α = ∇m} {β = 1m} (UL≈ {α = ∇m} {β = ∇m ∘1 1m} {γ = 1m} {e = 1⇒} (FL≈ {α = ∇m} {β = 1m} (FR2 {α = ∇m} {β = 1m ∘1 ∇m} {γ = ∇m ∘1 Δm} {γ' = 1m} {e = 1⇒} {e' = 1⇒} {D = _} {D' = □counit} ∇Δunit adjeq1 (FL≈ {α = Δm} {β = ∇m ∘1 Δm} (eq (ap (λ X → UL {α = Δm} {β = Δm ∘1 (∇m ∘1 Δm)} 1m X hyp) calc)))) ∘≈ Fη (Iso.g (!i mergeUFi ·i (!i collapseΔ ·i mergeUFi)))))
        where
    calc : (((1⇒ {_} {_} {Δm} ∘1cong ∇Δunit) ∘1cong 1⇒ {_} {_} {∇m}) ∘1cong 1⇒ {_} {_} {Δm}) == (1⇒ {_}{_}{Δm} ∘1cong ∇Δunit)
    calc = ! adjeq2 ∘ (ap (λ H → (H ∘1cong 1⇒ {_} {_} {∇m}) ∘1cong 1⇒ {_} {_} {Δm}) adjeq2)
  -}


  -- ----------------------------------------------------------------------
  -- Δ (F Δm) and ∇ (U ∇m) are full and faithful 
  -- (note that Γ (the other two) is not)

  FΔff : FullAndFaithfull (Ffunctor Δm)
  FΔff = retraction-ff (Ffunctor ∇m) F∇Δcancel (λ D → !≈ (fullsquare D)) where
    FΔ∇cancel : NatTrans (Ffunctor Δm ∘Func Ffunctor ∇m) 1Func
    FΔ∇cancel = NatIso-forward (!natiso (F∘-natiso {α = Δm} {β = ∇m})) ·NatTrans (F2-nattrans ∇Δunit ·NatTrans NatIso-forward F1-natiso)  

    lemma : ∀ {A} → (NatTrans.mor FΔ∇cancel {F Δm A}) ≈ Ffunc (Iso.f (NatIso.mor F∇Δcancel)) 
    lemma = FL≈ {α = Δm} {β = 1m} (!≈ (Fη _) ∘≈ FL≈ {α = ∇m} {β = Δm ∘1 1m} (!≈ (Fη _) ∘≈ FL≈ {α = Δm} {β = ∇m ∘1 (Δm ∘1 1m)}(((FR2 {α = Δm} {β = Δm ∘1 (∇m ∘1 Δm)} {γ = 1m} {γ' = 1m} {e = 1⇒ ·2 (1⇒ ∘1cong ∇Δunit)} {e' = 1⇒} {D = hyp} {D' = cut (FR 1m 1⇒ hyp) (cut (FR 1m 1⇒ hyp) (Iso.f (NatIso.mor F∇Δcancel)))} 1⇒ adjeq2 (!≈ (cut-ident-left _ ∘≈ eq (transport⊢1 _) ∘≈ cut-ident-left _ ∘≈ eq (transport⊢1 _) ∘≈ eq (transport⊢1 _) ∘≈ cut-ident-left _ ∘≈ eq (transport⊢1 _) ∘≈ eq (transport⊢1 _))) ∘≈ transport⊢≈ {α = Δm} (1⇒ ∘1cong ∇Δunit) (cut-ident-left (FR 1m 1⇒ hyp) ∘≈ eq (transport⊢1 _))) ∘≈ cut-ident-left _) ∘≈ eq (transport⊢1 _ ∘ transport⊢1 _)))) 

    fullsquare : ∀ {A B} (D : F Δm A [ 1m ]⊢ F Δm B) 
               → cut (Ffunc (Iso.f (NatIso.mor F∇Δcancel))) D ≈ cut (Ffunc {α = Δm} (Ffunc {α = ∇m} D)) (Ffunc (Iso.f (NatIso.mor F∇Δcancel)))
    fullsquare D = cut≈2 (Ffunc {α = Δm} (Ffunc {α = ∇m} D)) (lemma) ∘≈ (NatTrans.square FΔ∇cancel D) ∘≈ cut≈1 (!≈ lemma) D

  U∇ff : FullAndFaithfull (Ufunctor ∇m)
  U∇ff = retraction-ff (Ufunctor Δm) UΔ∇cancel fullsquare where
    U∇Δcancel : NatTrans 1Func (Ufunctor ∇m ∘Func Ufunctor Δm)
    U∇Δcancel = NatIso-forward (!natiso U1-natiso) ·NatTrans (U2-nattrans ∇Δunit ·NatTrans NatIso-forward (U∘-natiso {α = Δm} {β = ∇m}))

    lemma : ∀ {A} → (NatTrans.mor U∇Δcancel {U ∇m A}) ≈ Ufunc (Iso.g (NatIso.mor UΔ∇cancel)) 
    lemma = UR≈ {α = ∇m} {β = 1m} (!≈ (Uη _) ∘≈ UR≈ {α = Δm} {β = 1m ∘1 ∇m} (!≈ (Uη _) ∘≈ UR≈ {α = ∇m} {β = (1m ∘1 ∇m) ∘1 Δm} (UL2 {α = ∇m} {β = (∇m ∘1 Δm) ∘1 ∇m} {γ = 1m} {γ' = (1m ∘1 (Δm ∘1 1m)) ∘1 (∇m ∘1 1m)} {e = 1⇒ ·2 (∇Δunit ∘1cong 1⇒)} {e' = 1⇒} {D = hyp} {D' = cut (cut (Iso.g (NatIso.mor UΔ∇cancel)) (UL 1m 1⇒ hyp)) (UL 1m 1⇒ hyp)} 1⇒ adjeq1 (!≈ (((((cut-ident-left hyp ∘≈ eq (transport⊢1 _)) ∘≈ cut-ident-right (transport⊢ 1⇒ (cut hyp hyp))) ∘≈ eq (transport⊢1 _ ∘ transport⊢1 _)) ∘≈ cut-ident-right (transport⊢ 1⇒ (transport⊢ 1⇒ (cut (transport⊢ 1⇒ (cut hyp hyp)) hyp)))) ∘≈ eq (transport⊢1 _) ∘≈ eq (transport⊢1 _))) ∘≈ transport⊢≈ {α = ∇m} (∇Δunit ∘1cong 1⇒) (cut-ident-right (UL 1m 1⇒ hyp) ∘≈ eq (transport⊢1 _) ∘≈ cut-ident-left (transport⊢ 1⇒ (cut (UL 1m 1⇒ hyp) hyp))))))

    fullsquare' : ∀ {A B} (D : U ∇m A [ 1m ]⊢ U ∇m B) 
               →   cut (Ufunc (Iso.g (NatIso.mor UΔ∇cancel))) (Functor.ar (Ufunctor ∇m) (Functor.ar (Ufunctor Δm) D))
                 ≈ cut D (Ufunc (Iso.g (NatIso.mor UΔ∇cancel)))
    fullsquare' D = (cut≈2 D lemma ∘≈ NatTrans.square U∇Δcancel D) ∘≈ cut≈1 (!≈ lemma) (Functor.ar (Ufunctor ∇m) (Functor.ar (Ufunctor Δm) D))

    fullsquare : ∀ {A B} (D : U ∇m A [ 1m ]⊢ U ∇m B) 
               →   cut (Functor.ar (Ufunctor ∇m) (Functor.ar (Ufunctor Δm) D))
                       (Functor.ar (Ufunctor ∇m) (Iso.f (NatIso.mor UΔ∇cancel)))
                 ≈ cut (Functor.ar (Ufunctor ∇m) (Iso.f (NatIso.mor UΔ∇cancel))) D
    fullsquare D = (((cut-ident-right _ ∘≈ cut≈2 (cut (Functor.ar (Ufunctor ∇m) (Iso.f (NatIso.mor UΔ∇cancel))) D) (Functor.presid (Ufunctor ∇m) ∘≈ Functor.ar≈ (Ufunctor ∇m) (Iso.β (NatIso.mor UΔ∇cancel)) ∘≈ !≈ (Functor.prescut (Ufunctor ∇m) (Iso.g (NatIso.mor UΔ∇cancel)) (Iso.f (NatIso.mor UΔ∇cancel))))) ∘≈ !≈ (cut-assoc (cut (Functor.ar (Ufunctor ∇m) (Iso.f (NatIso.mor UΔ∇cancel))) D) (Ufunc (Iso.g (NatIso.mor UΔ∇cancel))) (Functor.ar (Ufunctor ∇m) (Iso.f (NatIso.mor UΔ∇cancel))))) ∘≈ cut≈1 (cut-assoc (Functor.ar (Ufunctor ∇m) (Iso.f (NatIso.mor UΔ∇cancel))) D (Ufunc (Iso.g (NatIso.mor UΔ∇cancel)))) (Functor.ar (Ufunctor ∇m) (Iso.f (NatIso.mor UΔ∇cancel)))) ∘≈ cut≈1 (cut≈2 (Functor.ar (Ufunctor ∇m) (Iso.f (NatIso.mor UΔ∇cancel))) (fullsquare' D)) (Functor.ar (Ufunctor ∇m) (Iso.f (NatIso.mor UΔ∇cancel))) ∘≈ cut-assoc (Functor.ar (Ufunctor ∇m) (Iso.f (NatIso.mor UΔ∇cancel))) (cut (Ufunc (Iso.g (NatIso.mor UΔ∇cancel))) (Functor.ar (Ufunctor ∇m) (Functor.ar (Ufunctor Δm) D))) (Functor.ar (Ufunctor ∇m) (Iso.f (NatIso.mor UΔ∇cancel))) ∘≈ cut≈2 (Functor.ar (Ufunctor ∇m) (Iso.f (NatIso.mor UΔ∇cancel))) (cut-assoc (Ufunc (Iso.g (NatIso.mor UΔ∇cancel))) (Functor.ar (Ufunctor ∇m) (Functor.ar (Ufunctor Δm) D)) (Functor.ar (Ufunctor ∇m) (Iso.f (NatIso.mor UΔ∇cancel)))) ∘≈ !≈ (cut-assoc (Functor.ar (Ufunctor ∇m) (Iso.f (NatIso.mor UΔ∇cancel))) (Ufunc (Iso.g (NatIso.mor UΔ∇cancel))) (cut (Functor.ar (Ufunctor ∇m) (Functor.ar (Ufunctor Δm) D)) (Functor.ar (Ufunctor ∇m) (Iso.f (NatIso.mor UΔ∇cancel))))) ∘≈ !≈ (cut≈1 {D = cut (Functor.ar (Ufunctor ∇m) (Iso.f (NatIso.mor UΔ∇cancel))) (Ufunc (Iso.g (NatIso.mor UΔ∇cancel)))} {D' = hyp} ((Functor.presid (Ufunctor ∇m) ∘≈ Functor.ar≈ (Ufunctor ∇m) (Iso.α (NatIso.mor UΔ∇cancel))) ∘≈ !≈ (Functor.prescut (Ufunctor ∇m) (Iso.f (NatIso.mor UΔ∇cancel)) (Iso.g (NatIso.mor UΔ∇cancel)))) (cut (Functor.ar (Ufunctor ∇m) (Functor.ar (Ufunctor Δm) D)) (Functor.ar (Ufunctor ∇m) (Iso.f (NatIso.mor UΔ∇cancel))))) ∘≈ !≈ (cut-ident-left _)

  --Pfenning-Davies style rules

  copy : {A : Tp c} → A [ ∇m ∘1 Δm ]⊢ A
  copy = (transport⊢ ∇Δunit hyp)

  ♯'R : { A B : Tp c} → A [ ∇m ∘1 Δm ]⊢ B → A [ 1m ]⊢ ♯' B 
  ♯'R D = UR {α = ∇m ∘1 Δm} {β = 1m} D

  ♯'R2 : { A B : Tp c} → A [ ∇m ∘1 Δm ]⊢ B → A [ ∇m ∘1 Δm ]⊢ ♯' B 
  ♯'R2 D = UR {α = ∇m ∘1 Δm} {β = ∇m ∘1 Δm } D

  ♯'L : { A B : Tp c} → A [ ∇m ∘1 Δm ]⊢ B → ♯' A [ (∇m ∘1 Δm) ]⊢ B
  ♯'L {A}{B} D = UL (∇m ∘1 Δm) 1⇒ D 

  ♭'R : {A B : Tp c} → A [ (∇m ∘1 Δm) ]⊢ B → A [ (∇m ∘1 Δm) ]⊢ ♭' B
  ♭'R D = FR {α = ∇m ∘1 Δm} {β = ∇m ∘1 Δm} (∇m ∘1 Δm) 1⇒ D 

  ♭'L : {A B : Tp c} → A [ ∇m ∘1 Δm ]⊢ B → ♭' A [ 1m ]⊢ B
  ♭'L D = FL {α = ∇m ∘1 Δm} {β = 1m} D

  eta♯' : ∀ {A} → ♯' A [ 1m ]⊢ ♯' A
  eta♯' = ♯'R (♯'L copy)

  -- A cohesive ⊢ C cohesive
  Coh⊢Coh : (A C : Tp c) -> Set
  Coh⊢Coh A C = A [ 1m ]⊢ C

  -- A crisp ⊢ C cohesive
  Crisp⊢Coh : (A C : Tp c) → Set
  Crisp⊢Coh A C = A [ ∇m ∘1 Δm ]⊢ C

  strengthen : ∀ {A C} → Coh⊢Coh A C → Crisp⊢Coh A C
  strengthen paste = cut copy paste

  -- Rules for ♯
    
  -- A crisp ⊢ C cohesive
  -- -------------------------
  -- A cohesive ⊢ ♯ C cohesive

  ♯'intro : {A C : Tp c } 
         → Crisp⊢Coh A C 
         → Coh⊢Coh A (♯' C)
  ♯'intro {A} {C} E = ♯'R E

  -- A crisp ⊢ ♯ C cohesive
  -- -------------------------
  -- A crisp ⊢ C cohesive

  ♯'elim : { A C : Tp c}
        → Crisp⊢Coh A (♯' C)
        → Crisp⊢Coh A C
  ♯'elim D = cut {α = ∇m ∘1 Δm} {β = ∇m ∘1 Δm} D (♯'L copy)

  ♯'reduction : ∀ {A C} (D : Crisp⊢Coh A C) 
              → ♯'elim (strengthen (♯'intro D)) ≈ D
  ♯'reduction D = ((((((eq (transport⊢1 _) ∘≈ eq (ap (λ x → transport⊢ x D) lemma)) ∘≈ transport⊢≈ _ (cut-ident-right D)) ∘≈ eq (! (transport⊢∘ (cut D hyp)))) ∘≈ !≈ (transport⊢≈ _ (transport⊢cut1 {e2 = ∇Δunit} D hyp))) ∘≈ transport⊢≈ _ (cut-ident-left _)) ∘≈ !≈ (transport⊢cut {e1 = ∇Δunit} {e2 = 1⇒} hyp (cut D (transport⊢ ∇Δunit hyp)))) ∘≈ !≈ (cut-assoc (transport⊢ ∇Δunit hyp) (♯'R D) (UL (∇m ∘1 Δm) 1⇒ (transport⊢ ∇Δunit hyp))) where
    lemma' : ((1⇒{_}{_}{∇m} ∘1cong (1⇒{_}{_}{Δm} ∘1cong ∇Δunit)) ·2 ((∇Δunit ∘1cong 1⇒{_}{_}{∇m}) ∘1cong 1⇒{_}{_}{Δm})) == 1⇒ {_}{_}{∇m ∘1 Δm}
    lemma' = (ap (λ x → (1⇒ {_} {_} {∇m} ∘1cong 1⇒) ·2 (x ∘1cong 1⇒ {_} {_} {Δm})) adjeq1) ∘ ap (λ x → (1⇒ {_} {_} {∇m} ∘1cong x) ·2 ((∇Δunit ∘1cong 1⇒ {_} {_} {∇m}) ∘1cong 1⇒ {_} {_} {Δm})) adjeq2

    lemma : (_·2_ {p = (∇m ∘1 Δm) ∘1 1m} {q = (∇m ∘1 Δm) ∘1 (∇m ∘1 Δm)} {r = (∇m ∘1 Δm) ∘1 (∇m ∘1 Δm)} ((1⇒{_}{_}{∇m} ∘1cong 1⇒{_}{_}{Δm}) ∘1cong ∇Δunit)  (∇Δunit ∘1cong (1⇒{_}{_}{∇m} ∘1cong 1⇒{_}{_}{Δm}))) == 1⇒ {_}{_}{∇m ∘1 Δm}
    lemma = lemma' ∘ ap2 _·2_ (∘1cong-assoc {e1 = 1⇒} {e2 = 1⇒} {e3 = ∇Δunit}) (! (∘1cong-assoc {e1 = ∇Δunit} {e2 = 1⇒} {e3 = 1⇒}))

  -- Δ ; Γ ⊢ M : ♯ A
  -- --------------------------
  -- Δ,Γ ; · ⊢ M [copy Γ] : ♯ A
  -- ---------------------------------
  -- Δ,Γ ; · ⊢ ♯elim (M [copy Γ]) : A
  -- ----------------------------------------
  -- Δ ; Γ ⊢ ♯intro (♯elim (M [copy Γ])) : ♯ A

  ♯'expansion : ∀ {A C} (D : Coh⊢Coh A (♯' C) )
              → ♯'intro (♯'elim (strengthen D)) ≈ D
  ♯'expansion {A}{C} D = !≈ (Uη _) ∘≈ UR≈ {α = ∇m ∘1 Δm} {β = 1m} ((((cut≈2 D lemma2 ∘≈ cut≈1 (cut-ident-left D) (UL (∇m ∘1 Δm) 1⇒ (transport⊢ ∇Δunit (ident C)))) ∘≈ eq (transport⊢1 _) ∘≈ eq (ap (λ x → transport⊢ x (cut (cut hyp D) (UL (∇m ∘1 Δm) 1⇒ (transport⊢ ∇Δunit (ident C))))) lemma1)) ∘≈ !≈ (transport⊢cut2 {e1 = ∇Δunit} (cut hyp D) (UL (∇m ∘1 Δm) 1⇒ (transport⊢ ∇Δunit (ident C))))) ∘≈ cut≈1 (!≈ (transport⊢cut2 {e1 = ∇Δunit} hyp D)) (UL (∇m ∘1 Δm) 1⇒ (transport⊢ ∇Δunit (ident C)))) 
   where
    lemma1' : ((∇Δunit ∘1cong 1⇒{_}{_}{∇m}) ∘1cong 1⇒{_}{_}{Δm}) == 1⇒
    lemma1' = ap (λ x → x ∘1cong 1⇒ {_} {_} {Δm}) adjeq1

    lemma1 : (∇Δunit ∘1cong (1⇒{_}{_}{∇m ∘1 Δm})) == 1⇒
    lemma1 = lemma1' ∘ ! (∘1cong-assoc {e1 = ∇Δunit} {e2 = 1⇒} {e3 = 1⇒})
   
    lemma2' : (1⇒{_}{_}{∇m} ∘1cong (1⇒ {_}{_}{Δm} ∘1cong ∇Δunit)) == 1⇒
    lemma2' = ap (λ x → 1⇒ {_} {_} {∇m} ∘1cong x) adjeq2

    lemma2 : (UL {α = ∇m ∘1 Δm} {β = (∇m ∘1 Δm) ∘1 (∇m ∘1 Δm)} (∇m ∘1 Δm) 1⇒ (transport⊢ ∇Δunit hyp)) ≈ (UL {α = ∇m ∘1 Δm} {β = (∇m ∘1 Δm) ∘1 (∇m ∘1 Δm)} 1m 1⇒ hyp)
    lemma2 = UL2 {α = ∇m ∘1 Δm} {β = ∇m ∘1 Δm} {γ = ∇m ∘1 Δm} {γ' = 1m} {e = 1⇒} {e' = 1⇒} {D = transport⊢ ∇Δunit hyp} {D' = hyp} ∇Δunit (lemma2' ∘ ∘1cong-assoc {e1 = 1⇒ {_} {_} {∇m}} {e2 = 1⇒ {_} {_} {Δm}} {e3 = ∇Δunit}) id 
