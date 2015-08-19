
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

  F∇Δcancel : ∀ {A} → Iso (F ∇m (F Δm A)) A
  F∇Δcancel = (Ffunc∘ {α = ∇m} {β = Δm}) ·i Ffunc1

  -- the monad for Δ and the comonad for ∇ are trivial

  collapseΔ : ∀ {A} → Iso (◯ Δm A) A
  collapseΔ = mergeUFi ·i F∇Δcancel 

  collapse∇ : ∀ {A} → Iso A (□ ∇m A)
  collapse∇ = !i Ufunc1 ·i (!i (Ufunc∘ {α = ∇m} {β = Δm}) ·i mergeUFi)

  -- ♯ and ♭ are idempotent

  ♯idempotent : ∀ {A} → Iso (♯ A) (♯ (♯ A))
  ♯idempotent = Ufunc-i {α = ∇m} collapse∇

  ♭idempotent : ∀ {A} → Iso (♭ (♭ A)) (♭ A)
  ♭idempotent = Ffunc-i collapseΔ 

  -- ♭ (♯ A) is equivalent to A: above retraction is an equivalence for this theory

  ♭absorbs♯-composite-2 : cut (♭absorbs♯2 {P}) (♭absorbs♯1 {P}) ≈ hyp
  ♭absorbs♯-composite-2 = FL≈ (FR≈ {γ = 1m}{e = 1⇒} (UR≈ {α = Δm} {β = 1m} (UL2 {α = Δm} {β = 1m ∘1 Δm} {γ = (∇m ∘1 1m) ∘1 (Δm ∘1 1m)} {γ' = 1m} {e = 1⇒} {e' = 1⇒} {D = cut (UL 1m 1⇒ mergeFU) (UL 1m 1⇒ ◯unit)} {D' = ident (♯ P)} ∇Δunit adjeq2 (UR≈ {α = ∇m} {β = (∇m ∘1 1m) ∘1 (Δm ∘1 1m)} (UL2 {D = _} {D' = ident (F ∇m P)} 1⇒ (! adjeq1) (FL≈ {α = ∇m} {β = 1m} (FR2 {α = ∇m} {β = ∇m ∘1 1m} {γ = ∇m ∘1 Δm} {γ' = 1m} {e = 1⇒} {e' = 1⇒} {D = cut (hypp ((1⇒ ·2 ∇Δunit) ∘1cong 1⇒)) (ident P)} {D' = ident P} ∇Δunit adjeq1 id))) ∘≈ Uη _))))

  ♭absorbs♯ : Iso (♭ P) (♭ (♯ P))
  ♭absorbs♯ = iso ♭absorbs♯1 ♭absorbs♯2 ♭absorbs♯-composite-1 ♭absorbs♯-composite-2

  -- ♯ (♭ A) is equivalent to A: above retraction is an equivalence for this theory

  ♯absorbs♭ : ∀ {A} → Iso (♯ A) (♯ (♭ A))
  ♯absorbs♭ = Ufunc-i (!i mergeUFi ·i (!i collapseΔ ·i mergeUFi))

  -- maps are the same as for TripleAdjunction
  ♯absorbs♭-map1 : (Iso.f (♯absorbs♭ {P})) ≈ ♯absorbs♭1
  ♯absorbs♭-map1 = UR≈ {α = ∇m} {β = 1m} (UL≈ {γ = 1m} {e = 1⇒} (FR≈ {α = ∇m} {γ = Δm} {e = 1⇒} (FR≈' {γ = 1m} adjeq2 (!≈ (Uη _)))))

  ♯absorbs♭-map2 : (Iso.g (♯absorbs♭ {P})) ≈ ♯absorbs♭2
  ♯absorbs♭-map2 = UR≈ {α = ∇m} {β = 1m} (UL≈ {α = ∇m} {β = ∇m ∘1 1m} {γ = 1m} {e = 1⇒} (FL≈ {α = ∇m} {β = 1m} (FR2 {α = ∇m} {β = 1m ∘1 ∇m} {γ = ∇m ∘1 Δm} {γ' = 1m} {e = 1⇒} {e' = 1⇒} {D = _} {D' = □counit} ∇Δunit adjeq1 (FL≈ {α = Δm} {β = ∇m ∘1 Δm} (eq (ap (λ X → UL {α = Δm} {β = Δm ∘1 (∇m ∘1 Δm)} 1m X hyp) calc)))) ∘≈ Fη (Iso.g (!i mergeUFi ·i (!i collapseΔ ·i mergeUFi)))))
        where
    calc : (((1⇒ {_} {_} {Δm} ∘1cong ∇Δunit) ∘1cong 1⇒ {_} {_} {∇m}) ∘1cong 1⇒ {_} {_} {Δm}) == (1⇒ {_}{_}{Δm} ∘1cong ∇Δunit)
    calc = ! adjeq2 ∘ (ap (λ H → (H ∘1cong 1⇒ {_} {_} {∇m}) ∘1cong 1⇒ {_} {_} {Δm}) adjeq2)

  -- ----------------------------------------------------------------------
  -- Δ (F Δm) and ∇ (U ∇m) are full and faithful but Γ (the other two) is not

  F∇Δcancel1 : ∀ {A} → F ∇m (F Δm A) [ 1m ]⊢ A
  F∇Δcancel1 = Iso.f F∇Δcancel

  F∇Δcancel2 : ∀ {A} → A [ 1m ]⊢ F ∇m (F Δm A)
  F∇Δcancel2 = Iso.g F∇Δcancel

  FΔ-fullandfaithful : ∀ {A B} → F Δm A [ 1m ]⊢ F Δm B -> A [ 1m ]⊢ B
  FΔ-fullandfaithful D = cut F∇Δcancel2 (cut (Ffunc {α = ∇m} D) F∇Δcancel1)

  FΔ-fullandfaithful-composite-1 : (D : P [ 1m ]⊢ Q) → FΔ-fullandfaithful (Ffunc D) ≈ D
  FΔ-fullandfaithful-composite-1 D = (((cut-ident-right _ ∘≈ (eq (transport⊢1 _) ∘≈ eq (transport⊢1 _))) ∘≈ cut-ident-left (transport⊢ 1⇒ (transport⊢ 1⇒ (cut D (hypq 1⇒))))) ∘≈ eq (transport⊢1 _)) ∘≈ eq (transport⊢1 _)

  -- something like an equivalence

  FRhyp : ∀ {A} → A [ Δm ]⊢ F Δm A
  FRhyp {A} = FR {α = Δm} {β = Δm} {A = A} 1m 1⇒ hyp

  unFR : ∀ {A} → F Δm A [ ∇m ]⊢ A 
  unFR = FL {α = Δm} {β = ∇m} hyp

  FRhyp-composite-1 : ∀ {A} → cut (FRhyp{A}) unFR ≈ hyp
  FRhyp-composite-1 = cut-ident-left hyp ∘≈ eq (transport⊢1 _)

  FRhyp-composite-2 : ∀ {A} → cut unFR (FRhyp{A}) ≈ transport⊢ ∇Δunit hyp
  FRhyp-composite-2 = FL≈ {α = Δm} {β = ∇m ∘1 Δm} (FR≈' {γ = 1m} {e1 = 1⇒} {e2 = (1⇒ ∘1cong ∇Δunit)} (! adjeq2) ((cut-ident-left hyp ∘≈ eq (transport⊢1 _)) ∘≈ (cut≈2 (FR 1m 1⇒ hyp) (cut-ident-right (FL {α = Δm} {β = ∇m} hyp))))) ∘≈ Fη _

  FΔ-fullandfaithful-composite-2 : (D : F Δm P [ 1m ]⊢ F Δm Q) → (Ffunc (FΔ-fullandfaithful D)) ≈ D 
  FΔ-fullandfaithful-composite-2 D = 
    !≈ (Fη _) ∘≈ FL≈ {α = Δm} {β = 1m} (fact4 (cut (FR 1m 1⇒ hyp) D) ∘≈ (fact3 ∘≈ !≈ (fact4 _))) where

    -- they're equal when postcomposed with unFR
    fact1 : cut (FR 1m 1⇒ (FΔ-fullandfaithful D)) unFR ≈ cut (cut (FR 1m 1⇒ hyp) D) unFR
    fact1 = (((cut-assoc (FR 1m 1⇒ (hypp 1⇒)) D (FL {α = Δm} {β = ∇m} (hypq 1⇒)) ∘≈  (cut≈2 (FR 1m 1⇒ (hypp 1⇒)) (eq (transport⊢1 (cut D (FL {α = Δm} {β = ∇m} (hypq 1⇒))))))) ∘≈ eq (transport⊢1 _)) ∘≈ cut-ident-right (transport⊢ 1⇒ (cut (FR 1m 1⇒ (hypp 1⇒)) (transport⊢ 1⇒ (cut D (FL {α = Δm} {β = ∇m} (hypq 1⇒))))))) ∘≈ eq (transport⊢1 _)

    -- reassociate
    fact2 : cut (FR 1m 1⇒ (FΔ-fullandfaithful D)) (cut unFR FRhyp) ≈ cut (cut (FR 1m 1⇒ hyp) D) (cut unFR FRhyp)
    fact2 = !≈ (cut-assoc (cut (FR 1m 1⇒ hyp) D) unFR FRhyp) ∘≈ (cut≈1 fact1 FRhyp ∘≈ cut-assoc (FR 1m 1⇒ (FΔ-fullandfaithful D)) unFR FRhyp)

    -- cancel
    fact3 : cut (FR {α = Δm} 1m 1⇒ (FΔ-fullandfaithful D)) (transport⊢ ∇Δunit hyp) ≈ cut (cut (FR 1m 1⇒ hyp) D) (transport⊢ ∇Δunit hyp)
    fact3 = (cut≈2 (cut (FR 1m 1⇒ hyp) D) FRhyp-composite-2) ∘≈ (fact2 ∘≈ (cut≈2 (FR {α = Δm} 1m 1⇒ (FΔ-fullandfaithful D)) (!≈ FRhyp-composite-2)))
   
    fact4 : (D : P [ Δm ]⊢ F Δm Q) → cut D (transport⊢ ∇Δunit hyp) ≈ D
    fact4 D = ((cut-ident-right D ∘≈ eq (transport⊢1 _)) ∘≈ eq (ap (λ x → transport⊢ x (cut D hyp)) adjeq2)) ∘≈ !≈ (transport⊢cut1 {e2 = ∇Δunit} D hyp)

  U∇-fullandfaithful : ∀ {A B} → U ∇m A [ 1m ]⊢ U ∇m B -> A [ 1m ]⊢ B
  U∇-fullandfaithful D = cut (Iso.f collapse∇) (cut (Ffunc {α = ∇m} D) (Iso.g collapse∇))

  U∇-fullandfaithful-composite-1 : (D : P [ 1m ]⊢ Q) -> (U∇-fullandfaithful (Ufunc D)) ≈ D
  U∇-fullandfaithful-composite-1 D = (((cut-ident-right D ∘≈ cut-ident-left (cut D (hypq 1⇒))) ∘≈ eq (transport⊢1 _)) ∘≈ eq (ap (λ H → transport⊢ H (cut (hypp 1⇒) (cut D (hypq 1⇒)))) (ap (λ x → 1⇒ {_} {_} {Δm} ∘1cong x) adjeq1))) ∘≈ eq (transport⊢1 _)

  unUL : ∀ {A} → A [ Δm ]⊢ U ∇m A 
  unUL = UR {α = ∇m} {β = Δm} hyp

  ULhyp : ∀ {A} → U ∇m A [ ∇m ]⊢ A
  ULhyp = UL 1m 1⇒ hyp

  unUL-ULhyp : ∀ {A} → cut (ULhyp {A}) unUL ≈ transport⊢ ∇Δunit hyp
  unUL-ULhyp = UR≈ {α = ∇m} {β = ∇m ∘1 Δm} (UL≈' {γ = 1m} (! adjeq1) (cut-ident-left hyp) ∘≈ cutUL {e = 1⇒} {D = hyp} hyp)

  U∇-fullandfaithful-composite-2 : (D : U ∇m P [ 1m ]⊢ U ∇m Q) -> (Ufunc (U∇-fullandfaithful D)) ≈ D
  U∇-fullandfaithful-composite-2 D = !≈ (Uη _) ∘≈ (UR≈ {α = ∇m} {β = 1m} (((fact4 ∘≈ eq (ap (λ H → UL 1m 1⇒ (cut {α = ∇m} {β = Δm} (UR {α = ∇m} {β = Δm} (hypp 1⇒)) (cut D H))) (ap2 (UL 1m) adjeq1 id))) ∘≈ eq (ap (λ H → UL 1m 1⇒ (cut {α = ∇m} {β = Δm} (UR {α = ∇m} {β = Δm} (hypp 1⇒)) H)) (transport⊢1 (cut D (UL 1m (∇Δunit ∘1cong 1⇒) (hypq 1⇒)))))) ∘≈ eq (ap (UL 1m 1⇒) (transport⊢1 (cut (UR {α = ∇m} {β = Δm} (hypp 1⇒)) (transport⊢ 1⇒ (cut D (UL 1m (∇Δunit ∘1cong 1⇒) (hypq 1⇒))))))))) where
     fact3 : cut unUL (UL 1m 1⇒ (cut (UR {α = ∇m} {β = Δm} (hypp 1⇒)) (cut D (UL 1m 1⇒ (hypq 1⇒))))) ≈ cut unUL (cut D (UL 1m 1⇒ (hypq 1⇒)))
     fact3 = cut-ident-left _ ∘≈ eq (transport⊢1 _)

     fact2 : {D : U ∇m P [ ∇m ]⊢ Q} → cut (ULhyp {P}) (cut unUL D) ≈ D
     fact2 {D} = (((cut-ident-left D ∘≈ (eq (transport⊢1 (cut hyp D) ∘ ap (λ H → transport⊢ H (cut hyp D)) adjeq1))) ∘≈ !≈ (transport⊢cut2 {e1 = ∇Δunit} hyp D)) ∘≈ (cut≈1 unUL-ULhyp D) ∘≈ cut-assoc ULhyp unUL D)

     fact4 : UL 1m 1⇒ (cut (UR {α = ∇m} {β = Δm} (hypp 1⇒)) (cut D (UL 1m 1⇒ (hypq 1⇒)))) ≈ cut D (UL 1m 1⇒ (hypq 1⇒))
     fact4 = fact2 ∘≈ (cut≈2 ULhyp fact3) ∘≈ !≈ fact2



  -- Mike's Pfenning-Davies style rules

  copy : {A : Tp c} → A [ ∇m ∘1 Δm ]⊢ A
  copy = (transport⊢ ∇Δunit hyp)

  ♯'R : { A B : Tp c} → A [ ∇m ∘1 Δm ]⊢ B → A [ 1m ]⊢ ♯' B 
  ♯'R D = UR {α = ∇m ∘1 Δm} {β = 1m} D

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
  ♯'reduction D = ((((((eq (transport⊢1 _) ∘≈ eq (ap (λ x → transport⊢ x D) {! !})) ∘≈ transport⊢≈ _ (cut-ident-right D)) ∘≈ eq (! (transport⊢∘ (cut D hyp)))) ∘≈ !≈ (transport⊢≈ _ (transport⊢cut1 {e2 = ∇Δunit} D hyp))) ∘≈ transport⊢≈ _ (cut-ident-left _)) ∘≈
                     !≈
                     (transport⊢cut {e1 = ∇Δunit} {e2 = 1⇒} hyp
                      (cut D (transport⊢ ∇Δunit hyp)))) ∘≈ !≈ (cut-assoc (transport⊢ ∇Δunit hyp) (♯'R D) (UL (∇m ∘1 Δm) 1⇒ (transport⊢ ∇Δunit hyp)))

  -- Δ ; Γ ⊢ M : ♯ A
  -- --------------------------
  -- Δ,Γ ; · ⊢ M [copy Γ] : ♯ A
  -- ---------------------------------
  -- Δ,Γ ; · ⊢ ♯elim (M [copy Γ]) : A
  -- ----------------------------------------
  -- Δ ; Γ ⊢ ♯intro (♯elim (M [copy Γ])) : ♯ A

  ♯'expansion : ∀ {A C} (D : Coh⊢Coh A (♯' C) )
              → ♯'intro (♯'elim (strengthen D)) ≈ D
  ♯'expansion {A}{C} D = {!!} -- !≈ (Uη _) ∘≈ (UR≈ {α = ∇m ∘1 Δm} {β = 1m} ((cut≈1 foo ? ∘≈ {!!}) ∘≈ !≈ (cut-assoc copy D (UL (∇m ∘1 Δm) 1⇒ copy)))) 
   where
    foo : (UL {A = C} {C = C} (∇m ∘1 Δm) 1⇒ (transport⊢ ∇Δunit hyp)) ≈ (UL 1m 1⇒ hyp)
    foo = UL2 ∇Δunit {!!} id
