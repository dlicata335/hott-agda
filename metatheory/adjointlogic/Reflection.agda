
open import adjointlogic.Lib
open import adjointlogic.Rules
open import adjointlogic.Properties
open import adjointlogic.General
open import adjointlogic.TripleAdjunction 

module adjointlogic.Reflection where

  -- for some reason the rewrites only work if we define the theory in that file
  open adjointlogic.Rules.Reflection
    
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

  F∇Δcancel : ∀ {A} → QEquiv (F ∇m (F Δm A)) A
  F∇Δcancel = (Ffunc∘ {α = ∇m} {β = Δm}) ·qeq Ffunc1

  -- the monad for Δ and the comonad for ∇ are trivial

  collapseΔ : ∀ {A} → QEquiv (◯ Δm A) A
  collapseΔ = mergeUFqeq ·qeq F∇Δcancel 

  collapse∇ : ∀ {A} → QEquiv A (□ ∇m A)
  collapse∇ = !qeq Ufunc1 ·qeq (!qeq (Ufunc∘ {α = ∇m} {β = Δm}) ·qeq mergeUFqeq)

  -- ♯ and ♭ are idempotent

  ♯idempotent : ∀ {A} → QEquiv (♯ A) (♯ (♯ A))
  ♯idempotent = Ufunc-qeq {α = ∇m} collapse∇

  ♭idempotent : ∀ {A} → QEquiv (♭ (♭ A)) (♭ A)
  ♭idempotent = Ffunc-qeq collapseΔ 

  -- ♭ (♯ A) is equivalent to A: above retraction is an equivalence for this theory

  ♭absorbs♯-composite-2 : cut (♭absorbs♯2 {P}) (♭absorbs♯1 {P}) == hyp
  ♭absorbs♯-composite-2 = ap (λ x → FL (FR 1m 1⇒ (UR x)))
                        (UL2 {α = Δm} {β = 1m ∘1 Δm} {γ = (∇m ∘1 1m) ∘1 (Δm ∘1 1m)} {γ' = 1m} {e = 1⇒} {e' = 1⇒} {D = cut (UL 1m 1⇒ mergeFU) (UL 1m 1⇒ ◯unit)} {D' = ident (♯ P)} 
                             ∇Δunit
                             adjeq2
                             (ap (UR {α = ∇m} {β = (∇m ∘1 1m) ∘1 (Δm ∘1 1m)}) (UL2 {D = _} {D' = ident (F ∇m P)} 1⇒ (! adjeq1) (ap (FL {α = ∇m} {β = 1m}) (FR2 {α = ∇m} {β = ∇m ∘1 1m} {γ = ∇m ∘1 Δm} {γ' = 1m} {e = 1⇒} {e' = 1⇒} {D = cut (hypp ((1⇒ ·2 ∇Δunit) ∘1cong 1⇒)) (ident P)} {D' = ident P} ∇Δunit adjeq1 id))) ∘ Uη _))

  ♭absorbs♯ : QEquiv (♭ P) (♭ (♯ P))
  ♭absorbs♯ = qequiv ♭absorbs♯1 ♭absorbs♯2 ♭absorbs♯-composite-1 ♭absorbs♯-composite-2

  -- ♯ (♭ A) is equivalent to A: above retraction is an equivalence for this theory

  ♯absorbs♭ : ∀ {A} → QEquiv (♯ A) (♯ (♭ A))
  ♯absorbs♭ = Ufunc-qeq (!qeq mergeUFqeq ·qeq (!qeq collapseΔ ·qeq mergeUFqeq))

  -- maps are the same as for TripleAdjunction
  ♯absorbs♭-map1 : (QEquiv.f (♯absorbs♭ {P})) == ♯absorbs♭1
  ♯absorbs♭-map1 = ap (UR {α = ∇m} {β = 1m}) (ap (UL 1m 1⇒) (ap (FR {α = ∇m} Δm 1⇒) (ap2 (FR 1m) adjeq2 (! (Uη _)))))

  ♯absorbs♭-map2 : (QEquiv.g (♯absorbs♭ {P})) == ♯absorbs♭2
  ♯absorbs♭-map2 = 
    ap (UR {α = ∇m} {β = 1m})
       (ap (UL {α = ∇m} {β = ∇m ∘1 1m} 1m 1⇒)
           (ap (FL {α = ∇m} {β = 1m})
               (FR2 {α = ∇m} {β = 1m ∘1 ∇m} {γ = ∇m ∘1 Δm} {γ' = 1m} {e = 1⇒} {e' = 1⇒} ∇Δunit adjeq1 (ap (FL {α = Δm} {β = ∇m ∘1 Δm}) (ap (λ X → UL {α = Δm} {β = Δm ∘1 (∇m ∘1 Δm)} 1m X hyp) {! calc!})))
            ∘ Fη (QEquiv.g (!qeq mergeUFqeq ·qeq (!qeq collapseΔ ·qeq mergeUFqeq))))) where
    calc : (((1⇒ {_} {_} {Δm} ∘1cong ∇Δunit) ∘1cong 1⇒ {_} {_} {∇m}) ∘1cong 1⇒ {_} {_} {Δm}) == (1⇒ {_}{_}{Δm} ∘1cong ∇Δunit)
    calc = ! adjeq2 ∘ (ap (λ H → (H ∘1cong 1⇒ {_} {_} {∇m}) ∘1cong 1⇒ {_} {_} {Δm}) adjeq2)

  -- ----------------------------------------------------------------------
  -- Δ (F Δm) and ∇ (U ∇m) are full and faithful but Γ (the other two) is not

  F∇Δcancel1 : ∀ {A} → F ∇m (F Δm A) [ 1m ]⊢ A
  F∇Δcancel1 = QEquiv.f F∇Δcancel

  F∇Δcancel2 : ∀ {A} → A [ 1m ]⊢ F ∇m (F Δm A)
  F∇Δcancel2 = QEquiv.g F∇Δcancel

  FΔ-fullandfaithful : ∀ {A B} → F Δm A [ 1m ]⊢ F Δm B -> A [ 1m ]⊢ B
  FΔ-fullandfaithful D = cut F∇Δcancel2 (cut (Ffunc {α = ∇m} D) F∇Δcancel1)

  FΔ-fullandfaithful-composite-1 : (D : P [ 1m ]⊢ Q) → FΔ-fullandfaithful (Ffunc D) == D
  FΔ-fullandfaithful-composite-1 D = (((cut-ident-right _ ∘ (transport⊢1 _ ∘ transport⊢1 _)) ∘
                                         cut-ident-left (transport⊢ 1⇒ (transport⊢ 1⇒ (cut D (hypq 1⇒))))) ∘ transport⊢1 _) ∘ transport⊢1 _

  -- something like an equivalence

  FRhyp : ∀ {A} → A [ Δm ]⊢ F Δm A
  FRhyp {A} = FR {α = Δm} {β = Δm} {A = A} 1m 1⇒ hyp

  unFR : ∀ {A} → F Δm A [ ∇m ]⊢ A 
  unFR = FL {α = Δm} {β = ∇m} hyp

  FRhyp-composite-1 : ∀ {A} → cut (FRhyp{A}) unFR == hyp
  FRhyp-composite-1 = cut-ident-left hyp ∘ transport⊢1 _

  FRhyp-composite-2 : ∀ {A} → cut unFR (FRhyp{A}) == transport⊢ ∇Δunit hyp
  FRhyp-composite-2 = ap (FL {α = Δm} {β = ∇m ∘1 Δm}) (ap2 (FR 1m) (! adjeq2) ((cut-ident-left hyp ∘ transport⊢1 _) ∘ ap (cut (FR 1m 1⇒ hyp)) (cut-ident-right (FL {α = Δm} {β = ∇m} hyp)))) ∘ Fη _

  FΔ-fullandfaithful-composite-2 : (D : F Δm P [ 1m ]⊢ F Δm Q) → (Ffunc (FΔ-fullandfaithful D)) == D 
  FΔ-fullandfaithful-composite-2 D = 
    ! (Fη _) ∘ ap (FL {α = Δm} {β = 1m}) (fact4 (cut (FR 1m 1⇒ hyp) D) ∘ (fact3 ∘ ! (fact4 _))) where

    -- they're equal when postcomposed with unFR
    fact1 : cut (FR 1m 1⇒ (FΔ-fullandfaithful D)) unFR == cut (cut (FR 1m 1⇒ hyp) D) unFR
    fact1 = (((cut-assoc (FR 1m 1⇒ (hypp 1⇒)) D (FL {α = Δm} {β = ∇m} (hypq 1⇒)) ∘ ap (λ H → cut (FR 1m 1⇒ (hypp 1⇒)) H) (transport⊢1 (cut D (FL {α = Δm} {β = ∇m} (hypq 1⇒))))) ∘ transport⊢1 _) ∘ cut-ident-right (transport⊢ 1⇒ (cut (FR 1m 1⇒ (hypp 1⇒)) (transport⊢ 1⇒ (cut D (FL {α = Δm} {β = ∇m} (hypq 1⇒))))))) ∘ transport⊢1 _ 

    -- reassociate
    fact2 : cut (FR 1m 1⇒ (FΔ-fullandfaithful D)) (cut unFR FRhyp) == cut (cut (FR 1m 1⇒ hyp) D) (cut unFR FRhyp)
    fact2 = ! (cut-assoc (cut (FR 1m 1⇒ hyp) D) unFR FRhyp) ∘ (ap (λ x → cut x FRhyp) fact1 ∘ cut-assoc (FR 1m 1⇒ (FΔ-fullandfaithful D)) unFR FRhyp)

    -- cancel
    fact3 : cut (FR {α = Δm} 1m 1⇒ (FΔ-fullandfaithful D)) (transport⊢ ∇Δunit hyp) == cut (cut (FR 1m 1⇒ hyp) D) (transport⊢ ∇Δunit hyp)
    fact3 = ap (λ x → cut (cut (FR 1m 1⇒ hyp) D) x) FRhyp-composite-2 ∘ (fact2 ∘ ap (λ x → cut (FR {α = Δm} 1m 1⇒ (FΔ-fullandfaithful D)) x) (! FRhyp-composite-2))
   
    fact4 : (D : P [ Δm ]⊢ F Δm Q) → cut D (transport⊢ ∇Δunit hyp) == D
    fact4 D = ((cut-ident-right D ∘ transport⊢1 _) ∘ ap (λ x → transport⊢ x (cut D hyp)) adjeq2) ∘ ! (transport⊢cut1 {e2 = ∇Δunit} D hyp)

{-
    abstract proof
    _ =〈 {!!} 〉 
    cut (Ffunc {α = Δm} F∇Δcancel2) (cut (Ffunc {α = Δm} (Ffunc {α = ∇m} D)) (Ffunc {α = Δm} F∇Δcancel1)) =〈 ap (λ x → cut (Ffunc {α = Δm} F∇Δcancel2) (cut x (Ffunc {α = Δm} F∇Δcancel1))) (Ffunc-func∘ D) 〉 
    cut (Ffunc {α = Δm} F∇Δcancel2) (cut (cut Ffunc∘1 (cut (Ffunc {α = ∇m ∘1 Δm} D) Ffunc∘2)) (Ffunc {α = Δm} F∇Δcancel1)) =〈 {!!} 〉 
    cut (Ffunc {α = Δm} F∇Δcancel2) (cut Ffunc∘1 (cut (Ffunc {α = ∇m ∘1 Δm} D) (cut Ffunc∘2 (Ffunc {α = Δm} F∇Δcancel1)))) =〈 {!!} 〉 
    cut (Ffunc {α = Δm} F∇Δcancel2) (cut Ffunc∘1 (cut (Ffunc {α = ∇m ∘1 Δm} D) (cut Ffunc∘2 (cut (Ffunc {α = Δm} (Ffunc∘1 {α = ∇m} {β = Δm} { A = Q} )) (Ffunc {α = Δm} Ffunc11))))) =〈 {!!} 〉 
    cut (Ffunc {α = Δm} F∇Δcancel2) (cut Ffunc∘1 (cut (Ffunc {α = ∇m ∘1 Δm} D) (cut (F2 {A = F Δm Q} ∇Δunit) Ffunc11))) =〈 {!!} 〉 
    cut (Ffunc {α = Δm} F∇Δcancel2) (cut Ffunc∘1 (cut (cut (F2 {A = F Δm P} ∇Δunit) (Ffunc {α = 1m} D)) Ffunc11)) =〈 {!!} 〉 
    cut (Ffunc {α = Δm} F∇Δcancel2) (cut Ffunc∘1 (cut (cut (F2 {A = F Δm P} ∇Δunit) (cut Ffunc11 (cut D Ffunc12))) Ffunc11)) =〈 {!!} 〉 
    cut (cut (Ffunc {α = Δm} F∇Δcancel2) (cut (cut Ffunc∘1 (F2 {A = F Δm P} ∇Δunit)) Ffunc11)) (cut (cut D Ffunc12) Ffunc11) =〈 {!!} 〉 
    cut (cut (Ffunc {α = Δm} F∇Δcancel2) (cut (cut Ffunc∘1 (F2 {A = F Δm P} ∇Δunit)) Ffunc11)) D =〈 {!!} 〉 
    _ ∎ where

    hmmmm : (cut Ffunc∘2 (cut (Ffunc {α = Δm} (Ffunc∘1 {α = ∇m} {β = Δm} { A = Q } )) (Ffunc {α = Δm} Ffunc11))) == cut (F2 {A = F Δm Q} ∇Δunit) Ffunc11
    hmmmm = ap (FL {α = ∇m ∘1 Δm} {β = 1m ∘1 (1m ∘1 1m)}) (ap (FL {α = Δm} {β = (∇m ∘1 Δm) ∘1 (1m ∘1 (1m ∘1 1m))}) (ap (λ x → FR 1m x (hypq 1⇒)) (! adjeq2)) ∘ Fη _)
    
    hmm : (cut (Ffunc {α = Δm} F∇Δcancel2) (cut (cut Ffunc∘1 (F2 {A = F Δm P} ∇Δunit)) Ffunc11)) == hyp
    hmm = ap (λ x → (FL {α = Δm} {β = 1m ∘1 ((1m ∘1 1m) ∘1 1m)}) (FR 1m x (hypp 1⇒))) adjeq2
-}

  U∇-fullandfaithful : ∀ {A B} → U ∇m A [ 1m ]⊢ U ∇m B -> A [ 1m ]⊢ B
  U∇-fullandfaithful D = cut (QEquiv.f collapse∇) (cut (Ffunc {α = ∇m} D) (QEquiv.g collapse∇))

  U∇-fullandfaithful-composite-1 : (D : P [ 1m ]⊢ Q) -> (U∇-fullandfaithful (Ufunc D)) == D
  U∇-fullandfaithful-composite-1 D = (((cut-ident-right D ∘ cut-ident-left (cut D (hypq 1⇒))) ∘ transport⊢1 _) ∘ ap (λ H → transport⊢ H (cut (hypp 1⇒) (cut D (hypq 1⇒)))) (ap (λ x → 1⇒ {_} {_} {Δm} ∘1cong x) adjeq1)) ∘ transport⊢1 _

  unUL : ∀ {A} → A [ Δm ]⊢ U ∇m A 
  unUL = UR {α = ∇m} {β = Δm} hyp

  ULhyp : ∀ {A} → U ∇m A [ ∇m ]⊢ A
  ULhyp = UL 1m 1⇒ hyp

  unUL-ULhyp : ∀ {A} → cut (ULhyp {A}) unUL == transport⊢ ∇Δunit hyp
  unUL-ULhyp = ap (UR {α = ∇m} {β = ∇m ∘1 Δm}) (ap2 (UL 1m) (! adjeq1) (cut-ident-left hyp) ∘ cutUL {e = 1⇒} {D = hyp} hyp)

  U∇-fullandfaithful-composite-2 : (D : U ∇m P [ 1m ]⊢ U ∇m Q) -> (Ufunc (U∇-fullandfaithful D)) == D
  U∇-fullandfaithful-composite-2 D = ! (Uη _) ∘ ap (UR {α = ∇m} {β = 1m}) (((fact4 ∘ ap (λ H → UL 1m 1⇒ (cut {α = ∇m} {β = Δm} (UR {α = ∇m} {β = Δm} (hypp 1⇒)) (cut D H))) (ap2 (UL 1m) adjeq1 id)) ∘ ap (λ H → UL 1m 1⇒ (cut {α = ∇m} {β = Δm} (UR {α = ∇m} {β = Δm} (hypp 1⇒)) H)) (transport⊢1 (cut D (UL 1m (∇Δunit ∘1cong 1⇒) (hypq 1⇒))))) ∘ ap (UL 1m 1⇒) (transport⊢1 (cut (UR {α = ∇m} {β = Δm} (hypp 1⇒)) (transport⊢ 1⇒ (cut D (UL 1m (∇Δunit ∘1cong 1⇒) (hypq 1⇒))))))) where
     fact3 : cut unUL (UL 1m 1⇒ (cut (UR {α = ∇m} {β = Δm} (hypp 1⇒)) (cut D (UL 1m 1⇒ (hypq 1⇒))))) == cut unUL (cut D (UL 1m 1⇒ (hypq 1⇒)))
     fact3 = cut-ident-left _ ∘ transport⊢1 _

     fact2 : {D : U ∇m P [ ∇m ]⊢ Q} → cut (ULhyp {P}) (cut unUL D) == D
     fact2 {D} = (((cut-ident-left D ∘ (transport⊢1 (cut hyp D) ∘ ap (λ H → transport⊢ H (cut hyp D)) adjeq1)) ∘ ! (transport⊢cut2 {e1 = ∇Δunit} hyp D)) ∘ ap (λ H → cut H D) unUL-ULhyp) ∘ cut-assoc ULhyp unUL D

     fact4 : UL 1m 1⇒ (cut (UR {α = ∇m} {β = Δm} (hypp 1⇒)) (cut D (UL 1m 1⇒ (hypq 1⇒)))) == cut D (UL 1m 1⇒ (hypq 1⇒))
     fact4 = fact2 ∘ (ap (cut ULhyp) fact3 ∘ ! fact2)


  -- Mike's Pfenning-Davies style rules

  -- A true ⊢ C true
  True⊢True : (A C : Tp c) -> Set
  True⊢True A C = A [ 1m ]⊢ C

  -- A valid ⊢ C true
  Valid⊢True : (A C : Tp c) → Set
  Valid⊢True A C = U Δm A [ Δm ]⊢ C

  -- A valid ⊢ C valid  
  Valid⊢Valid : (A C : Tp c) → Set
  Valid⊢Valid A C = U Δm A [ 1m ]⊢ U Δm C

  -- Rules for ♯
    
  -- can promote true to valid when proving ♯ C
  -- A valid ⊢ C valid
  -- ----------------
  -- A true  ⊢ ♯ C

  ♯intro : {A C : Tp c } 
         → Valid⊢Valid A C 
         → True⊢True A (♯ C)
  ♯intro {A} {C} E = cut {β = 1m} (cut (cut {α = 1m} {β = 1m} Ufunc12 (U2 ∇Δunit)) (Ufunc∘2 {α = Δm} {∇m})) (cut {α = 1m} (Ufunc {α = ∇m} E) (Ufunc mergeUF))

  coerce1 : ∀ {A C} → True⊢True A C → Valid⊢True A C
  coerce1 D = cut (UL 1m 1⇒ hyp) D

  coerce2 : ∀ {A C} → Valid⊢True A C → Valid⊢Valid A C
  coerce2 D = UR {α = Δm} {β = 1m} D

  ♯elim : { A C : Tp c}
        → Valid⊢Valid A (♯ C)
        → Valid⊢Valid A C
  ♯elim D = cut D (cut (Ufunc∘1 {α = ∇m} {β = Δm}) (cut Ufunc11 mergeFU))

  ♯reduction : (D : Valid⊢Valid P Q) → ♯elim (coerce2 (coerce1 (♯intro D))) == D
  ♯reduction = {!!}

  ♯expansion : (D : Valid⊢Valid P (♯ Q)) → coerce2 (coerce1 (♯intro (♯elim D))) == D
  ♯expansion D = {!mergeFU!}


  ♯' : Tp c -> Tp c
  ♯' A = U (∇m ∘1 Δm) A

  ♯'eqv : ∀ {A} → QEquiv (♯ A) (♯' A)
  ♯'eqv = Ufunc-qeq (!qeq mergeUFqeq) ·qeq Ufunc∘

  ♯'R : { A B : Tp c} → A [ ∇m ∘1 Δm ]⊢ B → A [ 1m ]⊢ ♯' B 
  ♯'R D = UR {α = ∇m ∘1 Δm} {β = 1m} D

  -- c ≥ c has two maps, 1m and ∇m ∘m Δm, with 1m ⇒ ∇m ∘m Δm, so 
  -- ∇m ∘m Δm gives the most freedom for D
  ♯'L : { A B : Tp c} → A [ ∇m ∘1 Δm ]⊢ B → ♯' A [ (∇m ∘1 Δm) ]⊢ B
  ♯'L {A}{B} D = UL (∇m ∘1 Δm) 1⇒ D 

  eta♯' : ∀ {A} → ♯' A [ 1m ]⊢ ♯' A
  eta♯' = ♯'R (♯'L (transport⊢ ∇Δunit hyp))

  test : ∀ {A} → eta♯' {A} == hyp
  test = ap UR (UL2 ∇Δunit {!!} id)

{-
  rule1' : {A C : Tp c } 
         → Valid⊢True A C
         → Valid⊢Lax A C 
  rule1' D = {!!} -- FR Δm 1⇒ D

  -- rule 2:
  -- A valid ⊢ C lax
  -- ----------------
  -- A true ⊢ C lax

  rule2 : ∀ {A C} 
         → Valid⊢Lax A C
         → True⊢Lax A C 
  rule2 D = {!!} -- transport⊢ (!·1-unit-l ·2 (∇Δunit ·1cong 1⇒ {_} {_} {∇m})) (cut (UR (transport⊢ Δ∇counit hyp)) D)

  rule2' : ∀ {A C} 
         → True⊢Lax A C
         → Valid⊢Lax A C
  rule2' D = UL ∇m 1⇒ D
-}
