
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

  -- each of these three steps should be an equivalence, so the whole thing should be
  collapseΔ1 : ∀ {A} → ◯ Δm A [ 1m ]⊢ A
  collapseΔ1 = cut mergeUF (cut (Ffunc∘1 {α = ∇m} {β = Δm}) Ffunc11)

  collapseΔ1' : ∀ {A} → ◯ Δm A [ 1m ]⊢ A
  collapseΔ1' = cut mergeUF' (cut (Ffunc∘1 {α = ∇m} {β = Δm}) Ffunc11)

  collapseΔ2 : ∀ {A} → A [ 1m ]⊢ ◯ Δm A
  collapseΔ2 = cut (cut Ffunc12 (Ffunc∘2 {α = ∇m} {β = Δm})) mergeFU

  collapseΔ2-composite-1 : cut collapseΔ2 collapseΔ1 == ident P
  collapseΔ2-composite-1 = {!!}

  collapseΔ2-composite-2 : cut collapseΔ1 collapseΔ2 == ident (◯ Δm P)
  collapseΔ2-composite-2 = {!!}

  -- each of these three steps should be an equivalence, so the whole thing should be
  collapse∇1 : ∀ {A} → A [ 1m ]⊢ □ ∇m A
  collapse∇1 = cut (cut Ufunc12 (Ufunc∘2 {α = ∇m} {β = Δm})) mergeUF

  collapse∇2 : ∀ {A} → □ ∇m A [ 1m ]⊢ A
  collapse∇2 = (cut mergeFU (cut (Ufunc∘1 {α = ∇m} {β = Δm}) Ufunc11))

  -- ap of U on an equivalence, should be an equivalence
  ♯idempotent : ∀ {A} → ♯ A [ 1m ]⊢ ♯ (♯ A)
  ♯idempotent = Ufunc collapse∇1

  -- ap of F on an equivalence, should be an equivalence
  ♭idempotent : ∀ {A} → ♭ (♭ A) [ 1m ]⊢ ♭ A
  ♭idempotent = Ffunc collapseΔ1


  -- Δ (F Δm) and ∇ (U ∇m) are full and faithful but Γ (the other two) is not

  F∇Δcancel1 : ∀ {A} → F ∇m (F Δm A) [ 1m ]⊢ A
  F∇Δcancel1 = cut (Ffunc∘1 {α = ∇m} {β = Δm}) Ffunc11

  F∇Δcancel2 : ∀ {A} → A [ 1m ]⊢ F ∇m (F Δm A)
  F∇Δcancel2 = (cut Ffunc12 (Ffunc∘2 {α = ∇m} {β = Δm}))

  FΔ-fullandfaithful : ∀ {A B} → F Δm A [ 1m ]⊢ F Δm B -> A [ 1m ]⊢ B
  FΔ-fullandfaithful D = cut F∇Δcancel2 (cut (Ffunc {α = ∇m} D) F∇Δcancel1)

  FΔ-fullandfaithful-composite-1 : (D : P [ 1m ]⊢ Q) → FΔ-fullandfaithful (Ffunc D) == D
  FΔ-fullandfaithful-composite-1 D = (((cut-ident-right _ ∘ (transport⊢1 _ ∘ transport⊢1 _)) ∘
                                         cut-ident-left (transport⊢ 1⇒ (transport⊢ 1⇒ (cut D (hypq 1⇒))))) ∘ transport⊢1 _) ∘ transport⊢1 _

  -- FIXME: seems like this is an equivalence by abstract reasoning, but why can't we do it just in terms of the normal forms??
  -- is something wrong?
  FΔ-fullandfaithful-composite-2 : (D : F Δm P [ 1m ]⊢ F Δm Q) → (Ffunc (FΔ-fullandfaithful D)) == D 
  FΔ-fullandfaithful-composite-2 D = 
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

{-

  FIXME : ∀ {A B} → (D : A [ Δm ]⊢ F Δm B) → D == FR {α = Δm} {β = 1m ∘1 Δm} 1m 1⇒ ((cut {α = ∇m} {β = Δm} D (FL {α = Δm} {β = ∇m} hyp))) -- 1m is only endomorphism of s
  FIXME D = {! Ffunc {α = Δm} (Ffunc {α = ∇m} (FL {α = Δm} {β = 1m} D))!}

  FIXME' : ∀ {A B} → (D : U ∇m A [ ∇m ]⊢ B) → D == UL 1m 1⇒ ((cut (UR {α = ∇m} {β = Δm} hyp) D)) -- 1m is only endomorphism of s
  FIXME' = {! !}

    OLD proof using FIXME 

    Ffunc (FΔ-fullandfaithful D) =〈 ap (λ x → FL (FR 1m 1⇒ x)) ( ap (cut {α = ∇m} {β = Δm} (FR 1m 1⇒ (hypp 1⇒))) (transport⊢1 (cut {α = ∇m} {β = 1m} D (FL {α = Δm} {β = ∇m} (hypq 1⇒)))) ∘ transport⊢1 (cut (FR 1m 1⇒ (hypp 1⇒)) (transport⊢ 1⇒ (cut D (FL {α = Δm} {β = ∇m}  (hypq 1⇒)))))) 〉 -- 
    FL {α = Δm} {β = 1m} (FR 1m 1⇒ (cut (FR 1m 1⇒ (hypp 1⇒)) (cut D (FL {α = Δm} {β = ∇m} (hypq 1⇒))))) =〈 ap (λ x → FL (FR 1m 1⇒ x)) (cut-assoc (FR 1m 1⇒ (hypp 1⇒)) D (FL {α = Δm} {β = ∇m} (hypq 1⇒))) 〉 
    FL {α = Δm} {β = 1m} (FR 1m 1⇒ (cut D' (FL {α = Δm} {β = ∇m} (hypq 1⇒)))) =〈 ! (ap (FL {α = Δm} {β = 1m}) (FIXME D')) 〉 
    FL {α = Δm} {β = 1m} D' =〈 ! (Fη D) 〉 
    D ∎ where
      D' : P [ Δm ]⊢ F Δm Q
      D' = (cut (FR 1m 1⇒ (hypp 1⇒)) D)

-}

  U∇-fullandfaithful : ∀ {A B} → U ∇m A [ 1m ]⊢ U ∇m B -> A [ 1m ]⊢ B
  U∇-fullandfaithful D = cut collapse∇1 (cut (Ffunc {α = ∇m} D) collapse∇2)

  -- seems OK
  U∇-fullandfaithful-composite-1 : (D : P [ 1m ]⊢ Q) -> (U∇-fullandfaithful (Ufunc D)) == D
  U∇-fullandfaithful-composite-1 D = {!!}

  U∇-fullandfaithful-composite-2 : (D : U ∇m P [ 1m ]⊢ U ∇m Q) -> (Ufunc (U∇-fullandfaithful D)) == D
  U∇-fullandfaithful-composite-2 D = {!!}

  -- ----------------------------------------------------------------------
  -- ♭ (♯ A) is equivalent to A: above retraction is an equivalence for this theory

  postulate
    focus-order : ∀ {p q r s} {A B} {α : q ≥ p} {β : q ≥ r} {γ : s ≥ r} 
                    {δ : p ≥ r} {δ' : p ≥ s} (e : (α ∘1 δ) ⇒ β) (e' : (δ' ∘1 γ) ⇒ δ) (D : A [ δ' ]⊢ B) 
                 → FR (α ∘1 δ') ((1⇒ ∘1cong e') ·2 e) (UL δ' 1⇒ D) == UL δ e (FR δ' e' D)

  ♭absorbs♯-composite-2 : cut (♭absorbs♯2 {P}) (♭absorbs♯1 {P}) == hyp
  ♭absorbs♯-composite-2 = ap (λ x → FL (FR 1m 1⇒ (UR x)))
                        (UL2 {D = cut (UL 1m 1⇒ mergeFU) (UL 1m 1⇒ ◯unit)} {D' = ident (♯ P)} 
                             ∇Δunit
                             {!!}
                             (ap (UR {α = ∇m} {β = (∇m ∘1 1m) ∘1 (Δm ∘1 1m)}) (UL2 {D = _} {D' = ident (F ∇m P)} 1⇒ (! adjeq1) (ap (FL {α = ∇m} {β = 1m}) (FR2 {α = ∇m} {β = ∇m ∘1 1m} {γ = ∇m ∘1 Δm} {γ' = 1m} {e = 1⇒} {e' = 1⇒} {D = cut (hypp ((1⇒ ·2 ∇Δunit) ∘1cong 1⇒)) (ident P)} {D' = ident P} ∇Δunit adjeq1 id))) ∘ Uη _))

  ♭absorbs♯ : QEquiv (♭ P) (♭ (♯ P))
  ♭absorbs♯ = qequiv ♭absorbs♯1 ♭absorbs♯2 ♭absorbs♯-composite-1 ♭absorbs♯-composite-2

  ♯absorbs♭1' : ∀ {A} → ♯ A [ 1m ]⊢ ♯ (♭ A) 
  ♯absorbs♭1' = Ufunc (cut (cut mergeFU ◯unit) mergeUF')

  ♯absorbs♭2' : ∀ {A} → ♯ (♭ A) [ 1m ]⊢ ♯ A
  ♯absorbs♭2' = Ufunc (cut mergeFU (cut collapseΔ1 mergeUF)) 

  ♯absorbs♭-composite-1' : cut (♯absorbs♭1' {P}) (♯absorbs♭2' {P}) == hyp
  ♯absorbs♭-composite-1' = {!!} -- ap (λ x → UR {α = ∇m} {β = 1m} (UL 1m 1⇒ x)) (ap (FL { α = ∇m} {β = 1m}) (FR2 {D = cut (FR 1m 1⇒ hyp) (FL (hypp ∇Δunit))} {D' = ident P} ∇Δunit adjeq2 id) ∘ Fη (FR Δm Δ∇counit (FL (hypp ∇Δunit))))

  ♯absorbs♭-composite-2' : cut (♯absorbs♭2' {P}) (♯absorbs♭1' {P}) == ident (♯ (♭ P))
  ♯absorbs♭-composite-2' = ap UR {!!} -- (! (Uη _) ∘ {!!}) ∘ Uη _
    -- ap (UR {α = ∇m} {β = 1m ∘1 1m}) (ap (UL 1m 1⇒) (ap (FL {α = ∇m} {β = 1m}) (FR2 (∇Δunit ·2 (1⇒ ∘1cong 1⇒' (∘1-assoc {α = Δm} {∇m} {Δm}))) {!!} (ap (FL {α = Δm} {β = (1m ∘1 ∇m) ∘1 (Δm ∘1 ((1m ∘1 ∇m) ∘1 Δm))}) (ap2 (λ x y → FR 1m x y) {!!} (ap (UR {α = Δm} {β = 1m}) (UL2 ∇Δunit {!!} id))) ∘ Fη _)) ∘ Fη _) ∘ FIXME' _)

  -- FIXME: seems like this is an equivalence by abstract reasoning, but why can't we do it just in terms of the normal forms??

  ♯absorbs♭ : QEquiv (♯ P) (♯ (♭ P))
  ♯absorbs♭ = qequiv ♯absorbs♭1' ♯absorbs♭2' ♯absorbs♭-composite-1' ♯absorbs♭-composite-2'
    


