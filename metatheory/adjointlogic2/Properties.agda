
open import adjointlogic2.Lib
open import adjointlogic2.Rules

module adjointlogic2.Properties where

  transport⊢1 : {p q : Mode} → {A : Tp q} → {α : q ≥ p} {B : Tp p} 
               (D : A [ α ]⊢ B)
             → transport⊢ (1⇒ {α = α}) D == D
  transport⊢1 (hypp x) = id
  transport⊢1 (hypq x) = id
  transport⊢1 (FL D) = ap FL (transport⊢1 D)
  transport⊢1 (FR γ x D) = id
  transport⊢1 (UL γ x D) = id
  transport⊢1 (UR D) = ap UR (transport⊢1 D)
  transport⊢1 (Inl D) = ap Inl (transport⊢1 D)
  transport⊢1 (Inr D) = ap Inr (transport⊢1 D)
  transport⊢1 (Case D D₁) = ap2 Case (transport⊢1 D) (transport⊢1 D₁)

  transport⊢∘ : {p q : Mode} → {A : Tp q} → {α β γ : q ≥ p} {e1 : α ⇒ β} {e2 : β ⇒ γ} {B : Tp p} 
               (D : A [ α ]⊢ B)
             → transport⊢ (e1 ·2 e2) D == transport⊢ e2 (transport⊢ e1 D)
  transport⊢∘ (hypp x) = id
  transport⊢∘ (hypq x) = id
  transport⊢∘ {e1 = e1} {e2 = e2} (FL D) = ap FL (transport⊢∘ {e1 = 1⇒ ∘1cong e1} {e2 = 1⇒ ∘1cong e2} D ∘ ap (λ x → transport⊢ x D) (interchange {e1 = 1⇒} {e2 = 1⇒} {f1 = e1} {f2 = e2}))
  transport⊢∘ (FR γ₁ x D) = id
  transport⊢∘ (UL γ₁ x D) = id
  transport⊢∘ {e1 = e1} {e2} (UR D) = ap UR (transport⊢∘ {e1 = e1 ∘1cong 1⇒} {e2 = e2 ∘1cong 1⇒} D ∘ ap (λ x → transport⊢ x D) (interchange {e1 = e1} {e2 = e2} {f1 = 1⇒} {f2 = 1⇒}))
  transport⊢∘ (Inl D) = ap Inl (transport⊢∘ D)
  transport⊢∘ (Inr D) = ap Inr (transport⊢∘ D)
  transport⊢∘ (Case D D₁) = ap2 Case (transport⊢∘ D) (transport⊢∘ D₁)

  -- these equations are not defintiional because cut matches on two args

  cutFR : ∀ {p q r} {α : q ≥ p} {β : r ≥ q} {A : Tp r} {B : Tp q} {q₁} {α' : q₁ ≥ p} {A₁ : Tp q₁} →
        {γ : q ≥ q₁} {e : (γ ∘1 α') ⇒ α} (D : A [ β ]⊢ B) {E : B [ γ ]⊢ A₁}
        → cut D (FR γ e E) == FR (β ∘1 γ) (1⇒ ∘1cong e) (cut D E)
  cutFR (hypp x) = id
  cutFR (hypq x) = id
  cutFR (FL D) = id
  cutFR (FR γ x D) = id
  cutFR (UL γ x D) = id
  cutFR (UR D) = id
  cutFR (Inl D) = id
  cutFR (Inr D) = id
  cutFR (Case D D₁) = id

  cutInl : ∀ {p q r} {α : q ≥ p} {β : r ≥ q} {A : Tp r} {B : Tp q} {A₁ : Tp p} →
         (D : A [ β ]⊢ B) {E : B [ α ]⊢ A₁} {B₁ : Tp p} → cut D (Inl {B = B₁} E) == Inl (cut D E)
  cutInl (hypp x) = id
  cutInl (hypq x) = id
  cutInl (FL D) = id
  cutInl (FR γ x D) = id
  cutInl (UL γ x D) = id
  cutInl (UR D) = id
  cutInl (Inl D) = id
  cutInl (Inr D) = id
  cutInl (Case D D₁) = id

  cutInr : ∀ {p q r} {α : q ≥ p} {β : r ≥ q} {A : Tp r} {B : Tp q} {A₁ : Tp p} {B₁ : Tp p} →
         (D : A [ β ]⊢ B) {E : B [ α ]⊢ B₁} → cut D (Inr {A = A₁} E) == Inr (cut D E)
  cutInr (hypp x) = id
  cutInr (hypq x) = id
  cutInr (FL D) = id
  cutInr (FR γ x D) = id
  cutInr (UL γ x D) = id
  cutInr (UR D) = id
  cutInr (Inl D) = id
  cutInr (Inr D) = id
  cutInr (Case D D₁) = id

  cutUR : ∀ {p q r} {α : q ≥ p} {β : r ≥ q} {A : Tp r} {B : Tp q}
          {q₁} {α1 : p ≥ q₁} {A₁ : Tp q₁} →
          (D : A [ β ]⊢ B) {E : B [ α ∘1 α1 ]⊢ A₁} → cut D (UR E) == UR {α = α1} {β = β ∘1 α} (cut D E)
  cutUR (hypp x) = id
  cutUR (hypq x) = id
  cutUR (FL D) = id
  cutUR (FR γ x D) = id
  cutUR (UL γ x D) = id
  cutUR (UR D) = id
  cutUR (Inl D) = id
  cutUR (Inr D) = id
  cutUR (Case D D₁) = id

  mutual
    transport⊢≈ : ∀ {p q} {α α' : p ≥ q} {A : Tp p} {B : Tp q} {D1 D2 : A [ α ]⊢ B}
                  (e : α ⇒ α') → D1 ≈ D2 
                → transport⊢ e D1 ≈ transport⊢ e D2
    transport⊢≈ e id = id
    transport⊢≈ e (q ∘≈ q₁) = transport⊢≈ e q ∘≈ transport⊢≈ e q₁
    transport⊢≈ e (!≈ q) = !≈ (transport⊢≈ e q)
    transport⊢≈ e (FL≈ q) = FL≈ (transport⊢≈ _ q)
    transport⊢≈ e (FR≈ q) = FR≈ q
    transport⊢≈ e (UL≈ q) = UL≈ q
    transport⊢≈ e (UR≈ q) = UR≈ (transport⊢≈ _ q)
    transport⊢≈ e (Inl≈ q) = Inl≈ (transport⊢≈ _ q)
    transport⊢≈ e (Inr≈ q) = Inr≈ (transport⊢≈ _ q)
    transport⊢≈ e (Case≈ q q₁) = Case≈ (transport⊢≈ _ q) (transport⊢≈ _ q₁)
    transport⊢≈ e (Fη D1) = FL≈ (!≈ (transport⊢cut (FR 1m 1⇒ hyp) D1)) ∘≈ Fη _ 
    transport⊢≈ e (Uη D1) = UR≈ (!≈ (transport⊢cut D1 (UL 1m 1⇒ hyp))) ∘≈ Uη _
    transport⊢≈ e (⊕η D1) = Case≈ (!≈ (transport⊢cut1 {e2 = e} (Inl hyp) D1)) (!≈ (transport⊢cut1 {e2 = e} (Inr hyp) D1)) ∘≈ ⊕η _
    transport⊢≈ e (FR2 γ2 e2 q) = FR2 γ2 (ap (λ x → x ·2 e) e2) q
    transport⊢≈ e (UL2 γ2 e2 q) = UL2 γ2 (ap (λ x → x ·2 e) e2) q
    transport⊢≈ e (commuteULFR D p) = commuteULFR D (ap (λ x → x ·2 e) p)
    transport⊢≈ e (commuteULInl D) = commuteULInl _
    transport⊢≈ e (commuteULInr D) = commuteULInr _

    -- FIXME: needs to be mutual with ap (transport⊢ e) - preserving ≈ 
    transport⊢cut : ∀ {p q r} {α α' : q ≥ p} {β β' : r ≥ q} {A : Tp r} {B : Tp q} {C : Tp p}
        {e1 : β ⇒ β'} {e2 : α ⇒ α'} (D : A [ β ]⊢ B) (E : B [ α ]⊢ C)
        → transport⊢ (e1 ∘1cong e2) (cut D E) ≈ cut (transport⊢ e1 D) (transport⊢ e2 E)
    -- E is hyp
    transport⊢cut {e1 = e1} {e2 = e2} (hypp x) (hypp x₁) = eq (ap hypp (! (interchange {e1 = x} {e2 = e1} {f1 = x₁} {f2 = e2})))
    transport⊢cut {e1 = e1} {e2 = e2} (FL D) (hypp x) = FL≈ (transport⊢cut {e1 = 1⇒ ∘1cong e1} {e2 = e2} D (hypp x))
    transport⊢cut {e1 = e1} {e2 = e2} (UL γ x D) (hypp x₁) = 
      !≈ (UL2 (1⇒ ∘1cong e2) (interchange {e1 = x} {e2 = e1} {f1 = 1⇒} {f2 = e2} ∘ (! (interchange {e1 = 1⇒ ∘1cong 1⇒} {e2 = x ·2 e1} {f1 = e2} {f2 = 1⇒}) ∘ ap (λ H → H ·2 ((x ·2 e1) ∘1cong 1⇒)) (! (∘1cong-assoc {e1 = 1⇒} {1⇒} {e2}))))
              (!≈ (transport⊢cut {e1 = 1⇒} {e2 = e2} D (hypp x₁)) ∘≈ eq (! (ap (λ x₂ → cut x₂ (hypp (x₁ ·2 e2))) (transport⊢1 D)))))
    transport⊢cut (Case D D₁) (hypp x) = Case≈ (transport⊢cut D (hypp x)) (transport⊢cut D₁ (hypp x))
    transport⊢cut {e1 = e1} {e2 = e2} (hypq x) (hypq x₁) = eq (ap hypq (! (interchange {e1 = x} {e2 = e1} {f1 = x₁} {f2 = e2})))
    transport⊢cut {e1 = e1} {e2 = e2} (FL D) (hypq x) = FL≈ (transport⊢cut {e1 = 1⇒ ∘1cong e1} {e2 = e2} D (hypq x))
    transport⊢cut {e1 = e1} {e2 = e2} (UL γ x D) (hypq x₁) = !≈ (UL2 (1⇒ ∘1cong e2) (interchange {e1 = x} {e2 = e1} {f1 = 1⇒} {f2 = e2} ∘ (! (interchange {e1 = 1⇒ ∘1cong 1⇒} {e2 = x ·2 e1} {f1 = e2} {f2 = 1⇒}) ∘ ap (λ H → H ·2 ((x ·2 e1) ∘1cong 1⇒)) (! (∘1cong-assoc {e1 = 1⇒} {1⇒} {e2})))) 
      (!≈ (transport⊢cut {e1 = 1⇒} {e2 = e2} D (hypq x₁)) ∘≈ eq (! (ap (λ x₂ → cut x₂ (hypq (x₁ ·2 e2))) (transport⊢1 D)))))
    transport⊢cut (Case D D₁) (hypq x) = Case≈ (transport⊢cut D (hypq x)) (transport⊢cut D₁ (hypq x))
    -- E is FL
    transport⊢cut {e1 = e1} {e2} (FL D) (FL E) = FL≈ (transport⊢cut {e1 = 1⇒ ∘1cong e1} {e2 = e2} D (FL E))
    transport⊢cut {e1 = e1} {e2} (FR γ x D) (FL E) = (transport⊢≈ ((x ·2 e1) ∘1cong 1⇒) (transport⊢cut1 {e2 = 1⇒ ∘1cong e2} D E) ∘≈ (eq (transport⊢∘ (cut D E) ∘ ap (λ x₁ → transport⊢ x₁ (cut D E)) (! (interchange {e1 = x} {e2 = e1} {f1 = 1⇒} {f2 = e2} ∘ (! (interchange {e1 = 1⇒ ∘1cong 1⇒} {e2 = x ·2 e1} {f1 = e2} {f2 = 1⇒}) ∘ ap (λ H → H ·2 ((x ·2 e1) ∘1cong 1⇒)) (! (∘1cong-assoc {e1 = 1⇒} {1⇒} {e2})))))))) ∘≈ eq (! (transport⊢∘ (cut D E)))
    transport⊢cut {e1 = e1} {e2} (UL γ x D) (FL E) = !≈ (UL2 (1⇒ ∘1cong e2) (interchange {e1 = x} {e2 = e1} {f1 = 1⇒} {f2 = e2} ∘ (! (interchange {e1 = 1⇒ ∘1cong 1⇒} {e2 = x ·2 e1} {f1 = e2} {f2 = 1⇒}) ∘ ap (λ H → H ·2 ((x ·2 e1) ∘1cong 1⇒)) (! (∘1cong-assoc {e1 = 1⇒} {1⇒} {e2})))) (!≈ (transport⊢cut1 {e2 = e2} D (FL E))))
    transport⊢cut (Case D D₁) (FL E) = Case≈ (transport⊢cut D (FL E)) (transport⊢cut D₁ (FL E))
    -- E is UL
    transport⊢cut {e1 = e1} {e2} (FL D) (UL γ x E) = FL≈ (transport⊢cut {e1 = 1⇒ ∘1cong e1} {e2 = e2} D (UL γ x E))
    transport⊢cut {e1 = e1} {e2} (UL γ x D) (UL γ₁ x₁ E) = !≈ (UL2 (1⇒ ∘1cong e2) (interchange {e1 = x} {e2 = e1} {f1 = 1⇒} {f2 = e2} ∘ (! (interchange {e1 = 1⇒ ∘1cong 1⇒} {e2 = x ·2 e1} {f1 = e2} {f2 = 1⇒}) ∘ ap (λ H → H ·2 ((x ·2 e1) ∘1cong 1⇒)) (! (∘1cong-assoc {e1 = 1⇒} {1⇒} {e2})))) (!≈ (transport⊢cut1 {e2 = e2} D (UL γ₁ x₁ E))))
    transport⊢cut {e1 = e1} {e2 = e2} (UR D) (UL γ x E) = ((transport⊢≈ (1⇒ ∘1cong (x ·2 e2)) (transport⊢cut2 {e1 = e1 ∘1cong 1⇒} D E)) ∘≈ (eq (transport⊢∘ (cut D E) ∘ ap (λ x₁ → transport⊢ x₁ (cut D E)) (! (interchange {e1 = 1⇒} {e2 = e1} {f1 = x} {f2 = e2} ∘ ! (interchange {e1 = e1} {e2 = 1⇒} {f1 = 1⇒ ∘1cong 1⇒} {f2 = x ·2 e2})))))) ∘≈ (eq (! (transport⊢∘ (cut D E))))
    transport⊢cut (Case D D₁) (UL γ x E) = Case≈ (transport⊢cut D (UL γ x E)) (transport⊢cut D₁ (UL γ x E))
    -- E is case
    transport⊢cut {e1 = e1} {e2} (FL D) (Case E E₁) = FL≈ (transport⊢cut {e1 = 1⇒ ∘1cong e1} {e2} D (Case E E₁))
    transport⊢cut {e1 = e1} {e2} (UL γ x D) (Case E E₁) = !≈ (UL2 (1⇒ ∘1cong e2) (interchange {e1 = x} {e2 = e1} {f1 = 1⇒} {f2 = e2} ∘ (! (interchange {e1 = 1⇒ ∘1cong 1⇒} {e2 = x ·2 e1} {f1 = e2} {f2 = 1⇒}) ∘ ap (λ H → H ·2 ((x ·2 e1) ∘1cong 1⇒)) (! (∘1cong-assoc {e1 = 1⇒} {1⇒} {e2})))) (!≈ (transport⊢cut {e1 = 1⇒} {e2} D (Case E E₁)) ∘≈ eq (ap (λ x₁ → cut x₁ (Case (transport⊢ e2 E) (transport⊢ e2 E₁))) (! (transport⊢1 D)))))
    transport⊢cut (Case D D₁) (Case E E₁) = Case≈ (transport⊢cut D (Case E E₁)) (transport⊢cut D₁ (Case E E₁))
    transport⊢cut (Inl D) (Case E E₁) = transport⊢cut D E
    transport⊢cut (Inr D) (Case E E₁) = transport⊢cut D E₁
    -- E is a right rule
    transport⊢cut {e1 = e1} {e2} D (FR γ x E) = (eq (! (cutFR (transport⊢ e1 D))) ∘≈ !≈ (FR2 (e1 ∘1cong 1⇒) (interchange {e1 = 1⇒} {e2 = e1} {f1 = x} {f2 = e2} ∘ (! (interchange {e1 = e1} {e2 = 1⇒} {f1 = 1⇒ ∘1cong 1⇒} {f2 = x ·2 e2}))) (!≈ (transport⊢cut {e1 = e1} {e2 = 1⇒} D E) ∘≈ eq (ap (cut (transport⊢ e1 D)) (! (transport⊢1 E)))))) ∘≈ eq (ap (transport⊢ (e1 ∘1cong e2)) (cutFR D))
    transport⊢cut {α = α} {α'} {β} {β'} {e1 = e1} {e2} D (UR {α = α1} E) = (eq (! (cutUR (transport⊢ e1 D))) ∘≈ UR≈ {α = α1} {β' ∘1 α'} (transport⊢cut {α = α ∘1 α1} {α' ∘1 α1} {β} {β'} {e1 = e1} {e2 = e2 ∘1cong 1⇒} D E)) ∘≈ eq (ap (transport⊢ (e1 ∘1cong e2)) (cutUR D))
    transport⊢cut {α = α} {α'} {β} {β'} {e1 = e1} {e2} D (Inl E) = (eq (! (cutInl (transport⊢ e1 D))) ∘≈ Inl≈ (transport⊢cut {α = α} {α'} {β} {β'} {e1 = e1} {e2 = e2} D E)) ∘≈ eq (ap (transport⊢ (e1 ∘1cong e2)) (cutInl D))
    transport⊢cut {α = α} {α'} {β} {β'} {e1 = e1} {e2} D (Inr E) =  (eq (! (cutInr (transport⊢ e1 D))) ∘≈ Inr≈ (transport⊢cut {α = α} {α'} {β} {β'} {e1 = e1} {e2 = e2} D E)) ∘≈ eq (ap (transport⊢ (e1 ∘1cong e2)) (cutInr D))

    transport⊢cut1 : ∀ {p q r} {α α' : q ≥ p} {β : r ≥ q} {A : Tp r} {B : Tp q} {C : Tp p}
        {e2 : α ⇒ α'} (D : A [ β ]⊢ B) (E : B [ α ]⊢ C)
        → transport⊢ (1⇒ ∘1cong e2) (cut D E) ≈ cut D (transport⊢ e2 E)
    transport⊢cut1 {e2 = e2} D E = eq (ap (λ x → cut x (transport⊢ e2 E)) (transport⊢1 D)) ∘≈ transport⊢cut {e1 = 1⇒} {e2} D E

    transport⊢cut2 : ∀ {p q r} {α : q ≥ p} {β β' : r ≥ q} {A : Tp r} {B : Tp q} {C : Tp p}
        {e1 : β ⇒ β'} (D : A [ β ]⊢ B) (E : B [ α ]⊢ C)
        → transport⊢ (e1 ∘1cong 1⇒) (cut D E) ≈ cut (transport⊢ e1 D) E
    transport⊢cut2 {e1 = e1} D E = eq (ap (λ x → cut (transport⊢ e1 D) x) (transport⊢1 E)) ∘≈ transport⊢cut {e1 = e1} {1⇒} D E

  -- doesn't need ap cut on ≈ 
  cut-assoc : ∀ {p q r s} {α : p ≥ q} {β : q ≥ r} {γ : r ≥ s} {A : Tp p} {B : Tp q} {C : Tp r} {D : Tp s}
                (D1 : A [ α ]⊢ B) (D2 : B [ β ]⊢ C) (D3 : C [ γ ]⊢ D) →
                cut D1 (cut D2 D3) ≈ cut (cut D1 D2) D3
  cut-assoc = {!!}
{-
  -- D3 is a right rule
  cut-assoc {α = α} {β} D1 D2 (FR γ₁ x D3) = ((! (cutFR (cut D1 D2)) ∘ ap2 (FR (α ∘1 (β ∘1 γ₁))) (! (∘1cong-assoc {e1 = 1⇒} {1⇒} {x})) (cut-assoc D1 D2 D3)) ∘ cutFR D1) ∘ ap (cut D1) (cutFR D2)
  cut-assoc {α = α} {β} {γ} D1 D2 (UR {α = α₁} D3) =  ((! (cutUR (cut D1 D2)) ∘ ap (UR {α = α₁} {β = (α ∘1 β) ∘1 γ}) (cut-assoc D1 D2 D3)) ∘ cutUR D1) ∘ ap (cut D1) (cutUR D2) 
  cut-assoc D1 D2 (Inl D3) = ((! (cutInl (cut D1 D2)) ∘ ap Inl (cut-assoc D1 D2 D3)) ∘ cutInl D1) ∘ ap (cut D1) (cutInl D2) 
  cut-assoc D1 D2 (Inr D3) = ((! (cutInr (cut D1 D2)) ∘ ap Inr (cut-assoc D1 D2 D3)) ∘ cutInr D1) ∘ ap (cut D1) (cutInr D2)
  -- D1 is a right rule and D3 is a left rule; this cuts down on what D2 can be 
  -- ENH: there's a lot of copy and paste here, because the case-analysis is used to get the reductions going
  -- is there any way to avoid that?
  cut-assoc (Inl D1) (FR γ₁ x D2) (FL D3) = ap (transport⊢ (1⇒ ∘1cong (x ∘1cong 1⇒))) (cut-assoc (Inl D1) D2 D3) ∘ (! (transport⊢cut {e1 = 1⇒} {e2 = x ∘1cong 1⇒} (Inl D1) (cut D2 D3)) ∘ ! (ap (λ H → cut (Inl H) (transport⊢ (x ∘1cong 1⇒) (cut D2 D3))) (transport⊢1 D1)))
  cut-assoc (Inl D1) (Case D2 D3) (FL D4) = cut-assoc D1 D2 (FL D4)
  cut-assoc (Inl D1) (UR D2) (UL γ₁ x D3) = ap (transport⊢ _) (cut-assoc (Inl D1) D2 D3) ∘ (ap (λ H → transport⊢ H (cut (Inl D1) (cut D2 D3))) (! (∘1cong-assoc {e1 = 1⇒} {1⇒} {x})) ∘ (! (transport⊢cut {e1 = 1⇒} {e2 = 1⇒ ∘1cong x} (Inl D1) (cut D2 D3)) ∘ ap (λ H → cut (Inl H) (transport⊢ (1⇒ ∘1cong x) (cut D2 D3))) (! (transport⊢1 D1))))
  cut-assoc (Inl D1) (Case D2 D3) (UL γ₁ x D4) = cut-assoc D1 D2 (UL γ₁ x D4)
  cut-assoc (Inl D1) (Inl D2) (Case D3 D4) = cut-assoc (Inl D1) D2 D3
  cut-assoc (Inl D1) (Inr D2) (Case D3 D4) = cut-assoc (Inl D1) D2 D4
  cut-assoc (Inl D1) (Case D2 D3) (Case D4 D5) = cut-assoc D1 D2 (Case D4 D5)
  cut-assoc (Inr D1) (FR γ₁ x D2) (FL D3) = ap (transport⊢ (1⇒ ∘1cong (x ∘1cong 1⇒))) (cut-assoc (Inr D1) D2 D3) ∘ (! (transport⊢cut {e1 = 1⇒} {e2 = x ∘1cong 1⇒} (Inr D1) (cut D2 D3)) ∘ ap (λ H → cut (Inr H) (transport⊢ (x ∘1cong 1⇒) (cut D2 D3))) (! (transport⊢1 D1)))
  cut-assoc (Inr D1) (Case D2 D3) (FL D4) = cut-assoc D1 D3 (FL D4) 
  cut-assoc (Inr D1) (UR D2) (UL γ₁ x D3) = ap (transport⊢ _) (cut-assoc (Inr D1) D2 D3) ∘ (ap (λ H → transport⊢ H (cut (Inr D1) (cut D2 D3))) (! (∘1cong-assoc {e1 = 1⇒} {1⇒} {x})) ∘ (! (transport⊢cut {e1 = 1⇒} {e2 = 1⇒ ∘1cong x} (Inr D1) (cut D2 D3)) ∘ ap (λ H → cut (Inr H) (transport⊢ (1⇒ ∘1cong x) (cut D2 D3))) (! (transport⊢1 D1))))
  cut-assoc (Inr D1) (Case D2 D3) (UL γ₁ x D4) = cut-assoc D1 D3 (UL γ₁ x D4)
  cut-assoc (Inr D1) (Inl D2) (Case D3 D4) = cut-assoc (Inr D1) D2 D3
  cut-assoc (Inr D1) (Inr D2) (Case D3 D4) = cut-assoc (Inr D1) D2 D4
  cut-assoc (Inr D1) (Case D2 D3) (Case D4 D5) = cut-assoc D1 D3 (Case D4 D5)
  cut-assoc (UR D1) (FR γ₁ x D2) (FL D3) = ap (transport⊢ ((1⇒ ∘1cong x) ∘1cong 1⇒)) (cut-assoc (UR D1) D2 D3) ∘ ! (transport⊢cut1 {e2 = x ∘1cong 1⇒} (UR D1) (cut D2 D3))
  cut-assoc (UR D1) (UL γ₁ x D2) (FL D3) = transport⊢cut2 {e1 = 1⇒ ∘1cong x} (cut D1 D2) (FL D3) ∘ ap (transport⊢ ((1⇒ ∘1cong x) ∘1cong 1⇒)) (cut-assoc D1 D2 (FL D3))
  cut-assoc (UR D1) (UL γ₁ x D2) (UL γ₂ x₁ D3) = transport⊢cut2 {e1 = 1⇒ ∘1cong x} (cut D1 D2) (UL γ₂ x₁ D3) ∘ ap (transport⊢ ((1⇒ ∘1cong x) ∘1cong 1⇒)) (cut-assoc D1 D2 (UL γ₂ x₁ D3))
  cut-assoc (UR D1) (UR D2) (UL γ₁ x D3) = ap (transport⊢ ((1⇒ ∘1cong 1⇒) ∘1cong x)) (cut-assoc (UR D1) D2 D3) ∘ (ap (λ H → transport⊢ H (cut (UR D1) (cut D2 D3))) (! (∘1cong-assoc {e1 = 1⇒} {1⇒} {x})) ∘ ! (transport⊢cut1 {e2 = 1⇒ ∘1cong x} (UR D1) (cut D2 D3)))
  cut-assoc (UR D1) (UL γ₁ x D2) (Case D3 D4) = transport⊢cut2 {e1 = 1⇒ ∘1cong x} (cut D1 D2) (Case D3 D4) ∘ ap (transport⊢ ((1⇒ ∘1cong x) ∘1cong 1⇒)) (cut-assoc D1 D2 (Case D3 D4))
  cut-assoc (UR D1) (Inl D2) (Case D3 D4) = cut-assoc (UR D1) D2 D3
  cut-assoc (UR D1) (Inr D2) (Case D3 D4) = cut-assoc (UR D1) D2 D4
  cut-assoc (FR γ₁ e D1) (FL D2) (FL D3) = (transport⊢cut2 {e1 = e ∘1cong 1⇒} (cut D1 D2) (FL D3) ∘ ap (λ H → transport⊢ H (cut (cut D1 D2) (FL D3))) (! (∘1cong-assoc {e1 = e} {1⇒} {1⇒}))) ∘ ap (transport⊢ (e ∘1cong 1⇒)) (cut-assoc D1 D2 (FL D3))
  cut-assoc (FR γ₁ e D1) (FR γ₂ x D2) (FL D3) = ap (transport⊢ ((1⇒ ∘1cong x) ∘1cong 1⇒)) (cut-assoc (FR γ₁ e D1) D2 D3) ∘ (! (transport⊢cut1 {e2 = x ∘1cong 1⇒} (FR γ₁ e D1) (cut D2 D3)))
  cut-assoc (FR γ₁ e D1) (FL D2) (UL γ₂ x D3) = (transport⊢cut2 {e1 = e ∘1cong 1⇒} (cut D1 D2) (UL γ₂ x D3) ∘ ap (λ H → transport⊢ H (cut (cut D1 D2) (UL γ₂ x D3))) (! (∘1cong-assoc {e1 = e} {1⇒} {1⇒}))) ∘ ap (transport⊢ (e ∘1cong 1⇒)) (cut-assoc D1 D2 (UL γ₂ x D3))
  cut-assoc (FR γ₁ e D1) (UR D2) (UL γ₂ x D3) = (ap (transport⊢ ((1⇒ ∘1cong 1⇒) ∘1cong x)) (cut-assoc (FR γ₁ e D1) D2 D3) ∘ ap (λ H → transport⊢ H (cut (FR γ₁ e D1) (cut D2 D3))) (! (∘1cong-assoc {e1 = 1⇒} {1⇒} {x}))) ∘ ! (transport⊢cut1 {e2 = 1⇒ ∘1cong x} (FR γ₁ e D1) (cut D2 D3))
  cut-assoc (FR γ₁ e D1) (FL D2) (Case D3 D4) = (transport⊢cut2 {e1 = e ∘1cong 1⇒} (cut D1 D2) (Case D3 D4) ∘ ap (λ H → transport⊢ H (cut (cut D1 D2) (Case D3 D4))) (! (∘1cong-assoc {e1 = e} {1⇒} {1⇒}))) ∘ ap (transport⊢ (e ∘1cong 1⇒)) (cut-assoc D1 D2 (Case D3 D4))
  cut-assoc (FR γ₁ e D1) (Inl D2) (Case D3 D4) = cut-assoc (FR γ₁ e D1) D2 D3
  cut-assoc (FR γ₁ e D1) (Inr D2) (Case D3 D4) = cut-assoc (FR γ₁ e D1) D2 D4
  -- D1 is a left rule and D3 is a left rule
  --    D1 is FL
  cut-assoc (FL D1) (FL D2) (FL D3) = ap FL (cut-assoc D1 (FL D2) (FL D3))
  cut-assoc {α = α} {β = β} (FL {α = α1} D1) (FR γ₁ x D2) (FL {α = α2} D3) = ap (transport⊢ (1⇒ ∘1cong (x ∘1cong 1⇒))) (cut-assoc (FL D1) D2 D3) ∘ (! (transport⊢cut1 (FL D1) (cut D2 D3)))
  cut-assoc (FL D1) (UL γ₁ x D2) (FL D3) = ap FL (cut-assoc D1 (UL γ₁ x D2) (FL D3))
  cut-assoc (FL D1) (Case D2 D3) (FL D4) = ap FL (cut-assoc D1 (Case D2 D3) (FL D4))
  cut-assoc (FL D1) (FL D2) (UL γ₁ x D3) = ap FL (cut-assoc D1 (FL D2) (UL γ₁ x D3))
  cut-assoc (FL D1) (UL γ₁ x D2) (UL γ₂ x₁ D3) = ap FL (cut-assoc D1 (UL γ₁ x D2) (UL γ₂ x₁ D3))
  cut-assoc (FL D1) (UR D2) (UL γ₁ x D3) = (ap (transport⊢ ((1⇒ ∘1cong 1⇒) ∘1cong x)) (cut-assoc (FL D1) D2 D3) ∘ ap (λ H → transport⊢ H (cut (FL D1) (cut D2 D3))) (! (∘1cong-assoc {e1 = 1⇒} {1⇒} {x}))) ∘ ! (transport⊢cut1 {e2 = 1⇒ ∘1cong x} (FL D1) (cut D2 D3))
  cut-assoc (FL D1) (Case D2 D3) (UL γ₁ x D4) = ap FL (cut-assoc D1 (Case D2 D3) (UL γ₁ x D4))
  cut-assoc (FL D1) (FL D2) (Case D3 D4) = ap FL (cut-assoc D1 (FL D2) (Case D3 D4))
  cut-assoc (FL D1) (UL γ₁ x D2) (Case D3 D4) = ap FL (cut-assoc D1 (UL γ₁ x D2) (Case D3 D4))
  cut-assoc (FL D1) (Inl D2) (Case D3 D4) = cut-assoc (FL D1) D2 D3
  cut-assoc (FL D1) (Inr D2) (Case D3 D4) = cut-assoc (FL D1) D2 D4
  cut-assoc (FL D1) (Case D2 D3) (Case D4 D5) = ap FL (cut-assoc D1 (Case D2 D3) (Case D4 D5)) 
  --    D1 is Case
  cut-assoc (Case D1 D1') (FL D2) (FL D3) = ap2 Case (cut-assoc D1 (FL D2) (FL D3)) (cut-assoc D1' (FL D2) (FL D3))
  cut-assoc (Case D1 D1') (FL D2) (UL γ₁ x D3) = ap2 Case (cut-assoc D1 (FL D2) (UL γ₁ x D3)) (cut-assoc D1' (FL D2) (UL γ₁ x D3))
  cut-assoc (Case D1 D1') (FL D2) (Case D3 D4) = ap2 Case (cut-assoc D1 (FL D2) (Case D3 D4)) (cut-assoc D1' (FL D2) (Case D3 D4))
  cut-assoc (Case D1 D1') (FR γ₁ x D2) (FL D3) = ap (transport⊢ (1⇒ ∘1cong (x ∘1cong 1⇒))) (cut-assoc (Case D1 D1') D2 D3) ∘ (! (transport⊢cut1 (Case D1 D1') (cut D2 D3)))
  cut-assoc (Case D1 D1') (UL γ₁ x D2) (FL D3) = ap2 Case (cut-assoc D1 (UL γ₁ x D2) (FL D3)) (cut-assoc D1' (UL γ₁ x D2) (FL D3))
  cut-assoc (Case D1 D1') (UL γ₁ x D2) (UL γ₂ x₁ D3) = ap2 Case (cut-assoc D1 (UL γ₁ x D2) (UL γ₂ x₁ D3)) (cut-assoc D1' (UL γ₁ x D2) (UL γ₂ x₁ D3))
  cut-assoc (Case D1 D1') (UL γ₁ x D2) (Case D3 D4) = ap2 Case (cut-assoc D1 (UL γ₁ x D2) (Case D3 D4)) (cut-assoc D1' (UL γ₁ x D2) (Case D3 D4))
  cut-assoc (Case D1 D1') (UR D2) (UL γ₁ x D3) = (ap (transport⊢ ((1⇒ ∘1cong 1⇒) ∘1cong x)) (cut-assoc (Case D1 D1') D2 D3) ∘ ap (λ H → transport⊢ H (cut (Case D1 D1') (cut D2 D3))) (! (∘1cong-assoc {e1 = 1⇒} {1⇒} {x}))) ∘ ! (transport⊢cut1 {e2 = 1⇒ ∘1cong x} (Case D1 D1') (cut D2 D3))
  cut-assoc (Case D1 D1') (Inl D2) (Case D3 D4) = cut-assoc (Case D1 D1') D2 D3
  cut-assoc (Case D1 D1') (Inr D2) (Case D3 D4) = cut-assoc (Case D1 D1') D2 D4
  cut-assoc (Case D1 D1') (Case D2 D3) (FL D4) = ap2 Case (cut-assoc D1 (Case D2 D3) (FL D4)) (cut-assoc D1' (Case D2 D3) (FL D4))
  cut-assoc (Case D1 D1') (Case D2 D3) (UL γ₁ x D4) = ap2 Case (cut-assoc D1 (Case D2 D3) (UL γ₁ x D4)) (cut-assoc D1' (Case D2 D3) (UL γ₁ x D4))
  cut-assoc (Case D1 D1') (Case D2 D3) (Case D4 D5) = ap2 Case (cut-assoc D1 (Case D2 D3) (Case D4 D5)) (cut-assoc D1' (Case D2 D3) (Case D4 D5))
  --    D1 is UL
  cut-assoc {α = α} {β} {γ} (UL γ1 e D1) (FL D2) (FL D3) = ap2 (UL (γ1 ∘1 (β ∘1 γ))) (! (∘1cong-assoc {e1 = e} {1⇒} {1⇒})) (cut-assoc D1 (FL D2) (FL D3))
  cut-assoc {α = α} {β} {γ} (UL γ1 e D1) (FL D2) (UL γ₁ x D3) = ap2 (UL (γ1 ∘1 (β ∘1 γ))) (! (∘1cong-assoc {e1 = e} {1⇒} {1⇒})) (cut-assoc D1 (FL D2) (UL γ₁ x D3))
  cut-assoc {α = α} {β} {γ} (UL γ1 e D1) (FL D2) (Case D3 D4) = ap2 (UL (γ1 ∘1 (β ∘1 γ))) (! (∘1cong-assoc {e1 = e} {1⇒} {1⇒})) (cut-assoc D1 (FL D2) (Case D3 D4))
  cut-assoc {α = α} {β} {γ} (UL γ1 e D1) (FR γ₁ x D2) (FL D3) = ap (transport⊢ (1⇒ ∘1cong (x ∘1cong 1⇒))) (cut-assoc (UL γ1 e D1) D2 D3) ∘ (! (transport⊢cut1 (UL γ1 e D1) (cut D2 D3)))
  cut-assoc {α = α} {β} {γ} (UL γ1 e D1) (UL γ₁ x D2) (FL D3) = ap2 (UL (γ1 ∘1 (β ∘1 γ))) (! (∘1cong-assoc {e1 = e} {1⇒} {1⇒})) (cut-assoc D1 (UL γ₁ x D2) (FL D3))
  cut-assoc {α = α} {β} {γ} (UL γ1 e D1) (UL γ₁ x D2) (UL γ₂ x₁ D3) = ap2 (UL (γ1 ∘1 (β ∘1 γ))) (! (∘1cong-assoc {e1 = e} {1⇒} {1⇒})) (cut-assoc D1 (UL γ₁ x D2) (UL γ₂ x₁ D3))
  cut-assoc {α = α} {β} {γ} (UL γ1 e D1) (UL γ₁ x D2) (Case D3 D4) = ap2 (UL (γ1 ∘1 (β ∘1 γ))) (! (∘1cong-assoc {e1 = e} {1⇒} {1⇒})) (cut-assoc D1 (UL γ₁ x D2) (Case D3 D4))
  cut-assoc {α = α} {β} {γ} (UL γ1 e D1) (UR D2) (UL γ₁ x D3) = (ap (transport⊢ ((1⇒ ∘1cong 1⇒) ∘1cong x)) (cut-assoc (UL γ1 e D1) D2 D3) ∘ ap (λ H → transport⊢ H (cut (UL γ1 e D1) (cut D2 D3))) (! (∘1cong-assoc {e1 = 1⇒} {1⇒} {x}))) ∘ ! (transport⊢cut1 {e2 = 1⇒ ∘1cong x} (UL γ1 e D1) (cut D2 D3))
  cut-assoc {α = α} {β} {γ} (UL γ1 e D1) (Inl D2) (Case D3 D4) = cut-assoc (UL γ1 e D1) D2 D3
  cut-assoc {α = α} {β} {γ} (UL γ1 e D1) (Inr D2) (Case D3 D4) = cut-assoc (UL γ1 e D1) D2 D4
  cut-assoc {α = α} {β} {γ} (UL γ1 e D1) (Case D2 D3) (FL D4) = ap2 (UL (γ1 ∘1 (β ∘1 γ))) (! (∘1cong-assoc {e1 = e} {1⇒} {1⇒})) (cut-assoc D1 (Case D2 D3) (FL D4))
  cut-assoc {α = α} {β} {γ} (UL γ1 e D1) (Case D2 D3) (UL γ₁ x D4) = ap2 (UL (γ1 ∘1 (β ∘1 γ))) (! (∘1cong-assoc {e1 = e} {1⇒} {1⇒})) (cut-assoc D1 (Case D2 D3) (UL γ₁ x D4))
  cut-assoc {α = α} {β} {γ} (UL γ1 e D1) (Case D2 D3) (Case D4 D5) = ap2 (UL (γ1 ∘1 (β ∘1 γ))) (! (∘1cong-assoc {e1 = e} {1⇒} {1⇒})) (cut-assoc D1 (Case D2 D3) (Case D4 D5))
  -- D1 is an identity
  --   P
  cut-assoc (hypp e) (hypp x) (hypp x₁) = ap hypp (! (∘1cong-assoc {e1 = e} {x} {x₁}))
  cut-assoc (hypp e) (FR γ x D2) (FL D3) = ap (transport⊢ ((1⇒ ∘1cong x) ∘1cong 1⇒)) (cut-assoc (hypp e) D2 D3) ∘ (! (transport⊢cut1 {e2 = x ∘1cong 1⇒} (hypp e) (cut D2 D3)))
  cut-assoc (hypp e) (UR D2) (UL γ₁ x D3) = ap (transport⊢ ((1⇒ ∘1cong 1⇒) ∘1cong x)) (cut-assoc (hypp e) D2 D3) ∘ (ap (λ H → transport⊢ H (cut (hypp e) (cut D2 D3))) (! (∘1cong-assoc {e1 = 1⇒} {1⇒} {x})) ∘ ! (transport⊢cut1 {e2 = 1⇒ ∘1cong x} (hypp e) (cut D2 D3)))
  cut-assoc (hypp e) (Inl D2) (Case D3 D4) = cut-assoc (hypp e) D2 D3
  cut-assoc (hypp e) (Inr D2) (Case D3 D4) = cut-assoc (hypp e) D2 D4
  --   Q
  cut-assoc (hypq e) (hypq x) (hypq x₁) = ap hypq (! (∘1cong-assoc {e1 = e} {x} {x₁}))
  cut-assoc (hypq e) (FR γ x D2) (FL D3) = ap (transport⊢ ((1⇒ ∘1cong x) ∘1cong 1⇒)) (cut-assoc (hypq e) D2 D3) ∘ (! (transport⊢cut1 {e2 = x ∘1cong 1⇒} (hypq e) (cut D2 D3)))
  cut-assoc (hypq e) (UR D2) (UL γ₁ x D3) = ap (transport⊢ ((1⇒ ∘1cong 1⇒) ∘1cong x)) (cut-assoc (hypq e) D2 D3) ∘ (ap (λ H → transport⊢ H (cut (hypq e) (cut D2 D3))) (! (∘1cong-assoc {e1 = 1⇒} {1⇒} {x})) ∘ ! (transport⊢cut1 {e2 = 1⇒ ∘1cong x} (hypq e) (cut D2 D3)))
  cut-assoc (hypq e) (Inl D2) (Case D3 D4) = cut-assoc (hypq e) D2 D3
  cut-assoc (hypq e) (Inr D2) (Case D3 D4) = cut-assoc (hypq e) D2 D4
  -- D3 is an identity
  --   P
  cut-assoc (FL D1) (hypp x) (hypp e') = ap FL (cut-assoc D1 (hypp x) (hypp e'))
  cut-assoc (FL D1) (FL D2) (hypp e') = ap FL (cut-assoc D1 (FL D2) (hypp e'))
  cut-assoc (FL D1) (UL γ₁ x D2) (hypp e') = ap FL (cut-assoc D1 (UL γ₁ x D2) (hypp e'))
  cut-assoc (FL D1) (Case D2 D3) (hypp e') = ap FL (cut-assoc D1 (Case D2 D3) (hypp e'))
  cut-assoc (FR γ₁ x D1) (FL D2) (hypp e') = (transport⊢cut2 {e1 = x ∘1cong 1⇒} (cut D1 D2) (hypp e') ∘ ap (λ H → transport⊢ H (cut (cut D1 D2) (hypp e'))) (! (∘1cong-assoc {e1 = x} {1⇒} {1⇒}))) ∘ ap (transport⊢ (x ∘1cong 1⇒)) (cut-assoc D1 D2 (hypp e'))
  cut-assoc (UR D1) (UL γ₁ x D2) (hypp e') = (transport⊢cut2 {e1 = 1⇒ ∘1cong x} (cut D1 D2) (hypp e')) ∘ ap (transport⊢ (1⇒ ∘1cong (x ∘1cong 1⇒))) (cut-assoc D1 D2 (hypp e'))
  cut-assoc (Inl D1) (Case D2 D3) (hypp e') = cut-assoc D1 D2 (hypp e')
  cut-assoc (Inr D1) (Case D2 D3) (hypp e') = cut-assoc D1 D3 (hypp e')
  cut-assoc (Case D1 D2) (hypp x) (hypp e') = ap2 Case (cut-assoc D1 (hypp x) (hypp e')) (cut-assoc D2 (hypp x) (hypp e'))
  cut-assoc (Case D1 D2) (FL D3) (hypp e') = ap2 Case (cut-assoc D1 (FL D3) (hypp e')) (cut-assoc D2 (FL D3) (hypp e'))
  cut-assoc (Case D1 D2) (UL γ₁ x D3) (hypp e') = ap2 Case (cut-assoc D1 (UL γ₁ x D3) (hypp e')) (cut-assoc D2 (UL γ₁ x D3) (hypp e'))
  cut-assoc (Case D1 D2) (Case D3 D4) (hypp e') = ap2 Case (cut-assoc D1 (Case D3 D4) (hypp e')) (cut-assoc D2 (Case D3 D4) (hypp e'))
  cut-assoc {α = α} {β = β} {γ = γ} (UL γ1 e D1) (hypp x) (hypp x₁) = ap2 (UL (γ1 ∘1 (β ∘1 γ))) (! (∘1cong-assoc {e1 = e} {1⇒} {1⇒})) (cut-assoc D1 (hypp x) (hypp x₁))
  cut-assoc {α = α} {β = β} {γ = γ} (UL γ1 e D1) (FL D2) (hypp x) = ap2 (UL (γ1 ∘1 (β ∘1 γ))) (! (∘1cong-assoc {e1 = e} {1⇒} {1⇒})) (cut-assoc D1 (FL D2) (hypp x))
  cut-assoc {α = α} {β = β} {γ = γ} (UL γ1 e D1) (UL γ₁ x D2) (hypp x₁) = ap2 (UL (γ1 ∘1 (β ∘1 γ))) (! (∘1cong-assoc {e1 = e} {1⇒} {1⇒})) (cut-assoc D1 (UL γ₁ x D2) (hypp x₁))
  cut-assoc {α = α} {β = β} {γ = γ} (UL γ1 e D1) (Case D2 D3) (hypp x) = ap2 (UL (γ1 ∘1 (β ∘1 γ))) (! (∘1cong-assoc {e1 = e} {1⇒} {1⇒})) (cut-assoc D1 (Case D2 D3) (hypp x))
  --   Q
  cut-assoc (FL D1) (hypq x) (hypq e') = ap FL (cut-assoc D1 (hypq x) (hypq e'))
  cut-assoc (FL D1) (FL D2) (hypq e') = ap FL (cut-assoc D1 (FL D2) (hypq e'))
  cut-assoc (FL D1) (UL γ₁ x D2) (hypq e') = ap FL (cut-assoc D1 (UL γ₁ x D2) (hypq e'))
  cut-assoc (FL D1) (Case D2 D3) (hypq e') = ap FL (cut-assoc D1 (Case D2 D3) (hypq e'))
  cut-assoc (FR γ₁ x D1) (FL D2) (hypq e') = (transport⊢cut2 {e1 = x ∘1cong 1⇒} (cut D1 D2) (hypq e') ∘ ap (λ H → transport⊢ H (cut (cut D1 D2) (hypq e'))) (! (∘1cong-assoc {e1 = x} {1⇒} {1⇒}))) ∘ ap (transport⊢ (x ∘1cong 1⇒)) (cut-assoc D1 D2 (hypq e'))
  cut-assoc (UR D1) (UL γ₁ x D2) (hypq e') = (transport⊢cut2 {e1 = 1⇒ ∘1cong x} (cut D1 D2) (hypq e')) ∘ ap (transport⊢ (1⇒ ∘1cong (x ∘1cong 1⇒))) (cut-assoc D1 D2 (hypq e'))
  cut-assoc (Inl D1) (Case D2 D3) (hypq e') = cut-assoc D1 D2 (hypq e')
  cut-assoc (Inr D1) (Case D2 D3) (hypq e') = cut-assoc D1 D3 (hypq e')
  cut-assoc (Case D1 D2) (hypq x) (hypq e') = ap2 Case (cut-assoc D1 (hypq x) (hypq e')) (cut-assoc D2 (hypq x) (hypq e'))
  cut-assoc (Case D1 D2) (FL D3) (hypq e') = ap2 Case (cut-assoc D1 (FL D3) (hypq e')) (cut-assoc D2 (FL D3) (hypq e'))
  cut-assoc (Case D1 D2) (UL γ₁ x D3) (hypq e') = ap2 Case (cut-assoc D1 (UL γ₁ x D3) (hypq e')) (cut-assoc D2 (UL γ₁ x D3) (hypq e'))
  cut-assoc (Case D1 D2) (Case D3 D4) (hypq e') = ap2 Case (cut-assoc D1 (Case D3 D4) (hypq e')) (cut-assoc D2 (Case D3 D4) (hypq e'))
  cut-assoc {α = α} {β = β} {γ = γ} (UL γ1 e D1) (hypq x) (hypq x₁) = ap2 (UL (γ1 ∘1 (β ∘1 γ))) (! (∘1cong-assoc {e1 = e} {1⇒} {1⇒})) (cut-assoc D1 (hypq x) (hypq x₁))
  cut-assoc {α = α} {β = β} {γ = γ} (UL γ1 e D1) (FL D2) (hypq x) = ap2 (UL (γ1 ∘1 (β ∘1 γ))) (! (∘1cong-assoc {e1 = e} {1⇒} {1⇒})) (cut-assoc D1 (FL D2) (hypq x))
  cut-assoc {α = α} {β = β} {γ = γ} (UL γ1 e D1) (UL γ₁ x D2) (hypq x₁) = ap2 (UL (γ1 ∘1 (β ∘1 γ))) (! (∘1cong-assoc {e1 = e} {1⇒} {1⇒})) (cut-assoc D1 (UL γ₁ x D2) (hypq x₁))
  cut-assoc {α = α} {β = β} {γ = γ} (UL γ1 e D1) (Case D2 D3) (hypq x) = ap2 (UL (γ1 ∘1 (β ∘1 γ))) (! (∘1cong-assoc {e1 = e} {1⇒} {1⇒})) (cut-assoc D1 (Case D2 D3) (hypq x))
-}

  mutual
    cut≈1 : ∀ {p q r} {α : q ≥ p} {β : r ≥ q} {A : Tp r} {B : Tp q} {C : Tp p}
              {D D' : A [ β ]⊢ B} → D ≈ D' → (E : B [ α ]⊢ C) → cut D E ≈ cut D' E
    cut≈1 = {!!}

    cut≈2 : ∀ {p q r} {α : q ≥ p} {β : r ≥ q} {A : Tp r} {B : Tp q} {C : Tp p}
              (D : A [ β ]⊢ B) {E E' : B [ α ]⊢ C} → E ≈ E' → cut D E ≈ cut D E'
    -- eqv rel
    cut≈2 D id = id
    cut≈2 D (q₁ ∘≈ q₂) = cut≈2 D q₁ ∘≈ cut≈2 D q₂
    cut≈2 D (!≈ q) = !≈ (cut≈2 D q)
    -- congruence of right rules
    cut≈2 D (FR≈ q₂) = !≈ (eq (cutFR D)) ∘≈ (FR≈ (cut≈2 D q₂) ∘≈ eq (cutFR D))
    cut≈2 {α = α} {β = β} D (UR≈ {α = α1} q₂) = !≈ (eq (cutUR D)) ∘≈ (UR≈ {α = α1} {β = β ∘1 α} (cut≈2 D q₂) ∘≈ eq (cutUR D) )
    cut≈2 D (Inl≈ q₁) = !≈ (eq (cutInl D)) ∘≈ (Inl≈ (cut≈2 D q₁) ∘≈ eq (cutInl D))
    cut≈2 D (Inr≈ q₁) = !≈ (eq (cutInr D)) ∘≈ (Inr≈ (cut≈2 D q₁) ∘≈ eq (cutInr D))
    -- congruence of left rules
    -- FL
    cut≈2 (FL D) (FL≈ q₃) = FL≈ (cut≈2 D (FL≈ q₃))
    cut≈2 (FR γ x D) (FL≈ q₁) = transport⊢≈ _ (cut≈2 D q₁)
    cut≈2 (UL γ x D) (FL≈ q₂) = UL≈ (cut≈2 D (FL≈ q₂))
    cut≈2 (Case D D₁) (FL≈ q₂) = Case≈ (cut≈2 D (FL≈ q₂)) (cut≈2 D₁ (FL≈ q₂))
    -- UL
    cut≈2 (FL D) (UL≈ q₃) = FL≈ (cut≈2 D (UL≈ q₃))
    cut≈2 (UL γ x D) (UL≈ q₂) = UL≈ (cut≈2 D (UL≈ q₂))
    cut≈2 (UR D) (UL≈ q₁) = transport⊢≈ _ (cut≈2 D q₁)
    cut≈2 (Case D D₁) (UL≈ q₂) = Case≈ (cut≈2 D (UL≈ q₂)) (cut≈2 D₁ (UL≈ q₂))
    -- Case
    cut≈2 (FL D) (Case≈ q₁ q₂) = FL≈ (cut≈2 D (Case≈ q₁ q₂))
    cut≈2 (UL γ x D) (Case≈ q₁ q₂) = UL≈ (cut≈2 D (Case≈ q₁ q₂))
    cut≈2 (Inl D) (Case≈ q₁ q₂) = cut≈2 D q₁
    cut≈2 (Inr D) (Case≈ q₁ q₂) = cut≈2 D q₂
    cut≈2 (Case D D₁) (Case≈ q₁ q₂) = Case≈ (cut≈2 D (Case≈ q₁ q₂)) (cut≈2 D₁ (Case≈ q₁ q₂))
    -- interesting cases
    -- Fη  
    cut≈2 (FL D) (Fη E) = FL≈ (cut≈2 D (Fη E)) ∘≈ cutFL E
    cut≈2 (FR γ x D) (Fη E) = !≈ (transport⊢≈ (x ∘1cong 1⇒) (cut-assoc D (FR 1m 1⇒ hyp) E)) ∘≈ (!≈ (transport⊢cut2 {e1 = x} (cut D (FR 1m 1⇒ hyp)) E) ∘≈ cut≈1 (eq (ap (transport⊢ x) (! (cutFR {γ = 1m} {e = 1⇒} D))) ∘≈ FR≈ (!≈ (cut-ident-right D))) E)
    cut≈2 (UL γ x D) (Fη E) = UL≈ (cut≈2 D (Fη E)) ∘≈ cutUL E
    cut≈2 (Case D D₁) (Fη E) = Case≈ (cut≈2 D (Fη E)) (cut≈2 D₁ (Fη E)) ∘≈ cutCase E
    -- Uη
    cut≈2 {α = α}{β} D (Uη {β = β2} E) = !≈ (eq (cutUR D)) ∘≈ (UR≈ {α = β2} {β = β ∘1 α} (!≈ (cut-assoc D E (UL 1m 1⇒ hyp))) ∘≈ Uη _)
    -- ⊕η 
    cut≈2 (FL D) (⊕η E) = {!!}
    cut≈2 (UL γ x D) (⊕η E) = {!!}
    cut≈2 (Inl D) (⊕η E) = {!!}
    cut≈2 (Inr D) (⊕η E) = {!!}
    cut≈2 (Case D D₁) (⊕η E) = {!!}
    -- FR2
    cut≈2 D (FR2 {e = e} {D = D1} {D' = D2} γ2 e2 q₁) = !≈ (eq (cutFR D)) ∘≈ (FR2 (1⇒ ∘1cong γ2) (ap (λ x → 1⇒ ∘1cong x) e2 ∘ ! (interchange {e1 = 1⇒} {e2 = 1⇒} {f1 = γ2 ∘1cong 1⇒} {f2 = e})) (!≈ (transport⊢cut1 {e2 = γ2} D D2) ∘≈ cut≈2 D q₁) ∘≈ eq (cutFR D))
    -- UL2
    cut≈2 (FL D) (UL2 γ2 e2 q₂) = FL≈ (cut≈2 D (UL2 γ2 e2 q₂))
    cut≈2 (UL γ x D) (UL2 γ2 e2 q₁) = UL≈ (cut≈2 D (UL2 γ2 e2 q₁))
    cut≈2 (UR D) (UL2 {e = e} {D' = D'} γ2 id q₂) = ((eq (ap (λ x → transport⊢ x (cut D D')) (! (interchange {e1 = 1⇒} {e2 = 1⇒} {f1 = 1⇒ ∘1cong γ2} {f2 = e}) ∘ ap (λ x → x ·2 (1⇒ ∘1cong e)) (∘1cong-assoc {e1 = 1⇒} {1⇒} {γ2}))) ∘≈ eq (! (transport⊢∘ (cut D D')))) ∘≈ !≈ (transport⊢≈ _ (transport⊢cut1 {e2 = γ2} D D'))) ∘≈ transport⊢≈ _ (cut≈2 D q₂)
    cut≈2 (Case D D₁) (UL2 γ2 e2 q₁) = Case≈ (cut≈2 D (UL2 γ2 e2 q₁)) (cut≈2 D₁ (UL2 γ2 e2 q₁))
    -- commuteULFR
    cut≈2 (FL D) (commuteULFR {e4 = e4} D₁ x) = {!!} -- !≈ (Fη _) ∘≈ FL≈ (((FR≈ {! (!≈ (cut-ident-left _ ∘≈ eq (transport⊢1 _))) !} ∘≈ eq (ap (λ x₁ → FR _ x₁ _) (∘1cong-assoc {e1 = 1⇒} {e2 = 1⇒} {e3 = e4}))) ∘≈ eq (cutFR D)) ∘≈ cut≈2 D (commuteULFR D₁ x))
    cut≈2 (UL γ₁ x D) (commuteULFR D₁ x₁) = {!!}
    cut≈2 (UR D) (commuteULFR D₁ x) = {!!}
    cut≈2 (Case D D₁) (commuteULFR D₂ x) = {!!}
    -- commuteULInl
    cut≈2 (FL D) (commuteULInl D₁) = FL≈ ((cut≈2 D (commuteULInl D₁) ∘≈ eq (! (cutInl D))) ∘≈ Inl≈ (cut-ident-left _ ∘≈ eq (transport⊢1 _))) ∘≈ Fη _
    cut≈2 (UL γ x D) (commuteULInl D₁) = UL≈ (cut≈2 D (commuteULInl D₁) ∘≈ eq (! (cutInl D))) ∘≈ commuteULInl _
    cut≈2 (UR D) (commuteULInl D₁) = eq (! (ap (transport⊢ _) (cutInl D)))
    cut≈2 (Case D D₁) (commuteULInl D₂) = Case≈ ((cut≈2 D (commuteULInl D₂) ∘≈ eq (! (cutInl D))) ∘≈ Inl≈ (cut-ident-left _)) ((cut≈2 D₁ (commuteULInl D₂) ∘≈ eq (! (cutInl D₁))) ∘≈ Inl≈ (cut-ident-left _)) ∘≈ ⊕η _
    -- commuteULInr
    cut≈2 (FL D) (commuteULInr D₁) = FL≈ ((cut≈2 D (commuteULInr D₁) ∘≈ eq (! (cutInr D))) ∘≈ Inr≈ (cut-ident-left _ ∘≈ eq (transport⊢1 _))) ∘≈ Fη _
    cut≈2 (UL γ x D) (commuteULInr D₁) = UL≈ (cut≈2 D (commuteULInr D₁) ∘≈ eq (! (cutInr D))) ∘≈ commuteULInr _
    cut≈2 (UR D) (commuteULInr D₁) = eq (! (ap (transport⊢ _) (cutInr D)))
    cut≈2 (Case D D₁) (commuteULInr D₂) = Case≈ ((cut≈2 D (commuteULInr D₂) ∘≈ eq (! (cutInr D))) ∘≈ Inr≈ (cut-ident-left _)) ((cut≈2 D₁ (commuteULInr D₂) ∘≈ eq (! (cutInr D₁))) ∘≈ Inr≈ (cut-ident-left _)) ∘≈ ⊕η _

    -- requires a bunch of commutation because the right-commutative cuts take precedence
    cutUL : ∀ {p q r} {α : q ≥ p} {β : r ≥ q} {B : Tp q} {C : Tp p}
            {q₁} {α₁ : r ≥ q₁} {A : Tp q₁} {γ : q₁ ≥ q}
            {e : (α₁ ∘1 γ) ⇒ β} {D : A [ γ ]⊢ B} (E : B [ α ]⊢ C) →
            cut (UL γ e D) E ≈ UL (γ ∘1 α) (e  ∘1cong 1⇒) (cut D E)
    cutUL (hypp x) = id
    cutUL (hypq x) = id
    cutUL (FL E) = id
    cutUL (UL γ₁ x E) = id
    cutUL (Case E E₁) = id
    -- principal rule fires
    cutUL {α = α} {β} {γ = γ} {e = e} {D = D} (UR {α = α2} E) = !≈ (Uη _) ∘≈ UR≈ {α = α2} {β = β ∘1 α} ((UL≈ (cut-assoc D (UR E) (UL 1m 1⇒ hyp) ∘≈ (eq (! (ap (cut D) (transport⊢1 (cut E hyp)))) ∘≈ cut≈2 D (!≈ (cut-ident-right _)))) ∘≈ eq (ap (λ x → UL (γ ∘1 (α ∘1 α2)) x _) (! (∘1cong-assoc {e1 = e} {1⇒} {1⇒})))) ∘≈ cutUL E)
    -- right-commutative rule fires
    cutUL {α = α} {β} {α₁ = α₁} {γ = γ} {e} {D} (FR γ₁ x E) = (eq (ap (UL {α = α₁} {β = β ∘1 α} (γ ∘1 α) (e ∘1cong 1⇒)) (! (cutFR D))) ∘≈ !≈ (commuteULFR {α = _} {β = γ ∘1 α} {γ = γ ∘1 γ₁} {δ1 = α₁} {δ2 = β ∘1 α} {δ3 = β ∘1 γ₁} (cut D E) (ap (λ H → H ·2 (1⇒ ∘1cong x)) (! (∘1cong-assoc {e1 = e} {1⇒} {1⇒})) ∘ (interchange {e1 = e} {e2 = 1⇒} {f1 = 1⇒ ∘1cong 1⇒} {f2 = x} ∘ (! (interchange {e1 = 1⇒ ∘1cong 1⇒} {e2 = e} {f1 = x} {f2 = 1⇒}) ∘ ap (λ H → H ·2 (e ∘1cong 1⇒)) (! (∘1cong-assoc {e1 = 1⇒} {1⇒} {x}))))))) ∘≈ FR≈ (cutUL E) 
    cutUL {α = α} {β} {α₁ = α₁} {γ = γ} {e} {D} (Inl E) = (UL≈ (eq (! (cutInl D))) ∘≈ commuteULInl (cut D E)) ∘≈ Inl≈ (cutUL E)
    cutUL {α = α} {β} {α₁ = α₁} {γ = γ} {e} {D} (Inr E) = (eq (ap (UL (γ ∘1 α) (e ∘1cong 1⇒)) (! (cutInr D))) ∘≈ commuteULInr (cut D E)) ∘≈ Inr≈ (cutUL E)

    cutFL : ∀ {p q r} {α : q ≥ p} {β : r ≥ q} {B : Tp q} {C : Tp p}
            {q₁} {α1 : q₁ ≥ r} {A : Tp q₁} →
            {D : A [ α1 ∘1 β ]⊢ B} (E : B [ α ]⊢ C)
            → cut (FL D) E ≈ FL {α = α1} {β = β ∘1 α} (cut D E) 
    cutFL {D = D} E = FL≈ ((cut≈1 (cut-ident-left D) E ∘≈ (eq (ap (λ x → cut x E) (transport⊢1 (cut hyp D))))) ∘≈ cut-assoc (FR 1m 1⇒ hyp) (FL D) E) ∘≈ Fη _
  
    cutCase : ∀ {p q r} {α : q ≥ p} {C : Tp p} {A B : Tp q} {C' : Tp r} {β : p ≥ r} {D1 : A [ α ]⊢ C} {D2 : B [ α ]⊢ C} (E : C [ β ]⊢ C')
            → cut (Case D1 D2) E ≈ Case (cut D1 E) (cut D2 E)
    cutCase D = Case≈ (cut≈1 (cut-ident-left _) D ∘≈ cut-assoc (Inl hyp) (Case _ _) D) (cut≈1 (cut-ident-left _) D ∘≈ cut-assoc (Inr hyp) (Case _ _) D) ∘≈ ⊕η _

    cut-ident-left : ∀ {p q} {α : q ≥ p} {A B} → (D : A [ α ]⊢ B)
                  → cut (ident A) D ≈ D
    cut-ident-left (hypp x) = id
    cut-ident-left (hypq x) = id
    cut-ident-left (FL D) = FL≈ (cut-ident-left D ∘≈ eq (transport⊢1 _))
    cut-ident-left {A = A} (FR γ x D) = FR≈ (cut-ident-left D) ∘≈ eq (cutFR {γ = γ} {e = x} hyp)
    cut-ident-left (UR D) = UR≈ (cut-ident-left D) ∘≈ eq (cutUR hyp)
    cut-ident-left (Inl D) = Inl≈ (cut-ident-left D) ∘≈ eq (cutInl hyp)
    cut-ident-left (Inr D) = Inr≈ (cut-ident-left D) ∘≈ eq (cutInr hyp)
    cut-ident-left (Case D D₁) = Case≈ (cut-ident-left _) (cut-ident-left _)
    -- because U is negative, this reduces by a principal cut instead of a commuting one
    cut-ident-left (UL γ x D) = UL≈ {γ = γ} {e = x} (cut-ident-left D) ∘≈ (transport⊢≈ x (cutUL {γ = 1m} {e = 1⇒} {D = hyp} D) )

    cut-ident-right : ∀ {p q} {α : q ≥ p} {A B} → (D : A [ α ]⊢ B)
                      → cut D (ident B) ≈ D
    cut-ident-right (hypp x) = id
    cut-ident-right (hypq x) = id
    cut-ident-right (FR γ x D) = FR≈ (cut-ident-right D) ∘≈ eq (ap (transport⊢ x) (cutFR {γ = 1m} {e = 1⇒} D))
    cut-ident-right (UR D) = UR≈ (cut-ident-right D ∘≈ eq (transport⊢1 _))
    cut-ident-right (Inl D) = Inl≈ (cut-ident-right D) ∘≈ eq (cutInl D {E = hyp})
    cut-ident-right (Inr D) = Inr≈ (cut-ident-right D) ∘≈ eq (cutInr D {E = hyp})
    -- when D is a left rule, we need to split based on what B is
    -- when B is U (or another negative, if we had them), cut will reduce by the right-commutative case instead of the left-commutative one
    -- so we need to use some eta
    -- FL
    cut-ident-right {B = P} (FL D) = FL≈ (cut-ident-right D)
    cut-ident-right {B = Q} (FL D) = FL≈ (cut-ident-right D)
    cut-ident-right {B = F α₁ B} (FL D) = FL≈ (cut-ident-right D)
    cut-ident-right {B = U α₁ B} (FL D) = FL≈ (!≈ (Uη _) ∘≈ UR≈ (cut-ident-left _ ∘≈ eq (transport⊢1 _))) ∘≈ Fη _ 
    cut-ident-right {B = B ⊕ B₁} (FL D) = FL≈ (cut-ident-right D)
    -- UL
    cut-ident-right {B = P} (UL γ x D) = UL≈ (cut-ident-right D)
    cut-ident-right {B = Q} (UL γ x D) = UL≈ (cut-ident-right D)
    cut-ident-right {B = F α₁ B} (UL γ x D) = UL≈ (cut-ident-right D)
    cut-ident-right {B = U α₁ B} (UL γ x D) = !≈ (Uη _)
    cut-ident-right {B = B ⊕ B₁} (UL γ x D) = UL≈ (cut-ident-right D)
    -- case
    cut-ident-right {B = P} (Case D D₁) = Case≈ (cut-ident-right D) (cut-ident-right D₁)
    cut-ident-right {B = Q} (Case D D₁) = Case≈ (cut-ident-right D) (cut-ident-right D₁)
    cut-ident-right {B = F α₁ B} (Case D D₁) = Case≈ (cut-ident-right D) (cut-ident-right D₁)
    cut-ident-right {B = U α₁ B} (Case D D₁) = !≈ (Uη _)
    cut-ident-right {B = B ⊕ B₁} (Case D D₁) = Case≈ (cut-ident-right D) (cut-ident-right D₁)


