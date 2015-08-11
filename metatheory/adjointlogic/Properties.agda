
open import adjointlogic.Lib
open import adjointlogic.Rules

module adjointlogic.Properties where

 abstract
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
    transport⊢cut : ∀ {p q r} {α α' : q ≥ p} {β β' : r ≥ q} {A : Tp r} {B : Tp q} {C : Tp p}
        {e1 : β ⇒ β'} {e2 : α ⇒ α'} (D : A [ β ]⊢ B) (E : B [ α ]⊢ C)
        → transport⊢ (e1 ∘1cong e2) (cut D E) == cut (transport⊢ e1 D) (transport⊢ e2 E)
    -- E is hyp
    transport⊢cut {e1 = e1} {e2 = e2} (hypp x) (hypp x₁) = ap hypp (! (interchange {e1 = x} {e2 = e1} {f1 = x₁} {f2 = e2}))
    transport⊢cut {e1 = e1} {e2 = e2} (FL D) (hypp x) = ap FL (transport⊢cut {e1 = 1⇒ ∘1cong e1} {e2 = e2} D (hypp x))
    transport⊢cut {e1 = e1} {e2 = e2} (UL γ x D) (hypp x₁) = ! (UL2 (1⇒ ∘1cong e2) (interchange {e1 = x} {e2 = e1} {f1 = 1⇒} {f2 = e2} ∘ (! (interchange {e1 = 1⇒ ∘1cong 1⇒} {e2 = x ·2 e1} {f1 = e2} {f2 = 1⇒}) ∘ ap (λ H → H ·2 ((x ·2 e1) ∘1cong 1⇒)) (! (∘1cong-assoc {e1 = 1⇒} {1⇒} {e2})))) (! (transport⊢cut {e1 = 1⇒} {e2 = e2} D (hypp x₁)) ∘ ! (ap (λ x₂ → cut x₂ (hypp (x₁ ·2 e2))) (transport⊢1 D))))
    transport⊢cut (Case D D₁) (hypp x) = ap2 Case (transport⊢cut D (hypp x)) (transport⊢cut D₁ (hypp x))
    transport⊢cut {e1 = e1} {e2 = e2} (hypq x) (hypq x₁) = ap hypq (! (interchange {e1 = x} {e2 = e1} {f1 = x₁} {f2 = e2}))
    transport⊢cut {e1 = e1} {e2 = e2} (FL D) (hypq x) = ap FL (transport⊢cut {e1 = 1⇒ ∘1cong e1} {e2 = e2} D (hypq x))
    transport⊢cut {e1 = e1} {e2 = e2} (UL γ x D) (hypq x₁) = ! (UL2 (1⇒ ∘1cong e2) (interchange {e1 = x} {e2 = e1} {f1 = 1⇒} {f2 = e2} ∘ (! (interchange {e1 = 1⇒ ∘1cong 1⇒} {e2 = x ·2 e1} {f1 = e2} {f2 = 1⇒}) ∘ ap (λ H → H ·2 ((x ·2 e1) ∘1cong 1⇒)) (! (∘1cong-assoc {e1 = 1⇒} {1⇒} {e2})))) (! (transport⊢cut {e1 = 1⇒} {e2 = e2} D (hypq x₁)) ∘ ! (ap (λ x₂ → cut x₂ (hypq (x₁ ·2 e2))) (transport⊢1 D))))
    transport⊢cut (Case D D₁) (hypq x) = ap2 Case (transport⊢cut D (hypq x)) (transport⊢cut D₁ (hypq x))
    -- E is FL
    transport⊢cut {e1 = e1} {e2} (FL D) (FL E) = ap FL (transport⊢cut {e1 = 1⇒ ∘1cong e1} {e2 = e2} D (FL E))
    transport⊢cut {e1 = e1} {e2} (FR γ x D) (FL E) = (ap (transport⊢ ((x ·2 e1) ∘1cong 1⇒)) (transport⊢cut1 {e2 = 1⇒ ∘1cong e2} D E) ∘ (transport⊢∘ (cut D E) ∘ ap (λ x₁ → transport⊢ x₁ (cut D E)) (! (interchange {e1 = x} {e2 = e1} {f1 = 1⇒} {f2 = e2} ∘ (! (interchange {e1 = 1⇒ ∘1cong 1⇒} {e2 = x ·2 e1} {f1 = e2} {f2 = 1⇒}) ∘ ap (λ H → H ·2 ((x ·2 e1) ∘1cong 1⇒)) (! (∘1cong-assoc {e1 = 1⇒} {1⇒} {e2}))))))) ∘ ! (transport⊢∘ (cut D E))
    transport⊢cut {e1 = e1} {e2} (UL γ x D) (FL E) = ! (UL2 (1⇒ ∘1cong e2) (interchange {e1 = x} {e2 = e1} {f1 = 1⇒} {f2 = e2} ∘ (! (interchange {e1 = 1⇒ ∘1cong 1⇒} {e2 = x ·2 e1} {f1 = e2} {f2 = 1⇒}) ∘ ap (λ H → H ·2 ((x ·2 e1) ∘1cong 1⇒)) (! (∘1cong-assoc {e1 = 1⇒} {1⇒} {e2})))) (! (transport⊢cut1 {e2 = e2} D (FL E))))
    transport⊢cut (Case D D₁) (FL E) = ap2 Case (transport⊢cut D (FL E)) (transport⊢cut D₁ (FL E))
    -- E is UL
    transport⊢cut {e1 = e1} {e2} (FL D) (UL γ x E) = ap FL (transport⊢cut {e1 = 1⇒ ∘1cong e1} {e2 = e2} D (UL γ x E))
    transport⊢cut {e1 = e1} {e2} (UL γ x D) (UL γ₁ x₁ E) = ! (UL2 (1⇒ ∘1cong e2) (interchange {e1 = x} {e2 = e1} {f1 = 1⇒} {f2 = e2} ∘ (! (interchange {e1 = 1⇒ ∘1cong 1⇒} {e2 = x ·2 e1} {f1 = e2} {f2 = 1⇒}) ∘ ap (λ H → H ·2 ((x ·2 e1) ∘1cong 1⇒)) (! (∘1cong-assoc {e1 = 1⇒} {1⇒} {e2})))) (! (transport⊢cut1 {e2 = e2} D (UL γ₁ x₁ E))))
    transport⊢cut {e1 = e1} {e2 = e2} (UR D) (UL γ x E) = (ap (transport⊢ (1⇒ ∘1cong (x ·2 e2))) (transport⊢cut2 {e1 = e1 ∘1cong 1⇒} D E) ∘ (transport⊢∘ (cut D E) ∘ ap (λ x₁ → transport⊢ x₁ (cut D E)) (! (interchange {e1 = 1⇒} {e2 = e1} {f1 = x} {f2 = e2} ∘ ! (interchange {e1 = e1} {e2 = 1⇒} {f1 = 1⇒ ∘1cong 1⇒} {f2 = x ·2 e2}))))) ∘ ! (transport⊢∘ (cut D E))
    transport⊢cut (Case D D₁) (UL γ x E) = ap2 Case (transport⊢cut D (UL γ x E)) (transport⊢cut D₁ (UL γ x E))
    -- E is case
    transport⊢cut {e1 = e1} {e2} (FL D) (Case E E₁) = ap FL (transport⊢cut {e1 = 1⇒ ∘1cong e1} {e2} D (Case E E₁))
    transport⊢cut {e1 = e1} {e2} (UL γ x D) (Case E E₁) = ! (UL2 (1⇒ ∘1cong e2) (interchange {e1 = x} {e2 = e1} {f1 = 1⇒} {f2 = e2} ∘ (! (interchange {e1 = 1⇒ ∘1cong 1⇒} {e2 = x ·2 e1} {f1 = e2} {f2 = 1⇒}) ∘ ap (λ H → H ·2 ((x ·2 e1) ∘1cong 1⇒)) (! (∘1cong-assoc {e1 = 1⇒} {1⇒} {e2})))) (! (transport⊢cut {e1 = 1⇒} {e2} D (Case E E₁)) ∘ ap (λ x₁ → cut x₁ (Case (transport⊢ e2 E) (transport⊢ e2 E₁))) (! (transport⊢1 D))))
    transport⊢cut (Case D D₁) (Case E E₁) = ap2 Case (transport⊢cut D (Case E E₁)) (transport⊢cut D₁ (Case E E₁))
    transport⊢cut (Inl D) (Case E E₁) = transport⊢cut D E
    transport⊢cut (Inr D) (Case E E₁) = transport⊢cut D E₁
    -- E is a right rule
    transport⊢cut {e1 = e1} {e2} D (FR γ x E) = (! (cutFR (transport⊢ e1 D)) ∘ ! (FR2 (e1 ∘1cong 1⇒) (interchange {e1 = 1⇒} {e2 = e1} {f1 = x} {f2 = e2} ∘ (! (interchange {e1 = e1} {e2 = 1⇒} {f1 = 1⇒ ∘1cong 1⇒} {f2 = x ·2 e2}))) (! (transport⊢cut {e1 = e1} {e2 = 1⇒} D E) ∘ ap (cut (transport⊢ e1 D)) (! (transport⊢1 E))))) ∘ ap (transport⊢ (e1 ∘1cong e2)) (cutFR D)
    transport⊢cut {α = α} {α'} {β} {β'} {e1 = e1} {e2} D (UR {α = α1} E) = (! (cutUR (transport⊢ e1 D)) ∘ ap (UR {α = α1} {β' ∘1 α'}) (transport⊢cut {α = α ∘1 α1} {α' ∘1 α1} {β} {β'} {e1 = e1} {e2 = e2 ∘1cong 1⇒} D E)) ∘ ap (transport⊢ (e1 ∘1cong e2)) (cutUR D)
    transport⊢cut {α = α} {α'} {β} {β'} {e1 = e1} {e2} D (Inl E) = (! (cutInl (transport⊢ e1 D)) ∘ ap Inl (transport⊢cut {α = α} {α'} {β} {β'} {e1 = e1} {e2 = e2} D E)) ∘ ap (transport⊢ (e1 ∘1cong e2)) (cutInl D) 
    transport⊢cut {α = α} {α'} {β} {β'} {e1 = e1} {e2} D (Inr E) =  (! (cutInr (transport⊢ e1 D)) ∘ ap Inr (transport⊢cut {α = α} {α'} {β} {β'} {e1 = e1} {e2 = e2} D E)) ∘ ap (transport⊢ (e1 ∘1cong e2)) (cutInr D) 

    transport⊢cut1 : ∀ {p q r} {α α' : q ≥ p} {β : r ≥ q} {A : Tp r} {B : Tp q} {C : Tp p}
        {e2 : α ⇒ α'} (D : A [ β ]⊢ B) (E : B [ α ]⊢ C)
        → transport⊢ (1⇒ ∘1cong e2) (cut D E) == cut D (transport⊢ e2 E)
    transport⊢cut1 {e2 = e2} D E = ap (λ x → cut x (transport⊢ e2 E)) (transport⊢1 D) ∘ transport⊢cut {e1 = 1⇒} {e2} D E

    transport⊢cut2 : ∀ {p q r} {α : q ≥ p} {β β' : r ≥ q} {A : Tp r} {B : Tp q} {C : Tp p}
        {e1 : β ⇒ β'} (D : A [ β ]⊢ B) (E : B [ α ]⊢ C)
        → transport⊢ (e1 ∘1cong 1⇒) (cut D E) == cut (transport⊢ e1 D) E
    transport⊢cut2 {e1 = e1} D E = ap (λ x → cut (transport⊢ e1 D) x) (transport⊢1 E) ∘ transport⊢cut {e1 = e1} {1⇒} D E

  cut-assoc : ∀ {p q r s} {α : p ≥ q} {β : q ≥ r} {γ : r ≥ s} {A : Tp p} {B : Tp q} {C : Tp r} {D : Tp s}
                (D1 : A [ α ]⊢ B) (D2 : B [ β ]⊢ C) (D3 : C [ γ ]⊢ D) →
                cut D1 (cut D2 D3) == cut (cut D1 D2) D3
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

  mutual
    -- needs η and associativity
    -- requires a bunch of commutation because the right-commutative cuts take precedence
    cutUL : ∀ {p q r} {α : q ≥ p} {β : r ≥ q} {B : Tp q} {C : Tp p}
            {q₁} {α₁ : r ≥ q₁} {A : Tp q₁} {γ : q₁ ≥ q}
            {e : (α₁ ∘1 γ) ⇒ β} {D : A [ γ ]⊢ B} (E : B [ α ]⊢ C) →
            cut (UL γ e D) E == UL (γ ∘1 α) (e  ∘1cong 1⇒) (cut D E)
    cutUL (hypp x) = id
    cutUL (hypq x) = id
    cutUL (FL E) = id
    cutUL (UL γ₁ x E) = id
    cutUL (Case E E₁) = id
    -- principal rule fires
    cutUL {α = α} {β} {γ = γ} {e = e} {D = D} (UR {α = α2} E) = ! (Uη _) ∘ ap (UR {α = α2} {β = β ∘1 α}) (ap2 (UL (γ ∘1 (α ∘1 α2))) (! (∘1cong-assoc {e1 = e} {1⇒} {1⇒})) ((cut-assoc D (UR E) (UL 1m 1⇒ hyp) ∘ ! (ap (cut D) (transport⊢1 (cut E hyp)))) ∘ ap (cut D) (! (cut-ident-right E))) ∘ cutUL {e = e} {D = D} E) 
    -- right-commutative rule fires
    cutUL (FR γ₁ x E) = {!!}  -- FIXME need some more rules for this to be true
    cutUL (Inl E) = {!!}
    cutUL (Inr E) = {!!}

    cut-ident-left : ∀ {p q} {α : q ≥ p} {A B} → (D : A [ α ]⊢ B)
                  → cut (ident A) D == D
    cut-ident-left (hypp x) = id
    cut-ident-left (hypq x) = id
    cut-ident-left (FL D) = ap FL (cut-ident-left D ∘ transport⊢1 _)
    cut-ident-left {A = A} (FR γ x D) = ap (FR γ x) (cut-ident-left D) ∘ cutFR {γ = γ} {e = x} hyp
    cut-ident-left (UR D) = ap UR (cut-ident-left D) ∘ cutUR hyp
    cut-ident-left (Inl D) = ap Inl (cut-ident-left D) ∘ cutInl hyp
    cut-ident-left (Inr D) = ap Inr (cut-ident-left D) ∘ cutInr hyp
    cut-ident-left (Case D D₁) = ap2 Case (cut-ident-left _) (cut-ident-left _)
    -- because U is negative, this is a principal cut instead of a commuting one
    cut-ident-left (UL γ x D) = ap (UL γ x) (cut-ident-left D) ∘ ap (transport⊢ x) (cutUL {γ = 1m} {e = 1⇒} {D = hyp} D) -- lemma γ x D where
{-
         -- proving this directly seems to need the same extra rules as cutUL does
         lemma : ∀ {p q} {α : q ≥ p} {B : Tp p} {q₁} {α₁ : q ≥ q₁}
                   {A : Tp q₁} (γ : q₁ ≥ p) (x : (α₁ ∘1 γ) ⇒ α) (D : A [ γ ]⊢ B) →
                   transport⊢ x (cut (UL 1m 1⇒ (ident A)) D) == UL γ x D
         lemma γ₁ e (hypp x₁) = id
         lemma γ₁ e (hypq x₁) = id
         lemma γ₁ e (FL D₁) = {!OK!}
         lemma γ₁ e (FR γ₂ x₁ D₁) = {!!}
         lemma γ₁ e (UL γ₂ x₁ D₁) = ap (UL γ₁ e) (lemma γ₂ x₁ D₁)
         lemma γ₁ e (UR D₁) = ! (Uη _) ∘ ap UR {!? ∘ (transport⊢cut {e1 = e ∘1cong 1⇒} {1⇒} (UL 1m 1⇒ hyp) D₁ ∘ ?)!}
         lemma γ₁ e (Inl D₁) = {!!} ∘ ap Inl (lemma γ₁ e D₁)
         lemma γ₁ e (Inr D₁) = {!!} ∘ ap Inr (lemma γ₁ e D₁)
         lemma γ₁ e (Case D₁ D₂) = ap (UL γ₁ e) (ap2 Case (cut-ident-left D₁) (cut-ident-left D₂))
-}

    cut-ident-right : ∀ {p q} {α : q ≥ p} {A B} → (D : A [ α ]⊢ B)
                      → cut D (ident B) == D
    cut-ident-right (hypp x) = id
    cut-ident-right (hypq x) = id
    cut-ident-right (FR γ x D) = ap (FR γ x) (cut-ident-right D) ∘ ap (transport⊢ x) (cutFR {γ = 1m} {e = 1⇒} D)
    cut-ident-right (UR D) = ap UR (cut-ident-right D ∘ transport⊢1 _)
    cut-ident-right (Inl D) = ap Inl (cut-ident-right D) ∘ cutInl D {E = hyp}
    cut-ident-right (Inr D) = ap Inr (cut-ident-right D) ∘ cutInr D {E = hyp}
    -- when D is a left rule, we need to split based on what B is
    -- when B is U (or another negative, if we had them), cut will reduce by the right-commutative case instead of the left-commutative one
    -- so we need to use some eta
    -- FL
    cut-ident-right {B = P} (FL D) = ap FL (cut-ident-right D)
    cut-ident-right {B = Q} (FL D) = ap FL (cut-ident-right D)
    cut-ident-right {B = F α₁ B} (FL D) = ap FL (cut-ident-right D)
    cut-ident-right {B = U α₁ B} (FL D) = ap FL (! (Uη _) ∘ ap UR (cut-ident-left _ ∘ transport⊢1 _)) ∘ Fη _ 
    cut-ident-right {B = B ⊕ B₁} (FL D) = ap FL (cut-ident-right D)
    -- UL
    cut-ident-right {B = P} (UL γ x D) = ap (UL γ x) (cut-ident-right D)
    cut-ident-right {B = Q} (UL γ x D) = ap (UL γ x) (cut-ident-right D)
    cut-ident-right {B = F α₁ B} (UL γ x D) = ap (UL γ x) (cut-ident-right D)
    cut-ident-right {B = U α₁ B} (UL γ x D) = ! (Uη _)
    cut-ident-right {B = B ⊕ B₁} (UL γ x D) = ap (UL γ x) (cut-ident-right D)
    -- case
    cut-ident-right {B = P} (Case D D₁) = ap2 Case (cut-ident-right D) (cut-ident-right D₁)
    cut-ident-right {B = Q} (Case D D₁) = ap2 Case (cut-ident-right D) (cut-ident-right D₁)
    cut-ident-right {B = F α₁ B} (Case D D₁) = ap2 Case (cut-ident-right D) (cut-ident-right D₁)
    cut-ident-right {B = U α₁ B} (Case D D₁) = ! (Uη _)
    cut-ident-right {B = B ⊕ B₁} (Case D D₁) = ap2 Case (cut-ident-right D) (cut-ident-right D₁)

  cutFL : ∀ {p q r} {α : q ≥ p} {β : r ≥ q} {B : Tp q} {C : Tp p}
          {q₁} {α1 : q₁ ≥ r} {A : Tp q₁} →
          {D : A [ α1 ∘1 β ]⊢ B} (E : B [ α ]⊢ C)
          → cut (FL D) E == FL {α = α1} {β = β ∘1 α} (cut D E) 
  cutFL {D = D} E = ap FL ((ap (λ x → cut x E) (cut-ident-left D) ∘ ap (λ x → cut x E) (transport⊢1 (cut hyp D))) ∘ cut-assoc (FR 1m 1⇒ hyp) (FL D) E) ∘ Fη _
