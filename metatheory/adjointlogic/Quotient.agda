
open import adjointlogic.Lib
open import adjointlogic.Rules
open import adjointlogic.Properties

module adjointlogic.Quotient where

  -- FIXME: this isn't really formal, but it is suggestive... 
  -- do things the hard way?

  transport⊢Fη : ∀ {p q r} {α : q ≥ p} {β β' : p ≥ r} {A : Tp q} {C : Tp r}
                 (e : β ⇒ β') (D : F α A [ β ]⊢ C) → 
                 transport⊢ e D == transport⊢ e (FL (cut {α = β} {β = α} (FR {α = α} {β = 1m ∘1 α} 1m 1⇒ hyp) D) )
  transport⊢Fη e D = ap FL (! (transport⊢cut {e1 = 1⇒} {e2 = e} (FR 1m 1⇒ hyp) D)) ∘ Fη _

  transport⊢Uη : ∀ {p q r} {α α' : p ≥ q} {β : q ≥ r} {A : Tp p} {C : Tp r}
                 (e : α ⇒ α') (D : A [ α ]⊢ U β C) → 
                 transport⊢ e D == transport⊢ e (UR (cut D (UL 1m 1⇒ hyp)))
  transport⊢Uη e D = ap UR (! (transport⊢cut {e1 = e} {e2 = 1⇒} D (UL 1m 1⇒ hyp))) ∘ Uη _

  transport⊢⊕η : ∀ {p q} {α α' : p ≥ q} {A B : Tp p} {C : Tp q} 
                  (e : α ⇒ α') (D : (A ⊕ B) [ α ]⊢ C) 
                → transport⊢ e D == transport⊢ e (Case (cut (Inl hyp) D) (cut (Inr hyp) D))
  transport⊢⊕η e D = ap2 Case (! (transport⊢cut1 {e2 = e} (Inl hyp) D)) (! (transport⊢cut1 {e2 = e} (Inr hyp) D)) ∘ ⊕η _

  transport⊢FR2 : ∀ {p q r} {α : q ≥ p} {β β' : r ≥ p} {A : Tp q} {C : Tp r}
                → {γ γ' : r ≥ q} → {e : (γ ∘1 α) ⇒ β} {e' : (γ' ∘1 α) ⇒ β } {D : C [ γ ]⊢ A}  {D' : C [ γ' ]⊢ A} 
                → (γ2 : γ' ⇒ γ) (e2 : ((γ2 ∘1cong 1⇒) ·2 e) == e') (D2 : D == transport⊢ γ2 D')
                → (β2 : β ⇒ β')
                → transport⊢ β2 (FR γ e D) == transport⊢ β2 (FR γ' e' D')
  transport⊢FR2 γ2 e2 D2 β2 = FR2 γ2 (ap (λ x → x ·2 β2) e2) D2

  transport⊢UL2 : ∀ {p q r} {α : p ≥ r} {β β' : p ≥ q} {A : Tp q} {C : Tp r}
                → {γ γ' : r ≥ q} → {e : (α ∘1 γ) ⇒ β } {e' : (α ∘1 γ') ⇒ β } {D : C [ γ ]⊢ A}  {D' : C [ γ' ]⊢ A} 
                → (γ2 : γ' ⇒ γ) (e2 : ((1⇒ ∘1cong γ2) ·2 e) == e') (D2 : D == transport⊢ γ2  D') (β2 : β ⇒ β')
                → transport⊢ β2 (UL γ e D) == transport⊢ β2 (UL γ' e' D')
  transport⊢UL2 γ2 e2 D2 β2 = UL2 γ2 (ap (λ x → x ·2 β2) e2) D2

  transport⊢commuteULInl : ∀ {p q r} {α : p ≥ q} {β β' : p ≥ r} {A : Tp q} {C C' : Tp r}
                         → {γ : q ≥ r} {e : (α ∘1 γ) ⇒ β} (D : A [ γ ]⊢ C) (β2 : β ⇒ β')
                         → transport⊢ β2 (Inl {B = C'} (UL γ e D)) == transport⊢ β2 (UL γ e (Inl D))
  transport⊢commuteULInl D β2 = commuteULInl _

  transport⊢commuteULInr : ∀ {p q r} {α : p ≥ q} {β β' : p ≥ r} {A : Tp q} {C C' : Tp r}
                         → {γ : q ≥ r} {e : (α ∘1 γ) ⇒ β} (D : A [ γ ]⊢ C) (β2 : β ⇒ β')
                         → transport⊢ β2 (Inr {A = C'} (UL γ e D)) == transport⊢ β2 (UL γ e (Inr  D))
  transport⊢commuteULInr D β2 = commuteULInr _

{- OK but takes a while
  transport⊢commuteULFR : ∀ {p q r s} {A : Tp q} {C : Tp r}
                   {α : q ≥ p} {β : r ≥ p} {γ : r ≥ q} {δ1 : s ≥ r} {δ2 δ2' : s ≥ p} {δ3 : s ≥ q} 
                   {e1 : (γ ∘1 α) ⇒ β} {e2 : (δ1 ∘1 β) ⇒ δ2}
                   {e3 : (δ1 ∘1 γ) ⇒ δ3} {e4 : (δ3 ∘1 α) ⇒ δ2} 
                   (D : C [ γ ]⊢ A) (δ22 : δ2 ⇒ δ2')
                → ((1⇒ ∘1cong e1) ·2 e2) == ((e3 ∘1cong 1⇒) ·2 e4)
                → _==_ { U δ1 C [ δ2' ]⊢ F α A } 
                        (transport⊢ δ22 (UL β e2 (FR γ e1 D)))
                        (transport⊢ δ22 (FR δ3 e4 (UL γ e3 D)))
  transport⊢commuteULFR D δ22 p = commuteULFR D (ap (λ x → x ·2 δ22) p)
-}

  -- ----------------------------------------------------------------------
  -- FIXME: cutFL and cutUL and cutCase and cut-ident-left and cut-ident-right need to be mutual with these?

  cutFη1 : ∀ {p q r} {α : q ≥ p} {β : p ≥ r} {A : Tp q} {C : Tp r} 
             (D : F α A [ β ]⊢ C) → {s : Mode} {C' : Tp s} {γ : r ≥ s} (E : C [ γ ]⊢ C')
             → cut D E == cut (FL (cut {α = β} {β = α} (FR {α = α} {β = 1m ∘1 α} 1m 1⇒ hyp) D)) E
  cutFη1 D E = ! (cutFL E) ∘ (ap FL (cut-assoc (FR 1m 1⇒ hyp) D E) ∘ Fη _)

  -- FIXME is induction on E allowed?
  cutFη2 : ∀ {p q r} {α : q ≥ p} {β : p ≥ r} {A : Tp q} {C : Tp r} 
             (D : F α A [ β ]⊢ C) → {s : Mode} {C' : Tp s} {γ : s ≥ _} (E : C' [ γ ]⊢ _)
             → cut E D == cut E (FL (cut {α = β} {β = α} (FR {α = α} {β = 1m ∘1 α} 1m 1⇒ hyp) D))
  cutFη2 D (FL E) = ap FL (cutFη2 D E) ∘ cutFL D
  cutFη2 {α = α} {β} D (FR γ₁ x E) = ! (ap (transport⊢ (x ∘1cong 1⇒)) (cut-assoc E (FR 1m 1⇒ hyp) D)) ∘ (! (transport⊢cut {e1 = x} {e2 = 1⇒} (cut E (FR 1m 1⇒ hyp)) D) ∘ ap2 cut (ap (transport⊢ x) (! (cutFR {e = 1⇒} E {E = hyp})) ∘ ap (FR γ₁ x) (! (cut-ident-right E))) (! (transport⊢1 D)))
  cutFη2 D (UL γ₁ x E) = ap (UL _ _) (cutFη2 D E) ∘ cutUL D
  cutFη2 D (Case E E₁) = ap2 Case (cutFη2 D E) (cutFη2 D E₁) ∘ cutCase D

  
  cutFR21 : ∀ {p q r} {α : q ≥ p} {β : r ≥ p} {A : Tp q} {C : Tp r}
          → {γ γ' : r ≥ q} → {e : (γ ∘1 α) ⇒ β} {e' : (γ' ∘1 α) ⇒ β } {D : C [ γ ]⊢ A}  {D' : C [ γ' ]⊢ A} 
          → (γ2 : γ' ⇒ γ) (e2 : ((γ2 ∘1cong 1⇒) ·2 e) == e') (D2 : D == transport⊢ γ2 D')
            {s : Mode} {C' : Tp s} {δ : _ ≥ s} (E : _ [ δ ]⊢ C')
          → cut (FR γ e D) E == cut (FR γ' e' D') E
  cutFR21 {e = e} {e' = e'} {D = D} {D' = D'} γ2 e2 D2 (FL E) = ((ap (λ H → transport⊢ H (cut D' E)) (ap (λ x → x ∘1cong 1⇒) e2 ∘ ! (interchange {e1 = γ2 ∘1cong 1⇒} {e2 = e} {f1 = 1⇒} {f2 = 1⇒})) ∘ ! (transport⊢∘ (cut D' E))) ∘ ap (λ H → transport⊢ (e ∘1cong 1⇒) H) (! (transport⊢cut2 {e1 = γ2} D' E))) ∘ ap (λ D'' → transport⊢ (e ∘1cong 1⇒) (cut D'' E)) D2
  cutFR21 γ2 e2 D2 (FR γ₁ x E) = ap (FR _ _) (cutFR21 γ2 e2 D2 E)
  cutFR21 {α = α} {β = β} γ2 e2 D2  {δ = δ} (UR {α = α1} E) = ap (UR {α = α1} {β = β ∘1 δ}) (cutFR21 γ2 e2 D2 E) 
  cutFR21 γ2 e2 D2 (Inl E) = ap Inl (cutFR21 γ2 e2 D2 E)
  cutFR21 γ2 e2 D2 (Inr E) = ap Inr (cutFR21 γ2 e2 D2 E)

  cutFR22 : ∀ {p q r} {α : q ≥ p} {β : r ≥ p} {A : Tp q} {C : Tp r}
          → {γ γ' : r ≥ q} → {e : (γ ∘1 α) ⇒ β} {e' : (γ' ∘1 α) ⇒ β } {D : C [ γ ]⊢ A}  {D' : C [ γ' ]⊢ A} 
          → (γ2 : γ' ⇒ γ) (e2 : ((γ2 ∘1cong 1⇒) ·2 e) == e') (D2 : D == transport⊢ γ2 D')
            {s : Mode} {C' : Tp s} {δ : s ≥ _} (E : C' [ δ ]⊢ _)
          → cut E (FR γ e D) == cut E (FR γ' e' D')
  cutFR22 {e = e} γ2 e2 D2 E  = ! (cutFR E) ∘ (FR2 (1⇒ ∘1cong γ2) (ap (λ x → 1⇒ ∘1cong x) e2 ∘ ! (interchange {e1 = 1⇒} {e2 = 1⇒} {f1 = γ2 ∘1cong 1⇒} {f2 = e})) (! (transport⊢cut1 {e2 = γ2} E _) ∘ ap (cut E) D2) ∘ cutFR E)


  cutcommuteULInl1 : ∀ {p q r} {α : p ≥ q} {β : p ≥ r} {A : Tp q} {C C' : Tp r}
                   → {γ : q ≥ r} {e : (α ∘1 γ) ⇒ β} (D : A [ γ ]⊢ C)
                      {s : Mode} {C'' : Tp s} {δ : s ≥ _} (E : C'' [ δ ]⊢ _)
                   → cut E (Inl {B = C'} (UL γ e D)) == cut E (UL γ e (Inl D))
  cutcommuteULInl1 D (FL E) = ap FL (cutcommuteULInl1 D E ∘ (! (cutInl E) ∘ ap Inl (cut-ident-left _ ∘ transport⊢1 _))) ∘ Fη _
  cutcommuteULInl1 D (UL γ₁ x E) = ap (UL _ _) (cutcommuteULInl1 D E ∘ ! (cutInl E)) ∘ commuteULInl _
  cutcommuteULInl1 D (UR E) = ! (ap (transport⊢ _) (cutInl E)) 
  cutcommuteULInl1 D (Case E E₁) = ap2 Case ((cutcommuteULInl1 D E ∘ ! (cutInl E)) ∘ ap Inl (cut-ident-left _)) ((cutcommuteULInl1 D E₁ ∘ ! (cutInl E₁)) ∘ ap Inl (cut-ident-left _)) ∘ ⊕η _

  cutcommuteULInl2 : ∀ {p q r} {α : p ≥ q} {β : p ≥ r} {A : Tp q} {C C' : Tp r}
                   → {γ : q ≥ r} {e : (α ∘1 γ) ⇒ β} (D : A [ γ ]⊢ C)
                      {s : Mode} {C'' : Tp s} {δ : _ ≥ s} (E : _ [ δ ]⊢ C'')
                   → cut (Inl {B = C'} (UL γ e D)) E == cut (UL γ e (Inl D)) E
  cutcommuteULInl2 D (FR γ₁ x E) = ap (FR _ _) (cutcommuteULInl2 D E)
  cutcommuteULInl2 {α = α} {β = β} D {δ = δ} (UR {α = α1} E) = ap (UR {α = α1} {β = β ∘1 δ}) (cutcommuteULInl2 D E)
  cutcommuteULInl2 D (Inl E) = ap Inl (cutcommuteULInl2 D E)
  cutcommuteULInl2 D (Inr E) = ap Inr (cutcommuteULInl2 D E)
  cutcommuteULInl2 D (Case E E₁) = cutUL E
