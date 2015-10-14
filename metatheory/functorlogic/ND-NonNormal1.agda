
-- non-normal and definitional equality

open import functorlogic.Lib
open import functorlogic.Modes
open import functorlogic.SequentHypOnly

module functorlogic.ND-NonNormal1 where


  data _[_]⊢_[_] {p r : Mode} (A1 : Tp r) (α1 : r ≥ p) : {q : Mode} → Tp q -> q ≥ p → Set where
      v   : A1 [ α1 ]⊢ A1 [ α1 ]
      Nat : {q : Mode} {A : Tp q} {α α' : q ≥ p} 
          → (e : α' ⇒ α) → A1 [ α1 ]⊢ A [ α ] 
          → A1 [ α1 ]⊢ A [ α' ]
      LetFunc : {q r s : Mode} {C : Tp r} {A2 : Tp s} {α2 : s ≥ q} (α : q ≥ p) {γ : r ≥ q}
              → A1 [ α1 ]⊢ A2 [ α2 ∘1 α ] → A2 [ α2 ]⊢ C [ γ ] 
              → A1 [ α1 ]⊢ C [ γ ∘1 α ] 
      FE : {q r : Mode} {A : Tp r} {β : q ≥ p} {α : r ≥ q} 
        → A1 [ α1 ]⊢ F α A [ β ] 
        → A1 [ α1 ]⊢ A [ α ∘1 β ]
      FI : {q r : Mode} {A : Tp r} {β : q ≥ p} {α : r ≥ q}
         → A1 [ α1 ]⊢ A [ α ∘1 β ]
         → A1 [ α1 ]⊢ F α A [ β ]

  subst : ∀ {p q r s : Mode} {A1 : Tp r} {α1 : r ≥ p} {A : Tp q} {α : q ≥ p} {C : Tp s} {γ : s ≥ p}
          → A1 [ α1 ]⊢ A [ α ]
          → A [ α ]⊢ C [ γ ]
          → A1 [ α1 ]⊢ C [ γ ]
  subst D v = D
  subst D (Nat e E) = Nat e (subst D E)
  subst D (LetFunc α₁ E E₁) = LetFunc α₁ (subst D E) E₁
  subst D (FE E) = FE (subst D E)
  subst D (FI E) = FI (subst D E)

  toseq : ∀ {p q r : Mode} {A1 : Tp r} {α1 : r ≥ p} {A : Tp q} {α : q ≥ p} 
        → A1 [ α1 ]⊢ A [ α ]
        → A1 [ α1 ]⊢ F α A
  toseq v = FR 1m 1⇒ hyp
  toseq {α1 = α1} {α = α} (Nat {α = α2} e D) = cut {α = 1m} (toseq D) (FL {α = α2} {β = 1m} (FR 1m e hyp))
  toseq {A1 = A1} {α1 = α1} (LetFunc {C = C} {A2 = A2} {α2 = α2} α {γ = γ} D D₁) = cut {α = 1m} have2 (FL {α = α2 ∘1 α} {β = 1m} have1') where
    have1 : A2 [ α2 ]⊢ F γ C
    have1 = toseq D₁

    have1' : A2 [ α2 ∘1 α ]⊢ F (γ ∘1 α) C
    have1' = cut have1 (FL {α = γ} {β = α} (FR 1m 1⇒ hyp))

    have2 : A1 [ α1 ]⊢ F (α2 ∘1 α) A2
    have2 = toseq D
  toseq (FE {β = β} {α = α} D) = cut {α = 1m} (toseq D) (FL {α = β} {β = 1m} (FL {α = α} {β = β ∘1 1m} (FR 1m 1⇒ hyp)))
  toseq (FI {β = β} {α = α} D) = cut {α = 1m} (toseq D) (FL {α = α ∘1 β} {β = 1m} (FR α 1⇒ (FR 1m 1⇒ hyp)))

  fromseq : ∀ {p r : Mode} {A1 : Tp r} {α1 : r ≥ p} {A : Tp p} 
          → A1 [ α1 ]⊢ A
          → A1 [ α1 ]⊢ A [ 1m ]
  fromseq (hypp x) = Nat x v
  fromseq (hypq x) = Nat x v
  fromseq (FL D) = subst (FE v) (fromseq D)
  fromseq {α1 = α1} (FR {α = α} γ e D) = FI {β = 1m} {α = α} (LetFunc α (Nat e v) (fromseq D))


  data _≈'_ {p0 p : Mode} {A0 : Tp p0} {α0 : p0 ≥ p} : {q : Mode} {A : Tp q} {α : q ≥ p} → (D1 D2 : A0 [ α0 ]⊢ A [ α ]) → Set where
    -- FIXME: congruence rules
    id  : ∀ {q : Mode} {A2 : Tp q} {α2 : q ≥ p}
        → {D : A0 [ α0 ]⊢ A2 [ α2 ]}
        → D ≈' D
    !≈' : ∀ {q : Mode} {A2 : Tp q} {α2 : q ≥ p}
        → {D D' : A0 [ α0 ]⊢ A2 [ α2 ]}
        → D ≈' D'
        → D' ≈' D
    _∘≈'_ : ∀ {q : Mode} {A2 : Tp q} {α2 : q ≥ p}
        → {D1 D2 D3 : A0 [ α0 ]⊢ A2 [ α2 ]}
        → D2 ≈' D3
        → D1 ≈' D2 
        → D1 ≈' D3
    Nat≈ : {q : Mode} {A : Tp q} {α α' : q ≥ p} 
        → (e : α' ⇒ α) → {D D' : A0 [ α0 ]⊢ A [ α ] }
        → D ≈' D' → Nat e D ≈' Nat e D
    LetFunc≈ : {q r s : Mode} {C : Tp r} {A2 : Tp s} {α2 : s ≥ q} (α : q ≥ p) {γ : r ≥ q}
            → {D1 D2 : A0 [ α0 ]⊢ A2 [ α2 ∘1 α ]} → {E1 E2 : A2 [ α2 ]⊢ C [ γ ] }
            → D1 ≈' D2 → E1 ≈' E2 → LetFunc α D1 E1 ≈' LetFunc α D2 E2 
    FE≈ : {q r : Mode} {A : Tp r} {β : q ≥ p} {α : r ≥ q} 
      → {D1 D2 : A0 [ α0 ]⊢ F α A [ β ]}
      → D1 ≈' D2 
      → FE D1 ≈' FE D2 
    FI≈ : {q r : Mode} {A : Tp r} {β : q ≥ p} {α : r ≥ q}
         {D1 D2 : A0 [ α0 ]⊢ A [ α ∘1 β ]}
         → D1 ≈' D2
         → (FI D1) ≈' (FI D2)

    Fβ : {q r : Mode} {A : Tp r} {β : q ≥ p} {α : r ≥ q}
         (D : A0 [ α0 ]⊢ A [ α ∘1 β ])
         → FE (FI D) ≈' D
    Fη' : {q r : Mode} {A : Tp r} {β : q ≥ p} {α : r ≥ q} 
         (D : A0 [ α0 ]⊢ F α A [ β ]) → 
         FI (FE D) ≈' D
    NatNat : ∀ {q} {A : Tp q} {α α₁ : q ≥ p}
               {e : α ⇒ α₁} {α₂ : q ≥ p} {e₁ : α₁ ⇒ α₂} {D : A0 [ α0 ]⊢ A [ α₂ ]} →
               (Nat e (Nat e₁ D)) ≈' Nat (e ·2 e₁) D
    Nat1 : {q : Mode} {A : Tp q} {α : q ≥ p} 
         → (D : A0 [ α0 ]⊢ A [ α ] )
         → Nat 1⇒ D ≈' D
    NatFI : ∀ {q} {α α₁ : q ≥ p} {e : α ⇒ α₁} {r}
            {A : Tp r} {α₂ : r ≥ q} {D : A0 [ α0 ]⊢ A [ α₂ ∘1 α₁ ]} →
            (Nat e (FI D)) ≈' FI (Nat (1⇒ ∘1cong e) D)
    NatFE : ∀ {q} {A : Tp q} {α : q ≥ p} {q₁}
            {β β' : q₁ ≥ p} {α₁ α₁' : q ≥ q₁} {e₁ : α₁' ⇒ α₁} {e : β' ⇒ β}
            {D : A0 [ α0 ]⊢ F α₁ A [ β ]} →
            (Nat (e₁ ∘1cong e) (FE D)) ≈' Nat (e₁ ∘1cong 1⇒) (FE (Nat e D))
    NatLetFunc : ∀ {q q2} {A : Tp q} {α : q ≥ p} {q₁}
               {A2 : Tp q2} {α2 : q2 ≥ q₁} {α₁ α₁' : q₁ ≥ p} {γ γ' : q ≥ q₁} {e : γ' ⇒ γ} {e₁ : α₁' ⇒ α₁}
               {θ : A0 [ α0 ]⊢ A2 [ α2 ∘1 α₁ ]}
               {D : A2 [ α2 ]⊢ A [ γ ]} → 
               (Nat (e ∘1cong e₁) (LetFunc α₁ θ D)) ≈' (LetFunc α₁' (Nat (1⇒ ∘1cong e₁) θ) (Nat e D))
    LetFuncCompose : {q r s t : Mode} {C : Tp r} (α : q ≥ p) {γ : r ≥ q} 
                   → {A2 : Tp t} {α2 : t ≥ q} {A3 : Tp s} {α3 : s ≥ q} → (D :  A0 [ α0 ]⊢ A2 [ α2 ∘1 α ]) 
                   → (E1 :  A2 [ α2 ]⊢ A3 [ α3 ]) 
                   → (E2 :  A3 [ α3 ]⊢ C [ γ ]) 
                   → LetFunc α (LetFunc α D E1) E2 ≈' LetFunc α D (subst E1 E2)
    LetFuncIdent : {q t : Mode} {α : q ≥ p} 
                   → {A2 : Tp t} {α2 : t ≥ q} → {D :  A0 [ α0 ]⊢ A2 [ α2 ∘1 α ]}
                   → (LetFunc α D v) ≈' D

                
  fromseq-hyp : ∀ {p  : Mode} (A : Tp p) → fromseq (ident A) ≈' v
  fromseq-hyp P = Nat1 v
  fromseq-hyp Q = Nat1 v
  fromseq-hyp (F α A) = Fη' v ∘≈' FI≈  {β = 1m}{α = α}(LetFuncIdent {α0 = 1m} {α = α}{α2 = 1m} {D = FE v} ∘≈' LetFunc≈ {α0 = 1m} α {D1 = Nat 1⇒ (FE v)} {D2 = FE v} {E1 = fromseq (ident A)} {E2 = v} (Nat1 _) (fromseq-hyp A)) 

  fromseq≈ : ∀ {p r : Mode} {A1 : Tp r} {α1 : r ≥ p} {A : Tp p} 
           {D D' : A1 [ α1 ]⊢ A}
           → D ≈ D' → fromseq D ≈' fromseq D'
  fromseq≈ id = {!!}
  fromseq≈ (eq ∘≈ eq₁) = {!!}
  fromseq≈ (!≈ eq) = {!!}
  fromseq≈ (FL≈ eq) = {!!}
  fromseq≈ (FR≈ eq) = {!!}
  fromseq≈ (Fη D) = {!!}
  fromseq≈ {α1 = α1} (FR2 {α = α} γ2 e2 eq) = FI≈ {!!}
