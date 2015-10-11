
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


{-
  data _≈_ {p : Mode} {Γ : Ctx p} : {q : Mode} {A : Tp q} {α : q ≥ p} → (D1 D2 : Γ ⊢ A [ α ]) → Set where
    -- FIXME: congruence rules

    Fβ : {q r : Mode} {A : Tp r} {β : q ≥ p} {α : r ≥ q}
         (D : Γ ⊢ A [ α ∘1 β ])
         → FE (FI D) ≈ D
    Fη : {q r : Mode} {A : Tp r} {β : q ≥ p} {α : r ≥ q} 
         (D : Γ ⊢ F α A [ β ]) → 
         FI (FE D) ≈ D
    ⊃β : {A B : Tp p} (D : (Γ , A [ 1m ]) ⊢ B [ 1m ]) (E : Γ ⊢ A [ 1m ])
       → App (Lam D) E ≈ LetFunc (Γ , A [ 1m ]) 1m (1s ,, E) D
    NatNat : ∀ {q} {A : Tp q} {α α₁ : q ≥ p}
               {e : α ⇒ α₁} {α₂ : q ≥ p} {e₁ : α₁ ⇒ α₂} {D : Γ ⊢ A [ α₂ ]} →
               (Nat e (Nat e₁ D)) ≈ Nat (e ·2 e₁) D
    Nat1 : {q : Mode} {A : Tp q} {α : q ≥ p} 
         → (D : Γ ⊢ A [ α ] )
         → Nat 1⇒ D ≈ D
    NatFI : ∀ {q} {α α₁ : q ≥ p} {e : α ⇒ α₁} {r}
            {A : Tp r} {α₂ : r ≥ q} {D : Γ ⊢ A [ α₂ ∘1 α₁ ]} →
            (Nat e (FI D)) ≈ FI (Nat (1⇒ ∘1cong e) D)
    NatFE : ∀ {q} {A : Tp q} {α : q ≥ p} {q₁}
            {β β' : q₁ ≥ p} {α₁ α₁' : q ≥ q₁} {e₁ : α₁' ⇒ α₁} {e : β' ⇒ β}
            {D : Γ ⊢ F α₁ A [ β ]} →
            (Nat (e₁ ∘1cong e) (FE D)) ≈ Nat (e₁ ∘1cong 1⇒) (FE (Nat e D))
    NatLetFunc : ∀ {q} {A : Tp q} {α : q ≥ p} {q₁}
               {Γ' : Ctx q₁} {α₁ α₁' : q₁ ≥ p} {γ γ' : q ≥ q₁} {e : γ' ⇒ γ} {e₁ : α₁' ⇒ α₁}
               {θ : Γ ⊢ (Γ' ∘c α₁)}
               {D : Γ' ⊢ A [ γ ]} → 
               (Nat (e ∘1cong e₁) (LetFunc Γ' α₁ θ D)) ≈ (LetFunc Γ' α₁' (subst∘c (λ x → Nat (1⇒ ∘1cong e₁) (θ (∈∘ x)))) (Nat e D))

    -- FIXME more general
    LetFuncLetFunc : {q r s : Mode} {C : Tp r} (α : q ≥ p) {γ : r ≥ q} {α1 : s ≥ q} {A : Tp s}
                      {Γ' : Ctx q} {θ : Γ ⊢ (Γ' ∘c α)} 
                      (E : (· , A [ α1 ]) ⊢ C [ γ ]) (D : Γ' ⊢ A [ α1 ])
                   → LetFunc1 α (LetFunc Γ' α θ D) E ≈ LetFunc Γ' α θ {!!}
-}
                
