

open import functorlogic.Lib
open import functorlogic.Modes

module functorlogic.NDHypOnly-OneVar where

  data Tp : Mode → Set where
    P : ∀ {m} → Tp m
    Q : ∀ {m} → Tp m
    F : ∀ {p q} (α : q ≥ p) → Tp q → Tp p
    _⊕_ : ∀ {p} (A B : Tp p) → Tp p

  data _[_]⊢_ : {p q : Mode} → Tp q → q ≥ p → Tp p -> Set where
    var : ∀ {p} {A : Tp p} {α : p ≥ p} → 1m ⇒ α → A [ α ]⊢ A
    FE : ∀ {p q r s} {α : r ≥ s} {β : s ≥ q} {γ : p ≥ s} {γ' : p ≥ q} {A : Tp r} {C : Tp p} {B : Tp q}
       → (γ ∘1 β) ⇒ γ'
       → C [ γ ]⊢ F α A 
       → A [ α ∘1 β ]⊢ B 
       → C [ γ' ]⊢ B
    FI : ∀ {p q r} {α : q ≥ p} {β : r ≥ p} {A : Tp q} {C : Tp r}
       → (γ : r ≥ q) → (γ ∘1 α) ⇒ β
       → C [ γ ]⊢ A
       → C [ β ]⊢ F α A
    Inl : ∀ {p q} {α : q ≥ p} {C : Tp q} {A B : Tp p} → C [ α ]⊢ A → C [ α ]⊢ (A ⊕ B)
    Inr : ∀ {p q} {α : q ≥ p} {C : Tp q} {A B : Tp p} → C [ α ]⊢ B → C [ α ]⊢ (A ⊕ B)
    Case : ∀ {p q} {D : Tp q} {δ : q ≥ p} {C : Tp p} {A B : Tp p} 
                 → D [ δ ]⊢ (A ⊕ B)
                 → A [ 1m ]⊢ C 
                 → B [ 1m ]⊢ C
                 → D [ δ ]⊢ C

  transport⊢ : {p q : Mode} → {A : Tp q} → {β β' : q ≥ p} {B : Tp p} 
             → β ⇒ β'
             → A [ β ]⊢ B 
             → A [ β' ]⊢ B 
  transport⊢ e (var e') = var (e' ·2 e)
  transport⊢ e (FE e' D E) = FE (e' ·2 e) D E
  transport⊢ e (FI γ e' D) = FI γ (e' ·2 e) D 
  transport⊢ e (Inl D) = Inl (transport⊢ e D)
  transport⊢ e (Inr D) = Inr (transport⊢ e D)
  transport⊢ e (Case D D1 D2) = Case (transport⊢ e D) D1 D2

  subst : ∀ {p q r} {α : q ≥ p} {β : r ≥ q} {A : Tp r} {B : Tp q} {C : Tp p}
      → A [ β ]⊢ B
      → B [ α ]⊢ C
      → A [ β ∘1 α ]⊢ C
  subst D (var e) = transport⊢ (1⇒ ∘1cong e) D
  subst {β = β'} D (FE {α = α} {β = β} {γ = γ} e E E₁) = FE {α = α} {β = β} {γ = β' ∘1 γ} (1⇒ ∘1cong e) (subst D E) E₁
  subst {β = β} D (FI γ e E) = FI (β ∘1 γ) (1⇒ ∘1cong e) (subst D E)
  subst D (Inl E) = Inl (subst D E)
  subst D (Inr E) = Inr (subst D E)
  subst D₁ (Case E E₁ E₂) = Case (subst D₁ E) E₁ E₂

  -- β reductions type check
  reduce : ∀ {p q} {α : q ≥ p} {A : Tp q} {B : Tp p} → A [ α ]⊢ B → A [ α ]⊢ B 
  reduce (FE e (FI γ e' D) D₁) = transport⊢ ((e' ∘1cong 1⇒) ·2 e) (subst D D₁) 
  reduce (Case (Inl D₁) D₂ D₃) = subst D₁ D₂
  reduce (Case (Inr D₁) D₂ D₃) = subst D₁ D₃
  reduce D = D

  F∘1 : ∀ {p q r : Mode} {A : Tp r} {α : r ≥ q} {β : q ≥ p}
      → (F β (F α A)) [ 1m ]⊢ F (α ∘1 β) A
  F∘1 = FE {β = 1m}{γ = 1m} 1⇒ (var 1⇒) (FE {γ = 1m} 1⇒ (var 1⇒) (FI 1m 1⇒ (var 1⇒)))

  F∘2 : ∀ {p q r : Mode} {A : Tp r} {α : r ≥ q} {β : q ≥ p}
      → F (α ∘1 β) A [ 1m ]⊢ (F β (F α A))
  F∘2 = FE {β = 1m} {γ = 1m} 1⇒ (var 1⇒) (FI _ 1⇒ (FI 1m 1⇒ (var 1⇒)))

  
