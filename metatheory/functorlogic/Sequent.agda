

open import functorlogic.Lib
open import functorlogic.Modes

module functorlogic.Sequent where

  data Tp : Mode → Set where
    P : ∀ {m} → Tp m
    Q : ∀ {m} → Tp m
    F : ∀ {p q} (α : q ≥ p) → Tp q → Tp p

  data _[_]⊢_ : {p q : Mode} → Tp q → q ≥ p → Tp p -> Set where
    hypp : ∀ {p} {α : p ≥ p} → 1m ⇒ α → P [ α ]⊢ P 
    hypq : ∀ {p} {α : p ≥ p} → 1m ⇒ α → Q [ α ]⊢ Q
    FL : ∀ {p q r} {α : r ≥ q} {β : q ≥ p} {A : Tp r} {C : Tp p}
       → A [ α ∘1 β ]⊢ C
       → F α A [ β ]⊢ C
    FR : ∀ {p q r} {α : q ≥ p} {β : r ≥ p} {A : Tp q} {C : Tp r}
       → (γ : r ≥ q) → (γ ∘1 α) ⇒ β
       → C [ γ ]⊢ A
       → C [ β ]⊢ F α A

  transport⊢ : {p q : Mode} → {A : Tp q} → {β β' : q ≥ p} {B : Tp p} 
             → β ⇒ β'
             → A [ β ]⊢ B 
             → A [ β' ]⊢ B 
  transport⊢ e (hypp e') = hypp (e' ·2 e)
  transport⊢ e (hypq e') = hypq (e' ·2 e)
  transport⊢ e (FL D) = FL (transport⊢ (1⇒ ∘1cong e) D)
  transport⊢ e (FR γ e' D) = FR γ (e' ·2 e) D 

  ident : ∀ {p} (A : Tp p) → A [ 1m ]⊢ A
  ident P = hypp 1⇒
  ident Q = hypq 1⇒
  ident (F α A) = FL (FR 1m 1⇒ (ident A)) 

  hyp : ∀ {p} {A : Tp p} → A [ 1m ]⊢ A
  hyp = ident _ 

  cut : ∀ {p q r} {α : q ≥ p} {β : r ≥ q} {A : Tp r} {B : Tp q} {C : Tp p}
      → A [ β ]⊢ B
      → B [ α ]⊢ C
      → A [ β ∘1 α ]⊢ C
  -- atom
  cut (hypp p) (hypp q) = hypp (p ∘1cong q)
  cut (hypq p) (hypq q) = hypq (p ∘1cong q)
  -- principal 
  cut (FR γ e D) (FL {α = α} E) = transport⊢ (e ∘1cong 1⇒) (cut D E)
  -- right commutative
  cut {β = β} D (FR  γ e E) = FR (β ∘1 γ) (1⇒ ∘1cong e) (cut D E)
  -- left commutative
  cut {α = β'} {β = β} (FL {α = α} D) E = FL {α = α} {β = β ∘1 β'} (cut D E)

