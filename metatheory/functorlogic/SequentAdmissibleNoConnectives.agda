
-- everything is admissible, but only works because there are no connectives

open import functorlogic.Lib
open import functorlogic.Modes
open import functorlogic.SequentHypOnly

module functorlogic.SequentAdmissibleNoConnectives where

  data _[_]⊢_[_] : {p q r : Mode} → Tp p → p ≥ r → Tp q -> q ≥ r → Set where
    hypp : ∀ {p q} {α β : p ≥ q} → β ⇒ α → P [ α ]⊢ P [ β ]
    hypq : ∀ {p q} {α β : p ≥ q} → β ⇒ α → Q [ α ]⊢ Q [ β ]
    FL : ∀ {p q r s} {α : r ≥ q} {β : q ≥ p} {A : Tp r} {C : Tp s} {γ : s ≥ p} 
       → A [ α ∘1 β ]⊢ C [ γ ]
       → F α A [ β ]⊢ C [ γ ]
    FR : ∀ {p q r s} {α : r ≥ q} {β : q ≥ p} {A : Tp r} {C : Tp s} {γ : s ≥ p} 
       → C [ γ ]⊢ A [ α ∘1 β ]
       → C [ γ ]⊢ F α A [ β ]

  func : ∀ {p q r s : Mode} {A : Tp p} {α : p ≥ r} {B : Tp q} {β : q ≥ r} (γ : r ≥ s)
       → A [ α ]⊢ B [ β ]
       → A [ α ∘1 γ ]⊢ B [ β ∘1 γ ]
  func γ (hypp x) = hypp (x ∘1cong 1⇒)
  func γ (hypq x) = hypq (x ∘1cong 1⇒)
  func γ (FL D) = FL (func γ D)
  func γ (FR D) = FR (func γ D)

  nat : ∀ {p q} {α β : p ≥ q} (A : Tp p) → β ⇒ α → A [ α ]⊢ A [ β ]
  nat P e = hypp e
  nat Q e = hypq e
  nat (F α₁ A) e = FL (FR (nat A (1⇒ ∘1cong e)))

  cut' : ∀ {p q r s : Mode} {A : Tp p} {α : p ≥ s} {B : Tp q} {β : q ≥ s} {C : Tp r} {γ : r ≥ s}
      → A [ α ]⊢ B [ β ]
      → B [ β ]⊢ C [ γ ]
      → A [ α ]⊢ C [ γ ]
  cut' (hypp x) (hypp x₁) = hypp (x₁ ·2 x)
  cut' (hypq x) (hypq x₁) = hypq (x₁ ·2 x)
  cut' D (FR E) = FR (cut' D E)
  cut' (FL D) E = FL (cut' D E)
  cut' (FR D) (FL E) = cut' D E
         
  hyp' : ∀ {p q} {α : p ≥ q} {A : Tp p} → A [ α ]⊢ A [ α ]
  hyp' = nat _ 1⇒

  toseq : ∀ {p q r : Mode} {A : Tp p} {α : p ≥ r} {B : Tp q} {β : q ≥ r}
        → A [ α ]⊢ B [ β ]
        → A [ α ]⊢ F β B
  toseq (hypp x) = FR 1m x hyp
  toseq (hypq x) = FR 1m x hyp
  toseq (FL D) = FL (toseq D)
  toseq (FR D) = cut {α = 1m} (toseq D) (FL {β = 1m} (FR _ 1⇒ (FR 1m 1⇒ hyp))) -- unfuse

  fromseq : ∀ {p r : Mode} {A : Tp p} {α : p ≥ r} {B : Tp r} 
        → A [ α ]⊢ B
        → A [ α ]⊢ B [ 1m ]
  fromseq (hypp x) = hypp x
  fromseq (hypq x) = hypq x
  fromseq (FL D) = FL (fromseq D)
  fromseq {A = A} {α = α} {B = F .α1 B} (FR {α = α1} γ x D) = FR {α = α1} {β = 1m} (cut' (nat _ x) (func α1 (fromseq D)))

  data _≈'_ : ∀ {p q r : Mode} {A : Tp p} {α : p ≥ r} {B : Tp q} {β : q ≥ r} → (D D' : A [ α ]⊢ B [ β ]) → Set where
    -- congruence
    id'  : ∀ {p q r : Mode} {A : Tp p} {α : p ≥ r} {B : Tp q} {β : q ≥ r}
            {D : A [ α ]⊢ B [ β ]} → D ≈' D
    _∘≈'_ :  ∀ {p q r : Mode} {A : Tp p} {α : p ≥ r} {B : Tp q} {β : q ≥ r}
            {D1 D2 D3 : A [ α ]⊢ B [ β ]}
            → D2 ≈' D3 → (D1 ≈' D2) → D1 ≈' D3 
    !≈' : ∀ {p q r : Mode} {A : Tp p} {α : p ≥ r} {B : Tp q} {β : q ≥ r}
           {D1 D2 : A [ α ]⊢ B [ β ]}
           → D1 ≈' D2 → D2 ≈' D1
    FL≈' : ∀ {p q r s} {α : r ≥ q} {β : q ≥ p} {A : Tp r} {C : Tp s} {γ : s ≥ p} 
       → {D D' : A [ α ∘1 β ]⊢ C [ γ ]}
       → D ≈' D' → FL D ≈' FL D'
    FR≈' : ∀ {p q r s} {α : r ≥ q} {β : q ≥ p} {A : Tp r} {C : Tp s} {γ : s ≥ p} 
       → {D D' : C [ γ ]⊢ A [ α ∘1 β ]}
       → D ≈' D' → FR D ≈' FR D' 
    Fη' : ∀ {p q r s} {α : q ≥ p} {β : p ≥ r} {A : Tp q} {C : Tp s} {γ : s ≥ r}
         (D : F α A [ β ]⊢ C [ γ ]) → 
         D ≈' FL (cut' (FR hyp') D)

    -- -- properties of the functor assigning morphisms between adjunctions

    -- FR2 : ∀ {p q r} {α : q ≥ p} {β : r ≥ p} {A : Tp q} {C : Tp r}
    --      → {γ γ' : r ≥ q} → {e : (γ ∘1 α) ⇒ β} {e' : (γ' ∘1 α) ⇒ β } {D : C [ γ ]⊢ A}  {D' : C [ γ' ]⊢ A} 
    --      → (γ2 : γ' ⇒ γ) (e2 : ((γ2 ∘1cong 1⇒) ·2 e) == e') (D2 : D ≈ transport⊢ γ2 D')
    --      → FR γ e D ≈ FR γ' e' D' 


  eq' : ∀ {p q r : Mode} {A : Tp p} {α : p ≥ r} {B : Tp q} {β : q ≥ r} {D D' : A [ α ]⊢ B [ β ]}
         → D == D' → D ≈' D'
  eq' id = id'

  fromseq≈-cut : ∀ {p q r} {α : q ≥ p} {β : r ≥ q} {A : Tp r} {B : Tp q} {C : Tp p}
               (D : A [ β ]⊢ B)
               (E : B [ α ]⊢ C)
               → fromseq (cut D E) ≈' cut' (func α (fromseq D)) (fromseq E)
  fromseq≈-cut (hypp x) (hypp x₁) = eq' (ap hypp (interchange {e1 = 1⇒} {e2 = x} {f1 = x₁} {f2 = 1⇒})) 
  fromseq≈-cut (hypq x) (hypq x₁) = eq' (ap hypq (interchange {e1 = 1⇒} {e2 = x} {f1 = x₁} {f2 = 1⇒})) 
  fromseq≈-cut (hypp x) (FR γ x₁ E) = {!!}
  fromseq≈-cut (hypq x) (FR γ x₁ E) = {!!}
  fromseq≈-cut (FL D) (hypp x) = {!!}
  fromseq≈-cut (FL D) (hypq x) = {!!}
  fromseq≈-cut (FL D) (FL E) = {!!}
  fromseq≈-cut (FL D) (FR γ x E) = {!!}
  fromseq≈-cut (FR γ x D) (FL E) = {!!}
  fromseq≈-cut (FR γ x D) (FR γ₁ x₁ E) = {!!}


  fromseq≈ : ∀ {p r : Mode} {A : Tp p} {α : p ≥ r} {B : Tp r} {D D' : A [ α ]⊢ B} 
           → D ≈ D'
           → (fromseq D) ≈' (fromseq D')
  fromseq≈ id = id'
  fromseq≈ (eq ∘≈ eq₁) = fromseq≈ eq ∘≈' fromseq≈ eq₁
  fromseq≈ (!≈ eq) = !≈' (fromseq≈ eq)
  fromseq≈ (FL≈ eq) = FL≈' (fromseq≈ eq)
  fromseq≈ (FR≈ eq) = {!!} -- FR≈' (Cut≈' id' (Func≈' _ (fromseq≈ eq)))
  fromseq≈ (Fη D) = {!!} -- FL≈' (!≈' (fromseq≈-cut (FR 1m 1⇒ hyp) D) ∘≈' Cut≈' {!!} id') ∘≈' Fη' (fromseq D)
  fromseq≈ (FR2 γ2 e2 eq) = {!!}
