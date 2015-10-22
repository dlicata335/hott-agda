

open import functorlogic.Lib
open import functorlogic.Modes

module functorlogic.NDBI where

  data Tp : Mode → Set where
    P : ∀ {m} → Tp m
    Q : ∀ {m} → Tp m
    F : ∀ {p q} (α : q ≥ p) → Tp q → Tp p
    _⊕_ : ∀ {p} (A B : Tp p) → Tp p
    _⊸_ : ∀ {p} (A B : Tp p) → Tp p

  data Ctx (p : Mode) : Set where
    ·   : Ctx p
    ▸   : Tp p → Ctx p
    _,_ : Ctx p → Ctx p → Ctx p
    _[_] : {q : Mode} → Ctx q → (α : q ≥ p) → Ctx p

  data _⇉_,_ : ∀ {p} → Ctx p → Ctx p → Ctx p → Set where
    split, : ∀ {p} {Γ1 Γ2 : Ctx p} → (Γ1 , Γ2) ⇉ Γ1 , Γ2

  data _⊢_ : {p : Mode} → Ctx p → Tp p -> Set where
    var : ∀ {p} {A : Tp p} → (▸ A) ⊢ A
    FE : ∀ {p q r} {Γ : Ctx p} {Γ1 : Ctx p} {Γ2 : Ctx r} {α : ? ≥ ?} {β : ? ≥ ?} {A : Tp q} {C : Tp p}
       → (s : Γ ⇉ Γ1 , Γ2 [ β ])
       → Γ2 ⊢ F α A 
       → (Γ1 , ((▸ A) [ ? ])) ⊢ C
       → Γ ⊢ C
    -- FIXME stuff might not be admissble
    FI : ∀ {p q} → {Γ : Ctx q} {A : Tp q} {α : q ≥ p}
       → Γ ⊢ A
       → Γ [ α ] ⊢ F α A
    Inl : ∀ {p} → {Γ : Ctx p} {A B : Tp p} 
       → Γ ⊢ A
       → Γ ⊢ (A ⊕ B)
    Inr : ∀ {p} → {Γ : Ctx p} {A B : Tp p} 
       → Γ ⊢ B
       → Γ ⊢ (A ⊕ B)
    Case : ∀ {p} {Γ Γ1 Γ2 : Ctx p} {A B : Tp p} {C : Tp p}
         → (s : Γ ⇉ Γ2 , Γ1)
         → Γ1 ⊢ (A ⊕ B)
         → (Γ2 , ▸ A) ⊢ C 
         → (Γ2 , ▸ B) ⊢ C 
         → Γ ⊢ C 
    Lam : ∀ {p} {Γ : Ctx p} {A B : Tp p}
        → (Γ , ▸ A) ⊢ B
        → Γ ⊢ (A ⊸ B)
    

  data _⊢s_ : {p : _} (Γ : Ctx p) → Ctx p → Set where
    ·      : ∀ {p} → ·{p} ⊢s ·
    ▸      : ∀  {p} {Γ : Ctx p} {A} → Γ ⊢ A → Γ ⊢s (▸ A)
    subst, : ∀ {p} {Γ : Ctx p} {Γ1 Γ2 Δ1 Δ2} →
              Γ ⇉ Γ1 , Γ2
           → Γ1 ⊢s Δ1
           → Γ2 ⊢s Δ2 
           → Γ ⊢s (Δ1 , Δ2)
    _[_] : {p q : Mode} → {Γ1 Γ2 : Ctx q} → Γ1 ⊢s Γ2 → (α : q ≥ p) → Γ1 [ α ] ⊢s Γ2 [ α ]

  ids : {p : _} (Γ : Ctx p) → Γ ⊢s Γ
  ids · = ·
  ids (▸ A) = ▸ var
  ids (Γ , Δ) = subst, split, (ids Γ) (ids Δ)
  ids (Γ [ α ]) = ids Γ [ α ]

  ⇉s : ∀ {p} {Δ Γ : Ctx p} {Γ1 Γ2 : Ctx p} 
     → (s : Γ ⇉ Γ1 , Γ2)
     → (θ : Δ ⊢s Γ)
     → Σ \ (Δ1 : _) → Σ \ (Δ2 : _) → Δ ⇉ Δ1 , Δ2 × (Δ1 ⊢s Γ1) × (Δ2 ⊢s Γ2)
  ⇉s s θ = {!!}

  subst : ∀ {p} {C} {Γ Γ' : Ctx p} → Γ' ⊢ C → Γ ⊢s Γ' → Γ ⊢ C
  subst var (▸ D) = D
  subst (FE {α = α} s D E) θ with ⇉s s θ
  ... | (Δ1 , (Δ2 , (sΔ , (θ1 , θ2)))) = ? -- FE sΔ (subst D θ2) (subst E (subst, split, θ1 (▸ var [ α ])))
  subst (FI D) (θ [ α ]) = FI (subst D θ)
  subst (Inl D) θ = Inl (subst D θ)
  subst (Inr D) θ = Inr (subst D θ)
  subst (Case s D D₁ D₂) θ with ⇉s s θ
  subst (Case s D D₁ D₂) θ | (Δ1 , (Δ2 , (sΔ , (θ1 , θ2)))) = Case sΔ (subst D θ2) (subst D₁ (subst, split, θ1 (▸ var))) (subst D₂ (subst, split, θ1 (▸ var)))
  subst (Lam D) θ = Lam (subst D (subst, split, θ (▸ var)))

  -- β steps type check
  reduce : ∀ {p : Mode} {Γ : Ctx p} {A : Tp p} → Γ ⊢ A → Γ ⊢ A
  reduce (FE s (FI E) E₁) = ? -- subst E₁ (subst, s (ids _) (▸ E [ _ ]))
  reduce (Case s (Inl E) E₁ E₂) = subst E₁ (subst, s (ids _) (▸ E))
  reduce (Case s (Inr E) E₁ E₂) = subst E₂ (subst, s (ids _) (▸ E))
  reduce D = D
  
  F∘1 : ∀ {p q r : Mode} {A : Tp r} {α : r ≥ q} {β : q ≥ p}
      → · ⊢ ((F β (F α A)) ⊸ F (α ∘1 β) A)
  F∘1 = ? -- Lam (FE split, var (FE split, {!!} {!!}))

{-
  transport⊢ : {p q : Mode} → {A : Tp q} → {β β' : q ≥ p} {B : Tp p} 
             → β ⇒ β'
             → A [ β ]⊢ B 
             → A [ β' ]⊢ B 
  transport⊢ e (var e') = var (e' ·2 e)
  transport⊢ e (FE D E) = FE (transport⊢ e D) E
  transport⊢ e (FI γ e' D) = FI γ (e' ·2 e) D 
  transport⊢ e (Inl D) = Inl (transport⊢ e D)
  transport⊢ e (Inr D) = Inr (transport⊢ e D)
  transport⊢ e (Case D D1 D2) = Case (transport⊢ e D) D1 D2

  subst : ∀ {p q r} {α : q ≥ p} {β : r ≥ q} {A : Tp r} {B : Tp q} {C : Tp p}
      → A [ β ]⊢ B
      → B [ α ]⊢ C
      → A [ β ∘1 α ]⊢ C
  subst D (var e) = transport⊢ (1⇒ ∘1cong e) D
  subst D (FE E E₁) = FE (subst D E) E₁
  subst {β = β} D (FI γ e E) = FI (β ∘1 γ) (1⇒ ∘1cong e) (subst D E)
  subst D (Inl E) = Inl (subst D E)
  subst D (Inr E) = Inr (subst D E)
  subst D₁ (Case E E₁ E₂) = Case (subst D₁ E) E₁ E₂

  -- β reductions type check
  reduce : ∀ {p q} {α : q ≥ p} {A : Tp q} {B : Tp p} → A [ α ]⊢ B → A [ α ]⊢ B 
  reduce (FE (FI γ x D) D₁) = transport⊢ x (subst D D₁)
  reduce (Case (Inl D₁) D₂ D₃) = subst D₁ D₂
  reduce (Case (Inr D₁) D₂ D₃) = subst D₁ D₃
  reduce D = D
-}
{-

  data _≈_ : ∀ {p q} {α : p ≥ q} {A : Tp p} {B : Tp q} (D1 D2 : A [ α ]⊢ B) → Set where

    -- congruence
    id  : ∀ {p q} {α : p ≥ q} {A : Tp p} {B : Tp q} {D1 : A [ α ]⊢ B} → D1 ≈ D1
    _∘≈_ : ∀ {p q} {α : p ≥ q} {A : Tp p} {B : Tp q} {D1 D2 D3 : A [ α ]⊢ B} 
         → D2 ≈ D3 → (D1 ≈ D2) → D1 ≈ D3 
    !≈ : ∀ {p q} {α : p ≥ q} {A : Tp p} {B : Tp q} {D1 D2 : A [ α ]⊢ B} 
         → D1 ≈ D2 → D2 ≈ D1
    FL≈ : ∀ {p q r} {α : q ≥ p} {β : p ≥ r} {A : Tp q} {C : Tp r}
       → {D1 D2 : A [ α ∘1 β ]⊢ C} → D1 ≈ D2 → FL D1 ≈ FL D2
    FR≈ : ∀ {p q r} {α : q ≥ p} {β : r ≥ p} {A : Tp q} {C : Tp r}
       → {γ : r ≥ q} {e : (γ ∘1 α) ⇒ β}
       → {D1 D2 : C [ γ ]⊢ A} → D1 ≈ D2 → FR γ e D1 ≈ FR γ e D2

    -- the η rules could maybe be made to hold on the nose 
    -- with focusing
    Fη : ∀ {p q r} {α : q ≥ p} {β : p ≥ r} {A : Tp q} {C : Tp r}
         (D : F α A [ β ]⊢ C) → 
         D ≈ FL (cut {α = β} {β = α} (FR {α = α} {β = 1m ∘1 α} 1m 1⇒ hyp) D) 

    -- properties of the functor assigning morphisms between adjunctions

    FR2 : ∀ {p q r} {α : q ≥ p} {β : r ≥ p} {A : Tp q} {C : Tp r}
         → {γ γ' : r ≥ q} → {e : (γ ∘1 α) ⇒ β} {e' : (γ' ∘1 α) ⇒ β } {D : C [ γ ]⊢ A}  {D' : C [ γ' ]⊢ A} 
         → (γ2 : γ' ⇒ γ) (e2 : ((γ2 ∘1cong 1⇒) ·2 e) == e') (D2 : D ≈ transport⊢ γ2 D')
         → FR γ e D ≈ FR γ' e' D' 

-}
