

open import functorlogic.Lib
open import functorlogic.Modes

module functorlogic.NDBI-2 where

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

  infix 12 _⇉_

  data _⇉_ : ∀ {p} → Ctx p → Ctx p → Set where
    id⇉  : ∀ {p} {Γ : Ctx p} → Γ ⇉ Γ
    _·⇉_ : ∀ {p} {Γ1 Γ2 Γ3 : Ctx p} → Γ1 ⇉ Γ2 → Γ2 ⇉ Γ3 → Γ1 ⇉ Γ3
    fuse : ∀ {p q r} {Γ : Ctx r} (α : r ≥ q) (β : q ≥ p)
         → (Γ [ α ]) [ β ] ⇉ Γ [ α ∘1 β ]
    unfuse : ∀ {p q r} {Γ : Ctx r} (α : r ≥ q) (β : q ≥ p)
           → Γ [ α ∘1 β ] ⇉ (Γ [ α ]) [ β ]
    [1] : ∀ {p} {Γ : Ctx p} → Γ ⇉ Γ [ 1m ]
    ![1] : ∀ {p} {Γ : Ctx p} → Γ [ 1m ] ⇉ Γ 
    nt : ∀ {p q} {Γ Δ : Ctx q} {α β : q ≥ p} (e : β ⇒ α) → Γ ⇉ Δ → Γ [ α ] ⇉ Δ [ β ]
    _,⇉_ : ∀ {p} {Γ1 Γ2 Δ1 Δ2 : Ctx p} 
           → Γ1 ⇉ Δ1
           → Γ2 ⇉ Δ2 
           → (Γ1 , Γ2) ⇉ (Δ1 , Δ2)
    ·unitl : ∀ {p} {Γ : Ctx p} → (· , Γ) ⇉ Γ 
    !·unitl : ∀ {p} {Γ : Ctx p} → Γ ⇉ (· , Γ)
    -- can add other structural properties

  data _⊢_ : {p : Mode} → Ctx p → Tp p -> Set where
    var : ∀ {p} {A : Tp p} → (▸ A) ⊢ A
    FE : ∀ {p q r} {Γ : Ctx p} {Γ1 : Ctx p} {Γ2 : Ctx r} {α : q ≥ r} {β : r ≥ p} {A : Tp q} {C : Tp p}
       → (s : Γ ⇉ Γ1 , Γ2 [ β ])
         → Γ2 ⊢ F α A 
       → (Γ1 , ((▸ A) [ α ∘1 β ])) ⊢ C
       → Γ ⊢ C
    FI : ∀ {p q} → {Γ : Ctx p} {Γ' : Ctx q} {A : Tp q} {α : q ≥ p}
       → Γ ⇉ Γ' [ α ] 
       → Γ' ⊢ A
       → Γ ⊢ F α A
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
    subst· : ∀ {p} {Γ : Ctx p} → Γ ⇉ · → Γ ⊢s ·
    subst▸ : ∀  {p} {Γ : Ctx p} {A} → Γ ⊢ A → Γ ⊢s (▸ A)
    subst, : ∀ {p} {Γ : Ctx p} {Γ1 Γ2 Δ1 Δ2} →
              Γ ⇉ Γ1 , Γ2
           → Γ1 ⊢s Δ1
           → Γ2 ⊢s Δ2  
           → Γ ⊢s (Δ1 , Δ2)
    subst[] : {p q : Mode} {Γ : Ctx p} → {Γ1 Γ2 : Ctx q} {α : q ≥ p} → Γ ⇉ Γ1 [ α ] → Γ1 ⊢s Γ2 → Γ ⊢s Γ2 [ α ]

  ids : {p : _} (Γ : Ctx p) → Γ ⊢s Γ
  ids · = subst· id⇉
  ids (▸ A) = subst▸ var
  ids (Γ , Δ) = subst, id⇉ (ids Γ) (ids Δ)
  ids (Γ [ α ]) = subst[] id⇉ (ids Γ)

  invert, : ∀ {p} {Δ Γ : Ctx p} {Γ1 Γ2 : Ctx p} 
     → (s : Γ ⇉ Γ1 , Γ2)
     → (θ : Δ ⊢s Γ)
     → Σ \ (Δ1 : _) → Σ \ (Δ2 : _) → Δ ⇉ Δ1 , Δ2 × (Δ1 ⊢s Γ1) × (Δ2 ⊢s Γ2)
  invert, s θ = {!θ!}

  invert[] : ∀ {p q} {α : q ≥ p} {Γ' : Ctx q} {Δ Γ : Ctx p}
      → (s : Γ ⇉ Γ' [ α ])
      → (θ : Δ ⊢s Γ)
      → Σ \ (Δ' : _) → Δ ⇉ Δ' [ α ] × Δ' ⊢s Γ'
  invert[] = {!!}

  subst : ∀ {p} {C} {Γ Γ' : Ctx p} → Γ' ⊢ C → Γ ⊢s Γ' → Γ ⊢ C
  subst var (subst▸ D) = D
  subst {Γ = Γ} {Γ'} (FE {α = α} s D E) θ with invert, s θ
  subst (FE {α = α} {β = β} s D E) θ | (Δ1 , (Δ2 , (sΔ , (θ1 , θ2)))) with invert[] id⇉ θ2
  ... | (Δ2' , (sΔ2 , θ2')) = FE (sΔ ·⇉ (id⇉ ,⇉ sΔ2)) (subst D θ2') (subst E (subst, id⇉ θ1 (subst[] id⇉ (subst▸ var))))
  subst (FI ρ D) θ with invert[] ρ θ 
  ... | (Δ' , (sΔ , θ')) = FI sΔ (subst D θ')
  subst (Inl D) θ = Inl (subst D θ)
  subst (Inr D) θ = Inr (subst D θ)
  subst (Case s D D₁ D₂) θ with invert, s θ
  subst (Case s D D₁ D₂) θ | (Δ1 , (Δ2 , (sΔ , (θ1 , θ2)))) = Case sΔ (subst D θ2) (subst D₁ (subst, id⇉ θ1 (subst▸ var))) (subst D₂ (subst, id⇉ θ1 (subst▸ var)))
  subst (Lam D) θ = Lam (subst D (subst, id⇉ θ (subst▸ var)))

  -- β steps type check
  reduce : ∀ {p : Mode} {Γ : Ctx p} {A : Tp p} → Γ ⊢ A → Γ ⊢ A
  reduce (FE s (FI ρ E) E₁) = subst E₁ (subst, s (ids _) (subst[] (nt 1⇒ ρ ·⇉ fuse _ _) (subst▸ E))) 
  reduce (Case s (Inl E) E₁ E₂) = subst E₁ (subst, s (ids _) (subst▸ E))
  reduce (Case s (Inr E) E₁ E₂) = subst E₂ (subst, s (ids _) (subst▸ E))
  reduce D = D
  
  F∘1 : ∀ {p q r : Mode} {A : Tp r} {α : r ≥ q} {β : q ≥ p}
      → · ⊢ ((F β (F α A)) ⊸ F (α ∘1 β) A)
  F∘1 = Lam (FE (id⇉ ,⇉ [1]) var (FE id⇉ var (FI ·unitl var))) 

  F∘2 : ∀ {p q r : Mode} {A : Tp r} {α : r ≥ q} {β : q ≥ p}
      → · ⊢ (F (α ∘1 β) A ⊸ (F β (F α A)) )
  F∘2 {A = A}{α = α}{β} = Lam (FE {Γ1 = ·} {Γ2 = ▸ (F (α ∘1 β) A)} {β = 1m} (id⇉ ,⇉ [1]) var (FI (·unitl ·⇉ unfuse α β) (FI id⇉ var)))
