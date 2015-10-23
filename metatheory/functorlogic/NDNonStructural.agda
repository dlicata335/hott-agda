

open import functorlogic.Lib
open import functorlogic.Modes

module functorlogic.NDNonStructural where

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
    contract : ∀ {p q} {Γ : Ctx q} {α : q ≥ p} → Γ [ α ] ⇉ (Γ [ α ] , Γ [ α ])

  data _⊢_ : {p : Mode} → Ctx p → Tp p -> Set where
    var : ∀ {p} {Γ : Ctx p} {A : Tp p} → Γ ⇉ (▸ A) → Γ ⊢ A
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

  rename : ∀ {p} {C} {Γ Γ' : Ctx p} → Γ' ⊢ C → Γ ⇉ Γ' → Γ ⊢ C
  rename (var ρ1) ρ = var (ρ ·⇉ ρ1)
  rename (FE ρ1 D D₁) ρ = FE (ρ ·⇉ ρ1) D D₁
  rename (FI ρ1 D) ρ = FI (ρ ·⇉ ρ1) D
  rename (Inl D) ρ = Inl (rename D ρ)
  rename (Inr D) ρ = Inr (rename D ρ)
  rename (Case ρ1 D D₁ D₂) ρ = Case (ρ ·⇉ ρ1) D D₁ D₂
  rename (Lam D) ρ = Lam (rename D (ρ ,⇉ id⇉))

  data _⊢s_ : {p : _} (Γ : Ctx p) → Ctx p → Set where
    subst· : ∀ {p} {Γ : Ctx p} → Γ ⇉ · → Γ ⊢s ·
    subst▸ : ∀  {p} {Γ : Ctx p} {A} → Γ ⊢ A → Γ ⊢s (▸ A)
    subst, : ∀ {p} {Γ : Ctx p} {Γ1 Γ2 Δ1 Δ2} →
              Γ ⇉ Γ1 , Γ2
           → Γ1 ⊢s Δ1
           → Γ2 ⊢s Δ2  
           → Γ ⊢s (Δ1 , Δ2)
    subst[] : {p q : Mode} {Γ : Ctx p} → {Γ1 Γ2 : Ctx q} {α : q ≥ p} → Γ ⇉ Γ1 [ α ] → Γ1 ⊢s Γ2 → Γ ⊢s Γ2 [ α ]

  _·rs_ : ∀ {p} {Γ1 Γ2 Γ3 : Ctx p} → Γ1 ⇉ Γ2 → Γ2 ⊢s Γ3 → Γ1 ⊢s Γ3
  ρ ·rs subst· ρ' = subst· (ρ ·⇉ ρ')
  ρ ·rs subst▸ D = subst▸ (rename D ρ)
  ρ ·rs subst, ρ' θ θ₁ = subst, (ρ ·⇉ ρ') θ θ₁
  ρ ·rs subst[] ρ' θ = subst[] (ρ ·⇉ ρ') θ

  _·sr_ : ∀ {p} {Γ1 Γ2 Γ3 : Ctx p} → Γ1 ⊢s Γ2 → Γ2 ⇉ Γ3 → Γ1 ⊢s Γ3
  θ ·sr id⇉ = θ
  θ ·sr (ρ ·⇉ ρ₁) = (θ ·sr ρ) ·sr ρ₁
  (subst[] ρ1 (subst[] ρ2 θ)) ·sr (fuse α β) = subst[] (ρ1 ·⇉ (nt 1⇒ ρ2 ·⇉ fuse α β)) θ
  subst[] ρ1 θ ·sr unfuse α β = subst[] (ρ1 ·⇉ unfuse α β) (subst[] id⇉ θ)
  θ ·sr [1] = subst[] [1] θ
  subst[] ρ θ ·sr ![1] = (ρ ·⇉ ![1]) ·rs θ
  subst[] ρ1 θ ·sr nt e ρ = subst[] (ρ1 ·⇉ nt e id⇉) (θ ·sr ρ)
  subst, ρ θ1 θ2 ·sr (ρ1 ,⇉ ρ2) = subst, ρ (θ1 ·sr ρ1) (θ2 ·sr ρ2)
  subst, ρ (subst· ρ1) θ2 ·sr ·unitl = (ρ ·⇉ ((ρ1 ,⇉ id⇉) ·⇉ ·unitl)) ·rs θ2
  θ ·sr !·unitl = subst, !·unitl (subst· id⇉) θ
  subst[] ρ θ ·sr contract = subst, (ρ ·⇉ contract) (subst[] id⇉ θ) (subst[] id⇉ θ)

  ids : {p : _} (Γ : Ctx p) → Γ ⊢s Γ
  ids · = subst· id⇉
  ids (▸ A) = subst▸ (var id⇉)
  ids (Γ , Δ) = subst, id⇉ (ids Γ) (ids Δ)
  ids (Γ [ α ]) = subst[] id⇉ (ids Γ)

  subst : ∀ {p} {C} {Γ Γ' : Ctx p} → Γ' ⊢ C → Γ ⊢s Γ' → Γ ⊢ C
  subst (var ρ) θ with θ ·sr ρ
  ... | subst▸ D = D
  subst {Γ = Γ} {Γ'} (FE {α = α} ρ D E) θ with θ ·sr ρ 
  ... | subst, sΔ θ1 (subst[] sΔ2 θ2') = 
    FE (sΔ ·⇉ (id⇉ ,⇉ sΔ2)) (subst D θ2') (subst E (subst, id⇉ θ1 (subst[] id⇉ (subst▸ (var id⇉)))))
  subst (FI ρ D) θ with θ ·sr ρ
  ... | (subst[] sΔ θ') = FI sΔ (subst D θ')
  subst (Inl D) θ = Inl (subst D θ)
  subst (Inr D) θ = Inr (subst D θ)
  subst (Case ρ D D₁ D₂) θ with θ ·sr ρ
  subst (Case s D D₁ D₂) θ | (subst, sΔ θ1 θ2) = Case sΔ (subst D θ2) (subst D₁ (subst, id⇉ θ1 (subst▸ (var id⇉)))) (subst D₂ (subst, id⇉ θ1 (subst▸ (var id⇉))))
  subst (Lam D) θ = Lam (subst D (subst, id⇉ θ (subst▸ (var id⇉))))

  -- β steps type check
  reduce : ∀ {p : Mode} {Γ : Ctx p} {A : Tp p} → Γ ⊢ A → Γ ⊢ A
  reduce (FE s (FI ρ E) E₁) = subst E₁ (subst, s (ids _) (subst[] (nt 1⇒ ρ ·⇉ fuse _ _) (subst▸ E))) 
  reduce (Case s (Inl E) E₁ E₂) = subst E₁ (subst, s (ids _) (subst▸ E))
  reduce (Case s (Inr E) E₁ E₂) = subst E₂ (subst, s (ids _) (subst▸ E))
  reduce D = D

  -- examples
  
  F∘1 : ∀ {p q r : Mode} {A : Tp r} {α : r ≥ q} {β : q ≥ p}
      → · ⊢ ((F β (F α A)) ⊸ F (α ∘1 β) A)
  F∘1 = Lam (FE (id⇉ ,⇉ [1]) (var id⇉) (FE id⇉ (var id⇉) (FI ·unitl (var id⇉)))) 

  F∘2 : ∀ {p q r : Mode} {A : Tp r} {α : r ≥ q} {β : q ≥ p}
      → · ⊢ (F (α ∘1 β) A ⊸ (F β (F α A)) )
  F∘2 {A = A}{α = α}{β} = Lam (FE {Γ1 = ·} {Γ2 = ▸ (F (α ∘1 β) A)} {β = 1m} (id⇉ ,⇉ [1]) (var id⇉) (FI (·unitl ·⇉ unfuse α β) (FI id⇉ (var id⇉))))

  Fnt : ∀ {p q : Mode} {A : Tp q} {α β : q ≥ p} (e : β ⇒ α)
      → · ⊢ (F α A ⊸ F β A)
  Fnt e = Lam (FE (id⇉ ,⇉ [1]) (var id⇉) (FI (·unitl ·⇉ nt e id⇉) (var id⇉)))

  
