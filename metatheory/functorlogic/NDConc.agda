
-- non-normal and definitional equality

open import functorlogic.Lib
open import functorlogic.Modes

module functorlogic.NDConc where

  data Tp : Mode → Set where
    P : ∀ {m} → Tp m
    Q : ∀ {m} → Tp m
    F : ∀ {p q} (α : q ≥ p) → Tp q → Tp p
    _⊃_ : ∀ {p} → Tp p → Tp p → Tp p
    _⊕_ : ∀ {p} → Tp p → Tp p → Tp p

  data Ctx (p : Mode) : Set where
    ·     : Ctx p
    _,_[_] : {q : Mode} → Ctx p → Tp q → q ≥ p → Ctx p

  _∘c_ : ∀ {p q} → Ctx p → p ≥ q → Ctx q
  · ∘c α = ·
  (Γ , A [ α ]) ∘c β = (Γ ∘c β) , A [ α ∘1 β ]

  ∘c-assoc : ∀ {p q r} (Γ : Ctx p) (α : p ≥ q) (β : q ≥ r) 
           → ((Γ ∘c α) ∘c β) == (Γ ∘c (α ∘1 β))
  ∘c-assoc · α β = id
  ∘c-assoc (Γ , A [ α1 ]) α β = ap (λ x → x , _ [ _ ]) (∘c-assoc Γ α β)

  ∘c-ident : ∀ {p} (Γ : Ctx p) → (Γ ∘c 1m) == Γ
  ∘c-ident · = id
  ∘c-ident (Γ , A [ α1 ]) = ap (λ x → x , _ [ _ ]) (∘c-ident Γ)

  -- eh why not... just lifting ∘-assoc to lists
  {-# REWRITE ∘c-assoc #-}
  {-# REWRITE ∘c-ident #-}

  data _[_]∈_ : {q p : Mode} → Tp q → q ≥ p → Ctx p → Set where
    i0 : {p q : Mode} {Γ : Ctx p} {A : Tp q} {α : q ≥ p} → A [ α ]∈ (Γ , A [ α ])
    iS : {p q r : Mode} {Γ : Ctx p} {A : Tp q} {α : q ≥ p} {B : Tp r} {β : r ≥ p}
       → A [ α ]∈ Γ 
       → A [ α ]∈ (Γ , B [ β ])

  ∈∘ : ∀ {p q r} {Γ : Ctx p} {α : p ≥ q}
         {A : Tp r} {β : r ≥ p}
         → A [ β ]∈ Γ → A [ β ∘1 α ]∈ (Γ ∘c α)
  ∈∘ i0 = i0
  ∈∘ (iS i) = iS (∈∘ i)

  _⊇_ : ∀ {p} → Ctx p → Ctx p → Set 
  Γ ⊇ Γ' = {q : Mode} {A : Tp q} {α : q ≥ _} → A [ α ]∈ Γ' → A [ α ]∈ Γ

  ⊇∘c : ∀ {p q} {Γ Γ' : Ctx p} {α : p ≥ q} → Γ ⊇ Γ' → (Γ ∘c α) ⊇ (Γ' ∘c α)
  ⊇∘c {Γ' = ·} w ()
  ⊇∘c {Γ' = Γ' , A [ α ]} w i0 = ∈∘ (w i0)
  ⊇∘c {Γ' = Γ' , A [ α ]} w (iS x) = ⊇∘c {Γ' = Γ'} (λ y → w (iS y)) x

  mutual 
    _⊢_ : {p : Mode} (Γ Γ' : Ctx p) → Set
    Γ ⊢ Γ' =  {q : Mode} {A : Tp q} {α : q ≥ _} → A [ α ]∈ Γ' → Γ ⊢ A [ α ] 

    data _⊢_[_] {p : Mode} (Γ : Ctx p) : {q : Mode} → Tp q -> q ≥ p → Set where
      v : {q : Mode} {A : Tp q} {α : q ≥ p} 
        → A [ α ]∈ Γ 
        → Γ ⊢ A [ α ]
      Nat : {q : Mode} {A : Tp q} {α α' : q ≥ p} 
          → (e : α' ⇒ α) → Γ ⊢ A [ α ] 
          → Γ ⊢ A [ α' ]
      LetFunc : {q r : Mode} {C : Tp r} (Γ' : Ctx q) (α : q ≥ p) {γ : r ≥ q}
              → Γ ⊢ (Γ' ∘c α) → Γ' ⊢ C [ γ ] 
              → Γ ⊢ C [ γ ∘1 α ] 
      FE : {q r : Mode} {A : Tp r} {β : q ≥ p} {α : r ≥ q} 
        → Γ ⊢ F α A [ β ] 
        → Γ ⊢ A [ α ∘1 β ]
      FI : {q r : Mode} {A : Tp r} {β : q ≥ p} {α : r ≥ q}
         → Γ ⊢ A [ α ∘1 β ]
         → Γ ⊢ F α A [ β ]
      Lam : {A B : Tp p}  
          → (Γ , A [ 1m ]) ⊢ B [ 1m ]
          → Γ ⊢ (A ⊃ B) [ 1m ]
      App : {A B : Tp p} 
        → Γ ⊢ (A ⊃ B) [ 1m ]
        → Γ ⊢ A [ 1m ]
        → Γ ⊢ B [ 1m ]
      Inl : {A B : Tp p}  
          → Γ ⊢ A [ 1m ]
          → Γ ⊢ (A ⊕ B) [ 1m ]
      Inr : {A B : Tp p}  
          → Γ ⊢ A [ 1m ]
          → Γ ⊢ (A ⊕ B) [ 1m ]
      Case : {A B : Tp p} {C : Tp p} 
          → Γ ⊢ (A ⊕ B) [ 1m ]
          → Γ , A [ 1m ] ⊢ C [ 1m ]
          → Γ , B [ 1m ] ⊢ C [ 1m ]
          → Γ ⊢ C [ 1m ]

  ·· : ∀ {p} {Γ : Ctx p} → Γ ⊢ · 
  ·· ()

  _,,_ : ∀ {p q} {Γ Γ' : Ctx p} {A : Tp q} {α : q ≥ p} → Γ ⊢ Γ' → Γ ⊢ A [ α ] → Γ ⊢ (Γ' , A [ α ])
  _,,_ θ e i0 = e 
  _,,_ θ e (iS x) = θ x

  1s : ∀ {p : Mode} {Γ : Ctx p} → Γ ⊢ Γ
  1s = {!!}

  subst∘c : ∀ {p q} {Γ : Ctx p} {Γ' : Ctx q} {α : q ≥ p} 
          → ({r : Mode} {A : Tp r} {α1 : r ≥ q} → A [ α1 ]∈ Γ' → Γ ⊢ A [ α1 ∘1 α ])
          → Γ ⊢ (Γ' ∘c α)
  subst∘c {Γ' = ·} θ ()
  subst∘c {Γ' = Γ' , A [ α₁ ]} θ i0 = θ i0
  subst∘c {Γ' = Γ' , A [ α₁ ]} θ (iS x) = subst∘c {Γ' = Γ'} (λ x₁ → θ (iS x₁)) x

  foo : {p : Mode} {Γ : Ctx p} {q : Mode} {A : Tp q} {α : q ≥ p} → (D : Γ ⊢ A [ α ]) → {!!}
  foo (v x) = {!!}
  foo (Nat e (v x)) = {!nothing!}
  foo (Nat e (Nat e₁ D)) = {!commutes!}
  foo (Nat e (LetFunc Γ' α θ D)) = {!commutes!}
  foo (Nat e (FE D)) = {!partial!}
  foo (Nat e (FI D)) = {!commutes!}
  foo (Nat e (Lam D)) = {!nothing!}
  foo (Nat e (App D D₁)) = {!nothing!}
  foo (Nat e (Inl D)) = {!nothing!}
  foo (Nat e (Inr D)) = {!nothing!}
  foo (Nat e (Case D D₁ D₂)) = {!nothing!}
  foo (LetFunc Γ' α x D) = {!!}
  foo (FE D) = {!!}
  foo (FI D) = {!!}
  foo (Lam D) = {!!}
  foo (App D D₁) = {!!}
  foo (Inl D) = {!!}
  foo (Inr D) = {!!}
  foo (Case D D₁ D₂) = {!!}

  LetFunc1 : {p q r s : Mode} {Γ : Ctx p} {C : Tp r} (α : q ≥ p) {γ : r ≥ q} {α1 : s ≥ q} {A : Tp s}
           → Γ ⊢ A [ α1 ∘1 α ] → (· , A [ α1 ]) ⊢ C [ γ ] 
           → Γ ⊢ C [ γ ∘1 α ] 
  LetFunc1 α {α1 = α1} {A = A} D E = LetFunc (· , A [ α1 ]) α (·· ,, D) E

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

  App' : {p q : Mode} {Γ : Ctx p} {A B : Tp q} {α : q ≥ p}
       → Γ ⊢ (A ⊃ B) [ α ]
       → Γ ⊢ A [ α ]
       → Γ ⊢ B [ α ]
  App' {A = A}{B} {α = α} D E = LetFunc ((· , A ⊃ B [ 1m ]) , A [ 1m ]) α ((·· ,, D) ,, E) (App (v (iS i0)) (v i0))

  Case' : {p : Mode} {Γ : Ctx p} {A B : Tp p} {q : Mode} {C : Tp q} {γ : q ≥ p}
          → Γ ⊢ (A ⊕ B) [ 1m ]
          → Γ , A [ 1m ] ⊢ C [ γ ]
          → Γ , B [ 1m ] ⊢ C [ γ ]
          → Γ ⊢ C [ γ ]
  Case' D D1 D2 = FE (Case D (FI {β = 1m} D1) (FI {β = 1m} D2))
                
