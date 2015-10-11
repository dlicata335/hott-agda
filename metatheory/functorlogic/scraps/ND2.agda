

open import functorlogic.Lib
open import functorlogic.Modes
open import functorlogic.Sequent

module functorlogic.ND2 where
  
  _≤_ : Mode → Mode → Set
  x ≤ y = y ≥ x

  _⇐_ : ∀ {p q} → (α β : p ≥ q) → Set 
  α ⇐ β = β ⇒ α

  mutual
    data _[_]⇓_[_] : {p q r : Mode} → Tp p → r ≤ p → Tp q -> r ≤ q → Set where
      V  : ∀ {p r : Mode} { A : Tp p} → {α : r ≤ p} → A [ α ]⇓ A [ α ]
      FE : ∀ {p q r s } {α : q ≤ p} {β : r ≤ q} {γ : r ≤ s} {A : Tp p} {C : Tp s}
         → C [ γ ]⇓ F α A [ β ] 
         → C [ γ ]⇓ A [ α ∘1 β ] 

    data _[_]⇑_[_] : {p q r : Mode} → Tp p → r ≤ p → Tp q -> r ≤ q → Set where
      -- could probably be restricted to base types on the right
      Func : ∀ {r s t t'} {α : s ≤ t} {β : s ≤ t'} {γ : r ≤ t} {γ' : r ≤ t'} {δ δ' : s ≤ r}  {A : Tp t} {B : Tp t'}
              → (e1 : α ⇐ (γ ∘1 δ))
              → A [ γ ]⇑ B [ γ' ]
              → (e : δ ⇐ δ') 
              → (e2 : ( γ' ∘1 δ' ) ⇐ β)
              → A [ α ]⇑ B [ β ]
      -- when do we need this?
      Let : ∀ {p q r s : Mode} {A : Tp p} {α : r ≤ p} {B : Tp q} {β : r ≤ q} {C : Tp s} {γ : r ≤ s}
          → A [ α ]⇓ B [ β ]
          → B [ β ]⇑ C [ γ ]
          → A [ α ]⇑ C [ γ ]
      -- only necessary at base type?
      ⇓⇑ : ∀ {p q r : Mode} {A : Tp p} {α : r ≤ p} {B : Tp q} {β : r ≤ q} 
          → A [ α ]⇓ B [ β ]
          → A [ α ]⇑ B [ β ]
      FI : ∀ {p q r s } {α : q ≤ p} {β : r ≤ q} {γ : r ≤ s} {A : Tp p} {C : Tp s}
          → C [ γ ]⇑ A [ α ∘1 β  ]
          → C [ γ ]⇑ (F α A) [ β ]
      -- Inl : ∀ {p q} {C : Tp p} {α : q ≤ p} {A B : Tp q} → C [ α ]⇑ A [ 1m ] → C [ α ]⇑ (A ⊕ B) [ 1m ]
      -- Inr : ∀ {p q} {C : Tp p} {α : q ≤ p} {A B : Tp q} → C [ α ]⇑ B [ 1m ] → C [ α ]⇑ (A ⊕ B) [ 1m ]
      -- Case : ∀ {p q s r} {C : Tp p} {D : Tp r} {δ : s ≤ r} {γ : q ≤ p} {A B : Tp q} 
      --      → D [ δ ]⇓ (A ⊕ B) [ {!!} ]
      --      → A [ 1m ]⇑ C [ γ ]
      --      → B [ 1m ]⇑ C [ γ ]
      --      → D [ δ ]⇑ C [ {!!} ]

  substaa : ∀ {p q r s : Mode} {A : Tp p} {α : r ≤ p} {B : Tp q} {β : r ≤ q} {C : Tp s} {γ : r ≤ s}
          → A [ α ]⇓ B [ β ]
          → B [ β ]⇓ C [ γ ]
          → A [ α ]⇓ C [ γ ]
  substaa D V = D
  substaa D (FE E) = FE (substaa D E)


  {-# NO_TERMINATION_CHECK #-}
  hsubsta : ∀ {p q r s : Mode} {A : Tp p} {α : s ≤ p} {B : Tp q} {β : s ≤ q} {C : Tp r} {γ : s ≤ r}
         → A [ α ]⇑ B [ β ]
         → B [ β ]⇓ C [ γ ]
         → A [ α ]⇑ C [ γ ]
  hsubsta D V = D
  hsubsta D (FE E) with hsubsta D E 
  hsubsta D (FE E) | Func e1 E' e e2 = Func e1 (hsubsta E' (FE V)) e (1⇒ ∘1cong e2)
  hsubsta D (FE E) | Let E1' E2' = Let E1' (hsubsta E2' (FE V))
  hsubsta D (FE E) | ⇓⇑ E' = ⇓⇑ (FE E')
  hsubsta D (FE E) | FI E' = E'

  -- hsubsta : ∀ {p q r s : Mode} {A : Tp p} {α : q ≤ p} {B : Tp q} {β : s ≤ q} {C : Tp r} {γ : s ≤ r}
  --        → A [ α ]⇑ B [ 1m ]
  --        → B [ β ]⇓ C [ γ ]
  --        → A [ α ∘1 β ]⇑ C [ γ ]
  -- hsubsta D V = Func 1⇒ D 1⇒ 1⇒
  -- hsubsta D (FE E) with hsubsta D E
  -- hsubsta D (FE E) | Func e1 D' e e2 = {!!} -- Func e1 (FE D') e (1⇒ ∘1cong e2)
  -- hsubsta D (FE E) | FI E' = E'
  -- hsubsta D (FE E) | Let D1 D2 = {!D2!}
  -- hsubsta D (FE E) | ⇓⇑ D' = ⇓⇑ (FE D')

{-
  hsubst : ∀ {p q r s : Mode} {A : Tp p} {α : q ≤ p} {B : Tp q} {β : s ≤ q} {C : Tp r} {γ : s ≤ r}
         → A [ α ]⇑ B [ 1m ]
         → B [ β ]⇑ C [ γ ]
         → A [ α ∘1 β ]⇑ C [ γ ]
  hsubst {α = α} D (Func {γ = γ}{γ'}{δ}{δ'} e1 E e2 e3) = func {γ = α ∘1 γ}{γ' = γ'} {δ = δ} {δ' = δ'} (1⇒ ∘1cong e1) (hsubsta D E) e2 e3
  hsubst D (FI E) = FI (hsubst D E)


  toseqa : ∀ {p q r : Mode} {A : Tp p} {α : r ≤ p} {B : Tp q} {β : r ≤ q}
         → A [ α ]⇓ B [ β ]
         → A [ α ]⊢ F β B 
  toseqa V = FR 1m 1⇒ (ident _)
  toseqa (FE D) = cut {α = 1m} (toseqa D) (FL (FL (FR 1m 1⇒ hyp))) -- fuse F's

  toseqc : ∀ {p q r : Mode} {A : Tp p} {α : r ≤ p} {B : Tp q} {β : r ≤ q}
         → A [ α ]⇑ B [ β ]
         → A [ α ]⊢ F β B 
  toseqc {A = A} {α = α} {B}  {β = β} (Func {γ = γ}{γ'}{δ}{δ'} e1 D e e2) = cut {α = 1m} step3 (FL {α = γ' ∘1 δ'} {β = 1m} (FR 1m e2 hyp)) where -- natural trans e1
    step1 : A [ γ ∘1 δ ]⊢ F δ' (F γ' B) -- functoriality
    step1 = FR γ (1⇒ ∘1cong e) (toseqa D)

    step2 : A [ α ]⊢ F δ' (F γ' B) -- natural trans e1
    step2 = transport⊢ e1 step1

    step3 : A [ α ]⊢ F (γ' ∘1 δ') B
    step3 = cut {α = 1m} step2 (FL (FL (FR 1m 1⇒ hyp))) -- fusion

  toseqc {α = α} {β = β} (FI {α = α1} D) = cut {α = 1m} (toseqc D) (FL {α = α1 ∘1 β} {β = 1m} (FR α1 1⇒ (FR 1m 1⇒ hyp))) -- unfuse F's

  fromseq : ∀ {p r : Mode} {A : Tp p} {α : r ≤ p} {B : Tp r}
          → A [ α ]⊢ B 
          → A [ α ]⇑ B [ 1m ]
  fromseq (hypp x) = Func {δ = 1m} {δ' = 1m} 1⇒ V 1⇒ x
  fromseq (hypq x) = Func {δ = 1m} {δ' = 1m} 1⇒ V 1⇒ x
  fromseq {A = F .α1 A} {α = α} (FL {α = α1} D) = {! (fromseq D)!} where
    step1 : F α1 A [ α ]⇓ A [ α1 ∘1 α ]
    step1 = FE V

    step2 : F α1 A [ α ]⇑ F (α1 ∘1 α) A [ 1m ]
    step2 = FI {α = α1 ∘1 α} {β = 1m} (Func {δ = 1m} {δ' = 1m} 1⇒ step1 1⇒ 1⇒)

  fromseq {A = A} {α = α} {B = F .α1 B} (FR {α = α1} γ x D) = FI {α = α1} {β = 1m} (func {γ = γ} {γ' = 1m} {δ = α1} {δ' = α1} x (fromseq D) 1⇒ 1⇒)
-}

{-
  -- derivable/admisible

  SimpleFunc : ∀ {r s t t'} {δ δ' : s ≤ r} {γ : r ≤ t} {γ' : r ≤ t'} {A : Tp t} {B : Tp t'}
          → (e : δ ⇒ δ') 
          → A [ γ ]⇓ B [ γ' ]
          → A [ δ ∘1 γ ]⇑ B [ δ' ∘1 γ' ]
  SimpleFunc e D = Func 1⇒ D e 1⇒ 

  Natr : ∀ {p q s} {α α' : q ≤ p} {γ : q ≤ s} {A : Tp p} {C : Tp s}
         → C [ γ ]⇓ A [ α ]
         → (e : α ⇒ α')
         → C [ γ ]⇑ A [ α' ]
  Natr {α = α}{α'}{γ} D e = Func {γ = γ} {γ' = α}  {δ = 1m} {δ' = 1m} 1⇒ D 1⇒ e

  Natl : ∀ {p q s} {α : q ≤ p} {γ γ' : q ≤ s} {A : Tp p} {C : Tp s}
           → C [ γ ]⇓ A [ α ]
           → (e : γ' ⇒ γ)
           → C [ γ' ]⇑ A [ α ]
  Natl {α = α} {γ} {γ'} D e = Func {γ = γ} {γ' = α} {δ = 1m} {δ' = 1m} e D 1⇒ 1⇒

  natr : ∀ {p q s} {α α' : q ≤ p} {γ : q ≤ s} {A : Tp p} {C : Tp s}
           → C [ γ ]⇑ A [ α ]
           → (e : α ⇒ α')
           → C [ γ ]⇑ A [ α' ]
  natr {α = α}{α'}{γ} D e = func {γ = γ} {γ' = α}  {δ = 1m} {δ' = 1m} 1⇒ D 1⇒ e

  natl : ∀ {p q s} {α : q ≤ p} {γ γ' : q ≤ s} {A : Tp p} {C : Tp s}
           → C [ γ ]⇑ A [ α ]
           → (e : γ' ⇒ γ)
           → C [ γ' ]⇑ A [ α ]
  natl {α = α} {γ} {γ'} D e = func {γ = γ} {γ' = α} {δ = 1m} {δ' = 1m} e D 1⇒ 1⇒

  simplefunc : ∀ {r s t t'} {δ δ' : s ≤ r} {γ : r ≤ t} {γ' : r ≤ t'} {A : Tp t} {B : Tp t'}
          → A [ γ ]⇑ B [ γ' ]
          → (e : δ ⇒ δ') 
          → A [ δ ∘1 γ ]⇑ B [ δ' ∘1 γ' ]
  simplefunc D e = func 1⇒ D e 1⇒
-}
