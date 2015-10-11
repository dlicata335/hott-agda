
-- functoriality as a rule

open import functorlogic.Lib
open import functorlogic.Modes
open import functorlogic.SequentHypOnly

module functorlogic.Sequent2 where

  data _[_]⊢_[_] : {p q r : Mode} → Tp p → p ≥ r → Tp q -> q ≥ r → Set where
    hypp : ∀ {p q} {α β : p ≥ q} → β ⇒ α → P [ α ]⊢ P [ β ]
    hypq : ∀ {p q} {α β : p ≥ q} → β ⇒ α → Q [ α ]⊢ Q [ β ]
    FL : ∀ {p q r s} {α : r ≥ q} {β : q ≥ p} {A : Tp r} {C : Tp s} {γ : s ≥ p} 
       → A [ α ∘1 β ]⊢ C [ γ ]
       → F α A [ β ]⊢ C [ γ ]
    FR : ∀ {p q r s} {α : r ≥ q} {β : q ≥ p} {A : Tp r} {C : Tp s} {γ : s ≥ p} 
       → C [ γ ]⊢ A [ α ∘1 β ]
       → C [ γ ]⊢ F α A [ β ]
    Func : ∀ {p q r s : Mode} {A : Tp p} {α : p ≥ r} {B : Tp q} {β : q ≥ r} {γ : r ≥ s} {α' : p ≥ s}
       → (e : (α ∘1 γ) ⇒ α')
       → A [ α ]⊢ B [ β ]
       → A [ α' ]⊢ B [ β ∘1 γ ]

  toseq : ∀ {p q r : Mode} {A : Tp p} {α : p ≥ r} {B : Tp q} {β : q ≥ r}
        → A [ α ]⊢ B [ β ]
        → A [ α ]⊢ F β B
  toseq (hypp x) = FR 1m x hyp
  toseq (hypq x) = FR 1m x hyp
  toseq (FL D) = FL (toseq D)
  toseq (FR D) = cut {α = 1m} (toseq D) (FL {β = 1m} (FR _ 1⇒ (FR 1m 1⇒ hyp))) -- unfuse
  toseq (Func {β = β} {γ = γ} e D) = transport⊢ e (cut (toseq D) (FL {α = β} {β = γ} (FR 1m 1⇒ hyp))) -- fuse

  fromseq : ∀ {p r : Mode} {A : Tp p} {α : p ≥ r} {B : Tp r} 
        → A [ α ]⊢ B
        → A [ α ]⊢ B [ 1m ]
  fromseq (hypp x) = hypp x
  fromseq (hypq x) = hypq x
  fromseq (FL D) = FL (fromseq D)
  fromseq {A = A} {α = α} {B = F .α1 B} (FR {α = α1} γ x D) = FR {α = α1} {β = 1m} (Func {γ = α1} x (fromseq D)) 

  nat : ∀ {p q} {α β : p ≥ q} (A : Tp p) → β ⇒ α → A [ α ]⊢ A [ β ]
  nat P e = hypp e
  nat Q e = hypq e
  nat (F α₁ A) e = FL (FR (nat A (1⇒ ∘1cong e)))
         
  hyp' : ∀ {p q} {α : p ≥ q} {A : Tp p} → A [ α ]⊢ A [ α ]
  hyp' = nat _ 1⇒

  cutroundabout : ∀ {p q r s : Mode} {A : Tp p} {α : p ≥ s} {B : Tp q} {β : q ≥ s} {C : Tp r} {γ : r ≥ s}
                → A [ α ]⊢ B [ β ]
                → B [ β ]⊢ C [ γ ]
                → A [ α ]⊢ F γ C [ 1m ]
  cutroundabout {A = A} {α} {B} {β} {C} {γ} D E = fromseq (cut thing1 thing2) where
    thing1 : A [ α ]⊢ F β B
    thing1 = toseq D
    
    thing2 : F β B [ 1m ]⊢ F γ C
    thing2 = FL {β = 1m} (toseq E)

  unFR : ∀ {p r s t : Mode} {A : Tp p} {α : p ≥ s} {C : Tp r} {γ : r ≥ t} {β : t ≥ s}
         → A [ α ]⊢ F γ C [ β ]
         → A [ α ]⊢ C [ γ ∘1 β ]
  unFR (FL D) = FL (unFR D)
  unFR (FR D) = D
  unFR (Func {γ = γ1} e D) = Func {γ = γ1} e (unFR D)

  unFL : ∀ {p r s t : Mode} {A : Tp p} {α : t ≥ s} {C : Tp r} {γ : p ≥ t} {β : r ≥ s}
         → F γ A [ α ]⊢ C [ β ]
         → A [ γ ∘1 α ]⊢ C [ β ]
  unFL (FL D) = D
  unFL (FR D) = FR (unFL D)
  unFL  {γ = γ1} (Func {α = α} {β = β} {γ = γ} e D) = Func {α = γ1 ∘1 α} {β = β} {γ = γ} (1⇒ ∘1cong e) (unFL D)

  cutexists : ∀ {p q r s : Mode} {A : Tp p} {α : p ≥ s} {B : Tp q} {β : q ≥ s} {C : Tp r} {γ : r ≥ s}
                → A [ α ]⊢ B [ β ]
                → B [ β ]⊢ C [ γ ]
                → A [ α ]⊢ C [ γ ]
  cutexists D E = unFR (cutroundabout D E)

  natr : ∀ {p q s : Mode} {A : Tp p} {α : p ≥ s} {B : Tp q} {β β' : q ≥ s} (e : β' ⇒ β)
                → A [ α ]⊢ B [ β ]
                → A [ α ]⊢ B [ β' ]
  natr e (hypp x) = hypp (e ·2 x)
  natr e (hypq x) = hypq (e ·2 x)
  natr e (FL D) = FL (natr e D)
  natr e (FR D) = FR (natr (1⇒ ∘1cong e) D)
  natr e (Func e₁ D) = {!!}

  cut' : ∀ {p q r s : Mode} {A : Tp p} {α : p ≥ s} {B : Tp q} {β : q ≥ s} {C : Tp r} {γ : r ≥ s}
       → A [ α ]⊢ B [ β ]
       → B [ β ]⊢ C [ γ ]
       → A [ α ]⊢ C [ γ ]
  -- atom
  cut' (hypp e1) (hypp e2) = hypp (e2 ·2 e1)
  cut' (hypq e1) (hypq e2) = hypq (e2 ·2 e1)
  -- principal
  cut' (FR D) (FL E) = cut' D E
  -- right commutative
  cut' {β = β} D (FR E) = FR (cut' D E)
  -- left commutative
  cut' {β = β} (FL D) E = FL (cut' D E)
  cut' (hypp x) (Func e E) = Func (e ·2 x) E
  cut' (hypq x) (Func e E) = Func (e ·2 x) E
  cut' (FR D) (Func e E) = cut' D (unFL (Func e E))
  cut' (Func e D) (hypp x) = natr x (Func e D) 
  cut' (Func e D) (hypq x) = natr x (Func e D)
  cut' (Func e D) (FL E) = cut' (unFR (Func e D)) E
  cut' (Func {α = α} {β = β} {γ = γ} e D) (Func {α = α'} {β = β'} {γ = γ'} e' E) = {!natr e' (Func {α = α} {β = β} {γ = γ} e D)!}
              

{-
  cut' : ∀ {p q r s t : Mode} {A : Tp p} {α : p ≥ q} {B : Tp t} {β : q ≥ s} {C : Tp r} {γ : r ≥ s} {β' : t ≥ q} {comp : t ≥ s}
         → A [ α ]⊢ B [ β' ]
         → comp == (β' ∘1 β)
         → B [ comp ]⊢ C [ γ ]
         → A [ α ∘1 β ]⊢ C [ γ ]
  -- atom
  cut' (hypp e1) eq (hypp e2) with eq 
  ... | id = hypp (e2 ·2 (e1 ∘1cong 1⇒))
  cut' (hypq e1) eq (hypq e2) with eq
  ... | id = hypq (e2 ·2 (e1 ∘1cong 1⇒))
  -- principal
  cut' (FR D) eq (FL E) with eq
  ... | id = cut' D id E
  -- right commutative
  cut' {β = β} D eq (FR E) with eq 
  ... | id = FR (cut' D id E)
  -- left commutative
  cut' {β = β} (FL D) eq E with eq 
  ... | id = FL (cut' D id E)
  cut' (hypp x) eq (Func E) = {!!}
  cut' (hypq x) eq (Func E) = {!!}
  cut' (FR D) eq (Func E) = {!!}
  cut' (Func D) eq (hypp x) = {!!}
  cut' (Func D) eq (hypq x) = {!!}
  cut' (Func D) eq (FL E) = {!!}
  cut' (Func D) eq (Func E) = {!!}
-}
{-
  cut' : ∀ {p q r s : Mode} {A : Tp p} {α : p ≥ q} {B : Tp q} {β : q ≥ s} {C : Tp r} {γ : r ≥ s} {one : q ≥ q}
         → A [ α ]⊢ B [ one ]
         → one == 1m
         → B [ β ]⊢ C [ γ ]
         → A [ α ∘1 β ]⊢ C [ γ ]
  -- atom
  cut' (hypp p₁) id (hypp q) = hypp (p₁ ∘1cong q)
  cut' (hypq p) id (hypq q) = hypq (p ∘1cong q)
  -- principal 
  cut' (FR D) id (FL E) = {!!}
  -- right commutative
  cut' {β = β} D eq (FR E) with eq 
  ... | id = FR (cut' D id E)
  -- left commutative
  cut' {α = β'} {β = β} (FL {α = α} D) eq E = FL (cut' D eq E)
  cut' (hypp x) id (Func E) = {!Func E!}
  cut' (hypq x) id (Func E) = {!!}
  cut' (FR D) id (Func E) = {!!}
  cut' (Func D) eq (hypp x) = {!!}
  cut' (Func D) eq (hypq x) = {!!}
  cut' (Func D) eq (FL E) = {!!}
  cut' (Func D) eq (Func E) = {!!}
-}

{-
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

  cut' : ∀ {p q r} {α : q ≥ p} {β : r ≥ q} {A : Tp r} {B : Tp q} {C : Tp p}
      → A [ β ]⊢ B
      → B [ α ]⊢ C
      → A [ β ∘1 α ]⊢ C
  -- atom
  cut' (hypp p) (hypp q) = hypp (p ∘1cong q)
  cut' (hypq p) (hypq q) = hypq (p ∘1cong q)
  -- principal 
  cut' (FR γ e D) (FL {α = α} E) = transport⊢ (e ∘1cong 1⇒) (cut' D E)
  -- right commutative
  cut' {β = β} D (FR  γ e E) = FR (β ∘1 γ) (1⇒ ∘1cong e) (cut' D E)
  -- left commutative
  cut' {α = β'} {β = β} (FL {α = α} D) E = FL {α = α} {β = β ∘1 β'} (cut' D E)

-}
