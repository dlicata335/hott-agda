

open import adjointlogic.Lib

module adjointlogic.Rules where

  -- use postulates rather than variables so the rewrite mechanism works
  -- don't want a datatype because we don't want elims

  {-# BUILTIN REWRITE _==_ #-}

  postulate
    Mode : Set 

    _≥_ : Mode -> Mode -> Set 
    1m : {m : Mode} → m ≥ m
    _∘1_ : {x y z : Mode} → z ≥ y → y ≥ x → z ≥ x -- function composition order

    ∘1-unit-l : ∀ {x y : Mode} {α : x ≥ y} → (1m ∘1 α) == α
    ∘1-unit-r : ∀ {x y : Mode} {α : x ≥ y} → (α ∘1 1m) == α
    ∘1-assoc  : ∀ {x y z w : Mode} {α : w ≥ z} {β : z ≥ y} {γ : y ≥ x} → ((α ∘1 β) ∘1 γ) == (α ∘1 (β ∘1 γ))

  {-# REWRITE ∘1-unit-l #-}
  {-# REWRITE ∘1-unit-r #-}
  {-# REWRITE ∘1-assoc #-}

  postulate
    ∘1-assoc'  : ∀ {x y z w : Mode} {α : w ≥ z} {β : z ≥ y} {γ : y ≥ x} → (∘1-assoc {α = α} {β} {γ}) == id

  postulate
    _⇒_ : ∀ {p q} → (α β : p ≥ q) → Set 
    1⇒ : ∀ {p q} → {α : p ≥ q} → α ⇒ α
    _·2_ : {x y : Mode} {p q r : x ≥ y} → p ⇒ q → q ⇒ r → p ⇒ r
    _∘1cong_ : {x y z : Mode} {p p' : x ≥ y} {q q' : y ≥ z} → p ⇒ p' → q ⇒ q' → (p ∘1 q) ⇒ (p' ∘1 q')

  1⇒' : ∀ {p q} → {α β : p ≥ q} → α == β -> α ⇒ β
  1⇒' id = 1⇒

  postulate
    ·1cong-unit-l : {x z : Mode} {q q' : x ≥ z} (β : q ⇒ q') → (1⇒ {_}{_}{1m} ∘1cong β) == β
    ·1cong-unit-r : {x z : Mode} {q q' : x ≥ z} (β : q ⇒ q') → (β ∘1cong 1⇒ {_}{_}{1m} ) == β
    ·2-unit-r : {x y : Mode} {p q : x ≥ y} (α : p ⇒ q) → (α ·2 1⇒) == α
    ·2-unit-l : {x y : Mode} {p q : x ≥ y} (α : p ⇒ q) → (1⇒ ·2 α) == α
    ·2-assoc  : ∀ {x y : Mode} {α β γ δ : x ≥ y} {e1 : α ⇒ β} {e2 : β ⇒ γ} {e3 : γ ⇒ δ}
              → ((e1 ·2 e2) ·2 e3) == (e1 ·2 (e2 ·2 e3))
    ·1cong-1⇒ : {x y z : Mode} {p : z ≥ y} {q : y ≥ x} → (1⇒ {_}{_}{p} ∘1cong 1⇒ {_}{_}{q}) == 1⇒
    interchange : {x y z : Mode} {p1 p2 p3 : x ≥ y} {e1 : p1 ⇒ p2} {e2 : p2 ⇒ p3}
                  {q1 q2 q3 : y ≥ z} {f1 : q1 ⇒ q2} {f2 : q2 ⇒ q3}
                → ((e1 ·2 e2) ∘1cong (f1 ·2 f2))  == ((e1 ∘1cong f1) ·2 (e2 ∘1cong f2))
    -- FIXME: doesn't always seem to be working as a rewrite
    ∘1cong-assoc : {x y z w : Mode} {p p' : x ≥ y} {q q' : y ≥ z} {r r' : z ≥ w} {e1 : p ⇒ p'} {e2 : q ⇒ q'} {e3 : r ⇒ r'} 
                   → ((e1 ∘1cong e2) ∘1cong e3) == (e1 ∘1cong (e2 ∘1cong e3))
    -- FIXME more equations on 2-cells?

  {-# REWRITE ·1cong-unit-l #-}
  {-# REWRITE ·1cong-unit-r #-}
  {-# REWRITE ·2-unit-r #-}
  {-# REWRITE ·2-unit-l #-}
  {-# REWRITE ·1cong-1⇒ #-}
  {-# REWRITE ·2-assoc #-}
  {-# REWRITE ∘1cong-assoc #-}
  
  data Tp : Mode → Set where
    P : ∀ {m} → Tp m
    Q : ∀ {m} → Tp m
    F : ∀ {p q} (α : q ≥ p) → Tp q → Tp p
    U : ∀ {p q} (α : q ≥ p) → Tp p → Tp q 
    _⊕_ : ∀ {p} (A B : Tp p) → Tp p

  data _[_]⊢_ : {p q : Mode} → Tp q → q ≥ p → Tp p -> Set where
    hypp : ∀ {p} {α : p ≥ p} → 1m ⇒ α → P [ α ]⊢ P 
    hypq : ∀ {p} {α : p ≥ p} → 1m ⇒ α → Q [ α ]⊢ Q
    FL : ∀ {p q r} {α : q ≥ p} {β : p ≥ r} {A : Tp q} {C : Tp r}
       → A [ α ∘1 β ]⊢ C
       → F α A [ β ]⊢ C
    FR : ∀ {p q r} {α : q ≥ p} {β : r ≥ p} {A : Tp q} {C : Tp r}
       → (γ : r ≥ q) → (γ ∘1 α) ⇒ β
       → C [ γ ]⊢ A
       → C [ β ]⊢ F α A
    UL : ∀ {p q r} {α : p ≥ q} {β : p ≥ r} {A : Tp q} {C : Tp r}
       → (γ : q ≥ r) → (α ∘1 γ) ⇒ β 
       → A [ γ ]⊢ C
       → U α A [ β ]⊢ C
    UR : ∀ {p q r} {α : p ≥ q} {β : r ≥ p} {A : Tp q} {C : Tp r}
       → C [ β ∘1 α ]⊢ A
       → C [ β ]⊢ U α A
    Inl : ∀ {p q} {α : q ≥ p} {C : Tp q} {A B : Tp p} → C [ α ]⊢ A → C [ α ]⊢ (A ⊕ B)
    Inr : ∀ {p q} {α : q ≥ p} {C : Tp q} {A B : Tp p} → C [ α ]⊢ B → C [ α ]⊢ (A ⊕ B)
    Case : ∀ {p q} {α : q ≥ p} {C : Tp p} {A B : Tp q} → A [ α ]⊢ C → B [ α ]⊢ C → (A ⊕ B) [ α ]⊢ C

  transport⊢ : {p q : Mode} → {A : Tp q} → {α β : q ≥ p} {B : Tp p} 
             → α ⇒ β
             → A [ α ]⊢ B 
             → A [ β ]⊢ B 
  transport⊢ e (hypp e') = hypp (e' ·2 e)
  transport⊢ e (hypq e') = hypq (e' ·2 e)
  transport⊢ e (FL D) = FL (transport⊢ (1⇒ ∘1cong e) D)
  transport⊢ e (FR γ e' D) = FR γ (e' ·2 e) D 
  transport⊢ e (UL γ e' D) = UL γ (e' ·2 e) D
  transport⊢ e (UR D) = UR (transport⊢ (e ∘1cong 1⇒) D) 
  transport⊢ e (Inl D) = Inl (transport⊢ e D)
  transport⊢ e (Inr D) = Inr (transport⊢ e D)
  transport⊢ e (Case D1 D2) = Case (transport⊢ e D1) (transport⊢ e D2)

  ident : ∀ {p} (A : Tp p) → A [ 1m ]⊢ A
  ident P = hypp 1⇒
  ident Q = hypq 1⇒
  ident (U α A) = (UR {α = α} {β = 1m} (UL 1m 1⇒ (ident A)))  -- need to annote because it infers the wrong association
  ident (F α A) = FL (FR 1m 1⇒ (ident A)) 
  ident (A ⊕ B) = Case (Inl (ident A)) (Inr (ident B))

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
  cut (FR γ e D) (FL E) = transport⊢ (e ∘1cong 1⇒) (cut D E)
  cut (UR {α = α1} D) (UL γ₁ e E) = transport⊢ (1⇒ ∘1cong e) (cut D E)
  cut (Inl D) (Case E1 E2) = cut D E1
  cut (Inr D) (Case E1 E2) = cut D E2
  -- right commutative
  cut {α = α} {β = β} D (FR {α = α'} γ e E) = FR (β ∘1 γ) (1⇒ ∘1cong e) (cut D E)
  cut {α = α} {β = β} D (UR {α = α1} E) = UR {α = α1} {β = β ∘1 α} (cut D E) 
  cut D (Inl E) = Inl (cut D E) 
  cut D (Inr E) = Inr (cut D E)
  -- left commutative
  cut {α = α} {β = β} (FL {α = α1} D) E = FL {α = α1} {β = β ∘1 α} (cut D E) 
  cut {α = α} (UL γ e D) E = UL (γ ∘1 α) (e ∘1cong 1⇒) (cut D E) 
  cut (Case D1 D2) E = Case (cut D1 E) (cut D2 E)

  -- FIXME: is cut well-defined on these?
  postulate
    -- FIXME: focusing? 
    Fη : ∀ {p q r} {α : q ≥ p} {β : p ≥ r} {A : Tp q} {C : Tp r}
         (D : F α A [ β ]⊢ C) → 
         D == FL (cut {α = β} {β = α} (FR {α = α} {β = 1m ∘1 α} 1m 1⇒ hyp) D) 

    -- FIXME: focusing? 
    Uη : ∀ {p q r} {α : p ≥ q} {β : q ≥ r} {A : Tp p} {C : Tp r}
         (D : A [ α ]⊢ U β C) → 
         D == UR (cut D (UL 1m 1⇒ hyp))

    -- properties of the functor assigning morphisms between adjunctions

    FR2 : ∀ {p q r} {α : q ≥ p} {β : r ≥ p} {A : Tp q} {C : Tp r}
         → {γ γ' : r ≥ q} → {e : (γ ∘1 α) ⇒ β} {e' : (γ' ∘1 α) ⇒ β } {D : C [ γ ]⊢ A}  {D' : C [ γ' ]⊢ A} 
         → (γ2 : γ' ⇒ γ) (e2 : ((γ2 ∘1cong 1⇒) ·2 e) == e') (D2 : D == transport⊢ γ2 D')
         → FR γ e D == FR γ' e' D' 

    UL2 : ∀ {p q r} {α : p ≥ r} {β : p ≥ q} {A : Tp q} {C : Tp r}
         → {γ γ' : r ≥ q} → {e : (α ∘1 γ) ⇒ β } {e' : (α ∘1 γ') ⇒ β } {D : C [ γ ]⊢ A}  {D' : C [ γ' ]⊢ A} 
         → (γ2 : γ' ⇒ γ) (e2 : ((1⇒ ∘1cong γ2) ·2 e) == e') (D2 : D == transport⊢ γ2  D')
         → UL γ e D == UL γ' e' D' 

    -- order of left vs right focus doesn't matter 

    commuteULFR : ∀ {p q r s} {A : Tp q} {C : Tp r}
                   {α : q ≥ p} {β : r ≥ p} {γ : r ≥ q} {δ1 : s ≥ r} {δ2 : s ≥ p} {δ3 : s ≥ q} 
                   {e1 : (γ ∘1 α) ⇒ β} {e2 : (δ1 ∘1 β) ⇒ δ2}
                   {e3 : (δ1 ∘1 γ) ⇒ δ3} {e4 : (δ3 ∘1 α) ⇒ δ2} 
                   (D : C [ γ ]⊢ A)
                → ((1⇒ ∘1cong e1) ·2 e2) == ((e3 ∘1cong 1⇒) ·2 e4)
                → _==_ { U δ1 C [ δ2 ]⊢ F α A } 
                        (UL β e2 (FR γ e1 D))
                        (FR δ3 e4 (UL γ e3 D))

    commuteULInl : ∀ {p q r} {α : p ≥ q} {β : p ≥ r} {A : Tp q} {C C' : Tp r}
                   → {γ : q ≥ r} {e : (α ∘1 γ) ⇒ β} (D : A [ γ ]⊢ C)
                   → Inl {B = C'} (UL γ e D) == UL γ e (Inl D)

    commuteULInr : ∀ {p q r} {α : p ≥ q} {β : p ≥ r} {A : Tp q} {C C' : Tp r}
                   → {γ : q ≥ r} {e : (α ∘1 γ) ⇒ β} (D : A [ γ ]⊢ C)
                   → Inr {A = C'} (UL γ e D) == UL γ e (Inr  D)


  -- HACK: for some reason the rewrites only work if we define this in this file
  module Reflection where
    postulate
      c : Mode
      s : Mode
      ∇m : c ≥ s
      Δm : s ≥ c
      Δ∇identity : _==_ {s ≥ s} (Δm ∘1 ∇m) (1m {s}) 
      ∇Δunit   : 1m ⇒ (∇m ∘1 Δm)
  
    {-# REWRITE Δ∇identity #-}
  
    Δ∇identity-prefix : ∀ {m} {α : s ≥ m} → (Δm ∘1 (∇m ∘1 α)) == α
    Δ∇identity-prefix {α = α} = ap (λ x → x ∘1 α) Δ∇identity ∘ ! (∘1-assoc {α = Δm} {∇m} {α}) 
  
    -- otherwise right-associating makes things get stuck sometimes;
    -- no idea if this makes sense or not as a rewriting theory
    {-# REWRITE Δ∇identity-prefix #-}
  
