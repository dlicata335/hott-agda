

open import functorlogic.Lib

module functorlogic.Rules where

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
    ∘1cong-unit-l : {x z : Mode} {q q' : x ≥ z} (β : q ⇒ q') → (1⇒ {_}{_}{1m} ∘1cong β) == β
    ∘1cong-unit-r : {x z : Mode} {q q' : x ≥ z} (β : q ⇒ q') → (β ∘1cong 1⇒ {_}{_}{1m} ) == β
    -- FIXME: doesn't always seem to be working as a rewrite
    ∘1cong-assoc : {x y z w : Mode} {p p' : x ≥ y} {q q' : y ≥ z} {r r' : z ≥ w} {e1 : p ⇒ p'} {e2 : q ⇒ q'} {e3 : r ⇒ r'} 
                 → ((e1 ∘1cong e2) ∘1cong e3) == (e1 ∘1cong (e2 ∘1cong e3))
    ·2-unit-r : {x y : Mode} {p q : x ≥ y} (α : p ⇒ q) → (α ·2 1⇒) == α
    ·2-unit-l : {x y : Mode} {p q : x ≥ y} (α : p ⇒ q) → (1⇒ ·2 α) == α
    ·2-assoc  : ∀ {x y : Mode} {α β γ δ : x ≥ y} {e1 : α ⇒ β} {e2 : β ⇒ γ} {e3 : γ ⇒ δ}
              → ((e1 ·2 e2) ·2 e3) == (e1 ·2 (e2 ·2 e3))
    interchange : {x y z : Mode} {p1 p2 p3 : x ≥ y} {e1 : p1 ⇒ p2} {e2 : p2 ⇒ p3}
                  {q1 q2 q3 : y ≥ z} {f1 : q1 ⇒ q2} {f2 : q2 ⇒ q3}
                → ((e1 ·2 e2) ∘1cong (f1 ·2 f2))  == ((e1 ∘1cong f1) ·2 (e2 ∘1cong f2))
    -- FIXME: shouldn't this be provable from the others?
    ·1cong-1⇒ : {x y z : Mode} {p : z ≥ y} {q : y ≥ x} → (1⇒ {_}{_}{p} ∘1cong 1⇒ {_}{_}{q}) == 1⇒

  {-# REWRITE ∘1cong-unit-l #-}
  {-# REWRITE ∘1cong-unit-r #-}
  {-# REWRITE ·2-unit-r #-}
  {-# REWRITE ·2-unit-l #-}
  {-# REWRITE ·1cong-1⇒ #-}
  {-# REWRITE ·2-assoc #-}
  {-# REWRITE ∘1cong-assoc #-}
  
  data Tp : Mode → Set where
    P : ∀ {m} → Tp m
    Q : ∀ {m} → Tp m
    F : ∀ {p q} (α : q ≥ p) → Tp p → Tp q
    _⊕_ : ∀ {p} (A B : Tp p) → Tp p

  data _[_]⊢_[_] : {p q r : Mode} → Tp p → r ≥ p → Tp q -> r ≥ q → Set where
    hypp : ∀ {p q} {α β : q ≥ p} → α ⇒ β → P [ α ]⊢ P [ β ]
    hypq : ∀ {p q} {α β : q ≥ p} → α ⇒ β → Q [ α ]⊢ Q [ β ]
    FL : ∀ {p q r s } {α : q ≥ p} {β : r ≥ q} {γ : r ≥ s} {A : Tp p} {C : Tp s}
        → A [ β ∘1 α ]⊢ C [ γ ]
        → F α A [ β ]⊢ C [ γ ]
    FR : ∀ {p q r s } {α : q ≥ p} {β : r ≥ q} {γ : r ≥ s} {A : Tp p} {C : Tp s}
        → C [ γ ]⊢ A [ β ∘1 α ]
        → C [ γ ]⊢ (F α A) [ β ]
    Inl : ∀ {p q r} {β1 β2 : r ≥ q} {γ : q ≥ p} (e : β1 ⇒ β2) {C : Tp p} {A B : Tp q} → C [ γ ]⊢ A [ 1m ] → C [ β1 ∘1 γ ]⊢ (A ⊕ B) [ β2 ]
    Inr : ∀ {p q} {β1 β2 : q ≥ p} (e : β1 ⇒ β2) {C : Tp p} {A B : Tp p} → C [ 1m ]⊢ B [ 1m ] → C [ β1 ]⊢ (A ⊕ B) [ β2 ]
    Case : ∀ {p q} {β1 β2 : q ≥ p} (e : β1 ⇒ β2) {C : Tp p} {A B : Tp p} → A [ 1m ]⊢ C [ 1m ] → B [ 1m ]⊢ C [ 1m ] → (A ⊕ B) [ β1 ]⊢ C [ β2 ]

  -- compose : ∀ {p q} {β1 β2 : q ≥ p} (A : Tp p) (e : β1 ⇒ β2) → A [ β1 ]⊢ A [ β2 ]
  -- compose P e = hypp e
  -- compose Q e = hypq e
  -- compose (F α A) e = FL (FR (compose A (e ∘1cong 1⇒)))
  -- compose (A ⊕ B) e = Case e (Inl 1⇒ (compose A 1⇒)) (Inr 1⇒ (compose B 1⇒))

  compose' : ∀ {p1 p2 q r} {β1 : r ≥ q} {β2 : r ≥ q} {α1 : q ≥ p1} {α2 : q ≥ p2} 
             {A : Tp p1} {B : Tp p2} (e : β1 ⇒ β2) → A [ α1 ]⊢ B [ α2 ] → A [ β1 ∘1 α1 ]⊢ B [ β2 ∘1 α2 ]
  compose' e (hypp e') = hypp (e ∘1cong e')
  compose' e (hypq e') = hypq (e ∘1cong e')
  compose' {β1 = β1} {α1 = α1} e (FL {α = α} D) = FL {α = α} {β = β1 ∘1 α1} (compose' e D)
  compose' {β2 = β2} {α2 = α2} e (FR {α = α} D) = FR {α = α} {β = β2 ∘1 α2} (compose' e D)
  compose' e (Inl e₁ D) = Inl (e ∘1cong e₁) D
  compose' e (Inr e₁ D) = Inr (e ∘1cong e₁) D
  compose' e (Case e₁ D D₁) = Case (e ∘1cong e₁) D D₁

  ident : ∀ {p} (A : Tp p) → A [ 1m ]⊢ A [ 1m ]
  ident P = hypp 1⇒
  ident Q = hypq 1⇒
  ident (F α A) = FL (FR (compose' 1⇒ (ident A)))
  ident (A ⊕ B) = Case 1⇒ (Inl 1⇒ (ident A)) (Inr 1⇒ (ident B))

  cut : ∀ {p q r s} {α : s ≥ p} {β : s ≥ q} {γ : s ≥ r} {A : Tp p} {B : Tp q} {C : Tp r}
      → A [ α ]⊢ B [ β ]
      → B [ β ]⊢ C [ γ ]
      → A [ α ]⊢ C [ γ ]
  -- -- atom
  cut (hypp e1) (hypp e2) = hypp (e1 ·2 e2)
  cut (hypq e1) (hypq e2) = hypq (e1 ·2 e2)
  -- principal 
  cut (FR D) (FL E) = cut D E
  cut (Inl e D) (Case e2 E1 E2) = compose' (e ·2 e2) (cut D E1)
  cut (Inr e D) (Case e2 E1 E2) = compose' (e ·2 e2) (cut D E2)
  -- right commutative
  cut D (FR E) = FR (cut D E)
  cut D (Inl e E) = {!cut D E!}
  cut D (Inr e E) = {!!}
  -- left commutative
  cut (FL D) E = FL (cut D E)
  cut (Case e D1 D2) E = {!!}

  -- infixr 10 _≈_

  -- data _≈_ : ∀ {p q} {α : p ≥ q} {A : Tp p} {B : Tp q} (D1 D2 : A [ α ]⊢ B) → Set where

  --   -- congruence
  --   id  : ∀ {p q} {α : p ≥ q} {A : Tp p} {B : Tp q} {D1 : A [ α ]⊢ B} → D1 ≈ D1
  --   _∘≈_ : ∀ {p q} {α : p ≥ q} {A : Tp p} {B : Tp q} {D1 D2 D3 : A [ α ]⊢ B} 
  --        → D2 ≈ D3 → (D1 ≈ D2) → D1 ≈ D3 
  --   !≈ : ∀ {p q} {α : p ≥ q} {A : Tp p} {B : Tp q} {D1 D2 : A [ α ]⊢ B} 
  --        → D1 ≈ D2 → D2 ≈ D1
  --   FL≈ : ∀ {p q r} {α : q ≥ p} {β : p ≥ r} {A : Tp q} {C : Tp r}
  --      → {D1 D2 : A [ α ∘1 β ]⊢ C} → D1 ≈ D2 → FL D1 ≈ FL D2
  --   FR≈ : ∀ {p q r} {α : q ≥ p} {β : r ≥ p} {A : Tp q} {C : Tp r}
  --      → {γ : r ≥ q} {e : (γ ∘1 α) ⇒ β}
  --      → {D1 D2 : C [ γ ]⊢ A} → D1 ≈ D2 → FR γ e D1 ≈ FR γ e D2
  --   UL≈ : ∀ {p q r} {α : p ≥ q} {β : p ≥ r} {A : Tp q} {C : Tp r}
  --      → {γ : q ≥ r} {e : (α ∘1 γ) ⇒ β}
  --         {D1 D2 : A [ γ ]⊢ C} → D1 ≈ D2 → UL γ e D1 ≈ UL γ e D2
  --   UR≈ : ∀ {p q r} {α : p ≥ q} {β : r ≥ p} {A : Tp q} {C : Tp r}
  --         {D1 D2 : C [ β ∘1 α ]⊢ A} → D1 ≈ D2 → UR D1 ≈ UR D2
  --   Inl≈ : ∀ {p q} {α : q ≥ p} {C : Tp q} {A B : Tp p} {D1 D2 : C [ α ]⊢ A} → D1 ≈ D2 → Inl{B = B} D1 ≈ Inl D2
  --   Inr≈ : ∀ {p q} {α : q ≥ p} {C : Tp q} {A B : Tp p} {D1 D2 : C [ α ]⊢ B} → D1 ≈ D2 → Inr{A = A} D1 ≈ Inr D2
  --   Case≈ : ∀ {p q} {α : q ≥ p} {C : Tp p} {A B : Tp q} {D1 D2 : A [ α ]⊢ C} {E1 E2 : B [ α ]⊢ C}
  --          → D1 ≈ D2 → E1 ≈ E2 → (Case D1 E1) ≈ (Case D2 E2)

  --   -- the η rules could maybe be made to hold on the nose 
  --   -- with focusing
  --   Fη : ∀ {p q r} {α : q ≥ p} {β : p ≥ r} {A : Tp q} {C : Tp r}
  --        (D : F α A [ β ]⊢ C) → 
  --        D ≈ FL (cut {α = β} {β = α} (FR {α = α} {β = 1m ∘1 α} 1m 1⇒ hyp) D) 

  --   Uη : ∀ {p q r} {α : p ≥ q} {β : q ≥ r} {A : Tp p} {C : Tp r}
  --        (D : A [ α ]⊢ U β C) → 
  --        D ≈ UR (cut D (UL 1m 1⇒ hyp))

  --   ⊕η : ∀ {p q} {α : p ≥ q} {A B : Tp p} {C : Tp q} (D : (A ⊕ B) [ α ]⊢ C) 
  --      → D ≈ Case (cut (Inl hyp) D) (cut (Inr hyp) D)

  --   -- properties of the functor assigning morphisms between adjunctions

  --   FR2 : ∀ {p q r} {α : q ≥ p} {β : r ≥ p} {A : Tp q} {C : Tp r}
  --        → {γ γ' : r ≥ q} → {e : (γ ∘1 α) ⇒ β} {e' : (γ' ∘1 α) ⇒ β } {D : C [ γ ]⊢ A}  {D' : C [ γ' ]⊢ A} 
  --        → (γ2 : γ' ⇒ γ) (e2 : ((γ2 ∘1cong 1⇒) ·2 e) == e') (D2 : D ≈ transport⊢ γ2 D')
  --        → FR γ e D ≈ FR γ' e' D' 

  --   UL2 : ∀ {p q r} {α : p ≥ r} {β : p ≥ q} {A : Tp q} {C : Tp r}
  --        → {γ γ' : r ≥ q} → {e : (α ∘1 γ) ⇒ β } {e' : (α ∘1 γ') ⇒ β } {D : C [ γ ]⊢ A}  {D' : C [ γ' ]⊢ A} 
  --        → (γ2 : γ' ⇒ γ) (e2 : ((1⇒ ∘1cong γ2) ·2 e) == e') (D2 : D ≈ transport⊢ γ2  D')
  --        → UL γ e D ≈ UL γ' e' D' 

  --   -- order of left vs right focus doesn't matter 

  --   commuteULFR : ∀ {p q r s} {A : Tp q} {C : Tp r}
  --                  {α : q ≥ p} {β : r ≥ p} {γ : r ≥ q} {δ1 : s ≥ r} {δ2 : s ≥ p} {δ3 : s ≥ q} 
  --                  {e1 : (γ ∘1 α) ⇒ β} {e2 : (δ1 ∘1 β) ⇒ δ2}
  --                  {e3 : (δ1 ∘1 γ) ⇒ δ3} {e4 : (δ3 ∘1 α) ⇒ δ2} 
  --                  (D : C [ γ ]⊢ A)
  --               → ((1⇒ ∘1cong e1) ·2 e2) == ((e3 ∘1cong 1⇒) ·2 e4)
  --               → UL β e2 (FR γ e1 D) ≈ (FR δ3 e4 (UL γ e3 D))

  --   commuteULInl : ∀ {p q r} {α : p ≥ q} {β : p ≥ r} {A : Tp q} {C C' : Tp r}
  --                  → {γ : q ≥ r} {e : (α ∘1 γ) ⇒ β} (D : A [ γ ]⊢ C)
  --                  → Inl {B = C'} (UL γ e D) ≈ UL γ e (Inl D)

  --   commuteULInr : ∀ {p q r} {α : p ≥ q} {β : p ≥ r} {A : Tp q} {C C' : Tp r}
  --                  → {γ : q ≥ r} {e : (α ∘1 γ) ⇒ β} (D : A [ γ ]⊢ C)
  --                  → Inr {A = C'} (UL γ e D) ≈ UL γ e (Inr  D)

  -- infixr 10 _∘≈_ 

  -- eq : ∀ {p q} {α : p ≥ q} {A : Tp p} {B : Tp q} {D1 D2 : A [ α ]⊢ B} → D1 == D2 → D1 ≈ D2
  -- eq id = id

  -- UL≈' : ∀ {p q r} {α : p ≥ q} {β : p ≥ r} {A : Tp q} {C : Tp r}
  --      → {γ : q ≥ r} {e1 e2 : (α ∘1 γ) ⇒ β}
  --         {D1 D2 : A [ γ ]⊢ C} → e1 == e2 → D1 ≈ D2 → UL γ e1 D1 ≈ UL γ e2 D2
  -- UL≈' id q = UL≈ q 

  -- FR≈' : ∀ {p q r} {α : q ≥ p} {β : r ≥ p} {A : Tp q} {C : Tp r}
  --      → {γ : r ≥ q} {e1 e2 : (γ ∘1 α) ⇒ β}
  --      → {D1 D2 : C [ γ ]⊢ A} → e1 == e2 → D1 ≈ D2 → FR γ e1 D1 ≈ FR γ e2 D2
  -- FR≈' id q = FR≈ q



  -- -- HACK: for some reason the rewrites only work if we define this in this file
  -- -- Be sure to only use one of these at once!

  -- module Reflection where
  --   postulate
  --     c : Mode
  --     s : Mode
  --     ∇m : c ≥ s
  --     Δm : s ≥ c
  --     Δ∇identity : _==_ {s ≥ s} (Δm ∘1 ∇m) (1m {s}) 
  --     ∇Δunit   : 1m ⇒ (∇m ∘1 Δm)
  
  --   {-# REWRITE Δ∇identity #-}
  
  --   Δ∇identity-prefix : ∀ {m} {α : s ≥ m} → (Δm ∘1 (∇m ∘1 α)) == α
  --   Δ∇identity-prefix {α = α} = ap (λ x → x ∘1 α) Δ∇identity ∘ ! (∘1-assoc {α = Δm} {∇m} {α}) 
  
  --   -- otherwise right-associating makes things get stuck sometimes;
  --   -- no idea if this makes sense or not as a rewriting theory
  --   {-# REWRITE Δ∇identity-prefix #-}

  -- module IdempotentMonad where
  --   postulate
  --     c : Mode
  --     r : c ≥ c
  --     ridentity : _==_ {c ≥ c} (r ∘1 r) r
  --     runit   : 1m ⇒ r
  
  --   {-# REWRITE ridentity #-}
  
  --   ridentity-prefix : {α : c ≥ c} → (r ∘1 (r ∘1 α)) == (r ∘1 α)
  --   ridentity-prefix {α = α} = ! (∘1-assoc {α = r} {r} {α}) 
  
  --   {-# REWRITE ridentity-prefix #-}

  --   -- It's necessary to make Mode a postulated type (rather than a parameter to this module) 
  --   -- in order to use the rewrite stuff to get associativity, etc. definitionally.
  --   -- Because of that, we can't instantiate Mode with a datatype for specific theories,
  --   -- which is what we really want here, so that we can analyze all possible 0,1,2-cells.
  --   -- I'm working around that by adding the relevant elimination principles as postulates.
  
  --   postulate
  --     -- the only 0-cell is c
  --     0-cell-case : {m : Mode} → m == c
  --     0-cell-case-c : _==_ {_==_ {Mode} c c } (0-cell-case {c}) (id {_}{c})
      
  --     -- the only 1-cells are 1 and r
  --     1-cell-case   : ∀ (α : c ≥ c) → Either (α == 1m) (α == r)
  --     1-cell-case-1 : _==_ {Either (_==_ {c ≥ c} (1m{c}) (1m{c})) (_==_ { c ≥ c } (1m{c}) r)} (1-cell-case 1m) (Inl id)
  --     1-cell-case-r : _==_ {Either (_==_ {c ≥ c} r (1m{c})) (_==_ { c ≥ c } r r)} (1-cell-case r) (Inr id)
      
  --     1≠r : {C : Set} → 1m == r → C
    
  --     r⇒/1 : ∀ {C : Set} → r ⇒ 1m → C

  --     2-cell-case-loop : ∀ {α : c ≥ c} (e : α ⇒ α) → e == 1⇒
  --     2-cell-case1r : ∀ (e : 1m{c} ⇒ r) → e == runit

  --   {-# REWRITE 0-cell-case-c #-}
  --   {-# REWRITE 1-cell-case-1 #-}
  --   {-# REWRITE 1-cell-case-r #-}

  
  -- module Directed where
  --   -- walking coreflection
  --   postulate
  --     g : Mode
  --     c : Mode
  --     corem : g ≥ c
  --     locm : c ≥ g
  --     coreloc : _==_ { g ≥ g} (corem ∘1 locm) (1m{g})
  --     lccounit : (locm ∘1 corem) ⇒ 1m

  --     opm : c ≥ c
  --     opinvol : _==_ {c ≥ c} (opm ∘1 opm) (1m{c})

  --     opcore : _==_ {g ≥ c} (corem ∘1 opm) (corem)
  --     oploc : _==_ {c ≥ g} (opm ∘1 locm) (locm)

  --   {-# REWRITE coreloc #-}
  --   {-# REWRITE opinvol #-}
  --   {-# REWRITE opcore #-}
  --   {-# REWRITE oploc #-}
  
  --   coreloc-prefix : {m : Mode} {α : g ≥ m} → (corem ∘1 (locm ∘1 α)) == α
  --   coreloc-prefix {α = α} = ! (∘1-assoc {α = corem} { locm } {α}) 

  --   opinvol-prefix : {m : Mode} {α : c ≥ m} → (opm ∘1 (opm ∘1 α)) == α
  --   opinvol-prefix {α = α} = ! (∘1-assoc {α = opm} { opm } {α}) 

  --   {-# REWRITE coreloc-prefix #-}
  --   {-# REWRITE opinvol-prefix #-}
