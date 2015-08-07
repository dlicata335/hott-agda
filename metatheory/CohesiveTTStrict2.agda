-- requires Agda 2.4.2.3 or later for the rewrite stuff

open import Agda.Primitive

module metatheory.CohesiveTTStrict2 where

  -- REWRITE seems not to work with type-in-type
  data _==_ {A : Set} (M : A) : A → Set where
    id : M == M

  ap :  {A B : Set} {M N : A}
       (f : A → B) → M == N → (f M) == (f N)
  ap f id = id

  ap2 :  {A B C : Set} {M N : A} {M' N' : B} (f : A -> B -> C) -> M == N -> M' == N' -> (f M M') == (f N N')
  ap2 f id id = id

  ! :  {A : Set} {M N : A} → M == N → N == M
  ! id = id

  _∘_  : {A : Set} {M N P : A} → N == P → M == N → M == P
  β ∘ id = β

  _=〈_〉_ : {A : Set} (x : A) {y z : A} → x == y → y == z → x == z
  _ =〈 p1 〉 p2 = (p2 ∘ p1)
 
  _∎ : ∀ {A : Set} (x : A) → x == x
  _∎ _ = id

  infix  2 _∎
  infixr 2 _=〈_〉_ 

 
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
    ·1cong-1⇒ : {x y z : Mode} {p : z ≥ y} {q : y ≥ x} → (1⇒ {_}{_}{p} ∘1cong 1⇒ {_}{_}{q}) == 1⇒
    -- FIXME more equations on 2-cells?

  {-# REWRITE ·1cong-unit-l #-}
  {-# REWRITE ·1cong-unit-r #-}
  {-# REWRITE ·2-unit-r #-}
  {-# REWRITE ·2-unit-l #-}
  {-# REWRITE ·1cong-1⇒ #-}
  
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

  transport⊢1 : {p q : Mode} → {A : Tp q} → {α : q ≥ p} {B : Tp p} 
               (D : A [ α ]⊢ B)
             → transport⊢ (1⇒ {α = α}) D == D
  transport⊢1 (hypp x) = id
  transport⊢1 (hypq x) = id
  transport⊢1 (FL D) = ap FL (transport⊢1 D)
  transport⊢1 (FR γ x D) = id
  transport⊢1 (UL γ x D) = id
  transport⊢1 (UR D) = ap UR (transport⊢1 D)
  transport⊢1 (Inl D) = ap Inl (transport⊢1 D)
  transport⊢1 (Inr D) = ap Inr (transport⊢1 D)
  transport⊢1 (Case D D₁) = ap2 Case (transport⊢1 D) (transport⊢1 D₁)

  -- seems to only work for 1m
  ident : ∀ {p} (A : Tp p) → A [ 1m ]⊢ A
  ident P = hypp 1⇒
  ident Q = hypq 1⇒
  ident (U α A) = (UR {α = α} {β = 1m} (UL 1m 1⇒ (ident A)))  -- need to annote because it infers the wrong association
  ident (F α A) = FL (FR 1m 1⇒ (ident A)) 
  ident (A ⊕ B) = Case (Inl (ident A)) (Inr (ident B))

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
  cut {α = α} (UL γ e D) E = UL (γ ∘1 α) (e  ∘1cong 1⇒) (cut D E)
  cut (Case D1 D2) E = Case (cut D1 E) (cut D2 E)
    
  -- equations are not defintiional because of matching on two args
  cutFR : ∀ {p q r} {α : q ≥ p} {β : r ≥ q} {A : Tp r} {B : Tp q} {q₁} {α' : q₁ ≥ p} {A₁ : Tp q₁} →
        {D : A [ β ]⊢ B} {γ : q ≥ q₁} {e : (γ ∘1 α') ⇒ α} {E : B [ γ ]⊢ A₁}
        → cut D (FR γ e E) == FR (β ∘1 γ) (1⇒ ∘1cong e) (cut D E)
  cutFR {D = hypp x} = id
  cutFR {D = hypq x} = id
  cutFR {D = FL D} = id
  cutFR {D = FR γ x D} = id
  cutFR {D = UL γ x D} = id
  cutFR {D = UR D} = id
  cutFR {D = Inl D} = id
  cutFR {D = Inr D} = id
  cutFR {D = Case D D₁} = id

  hyp : ∀ {p} {A : Tp p} → A [ 1m ]⊢ A
  hyp = ident _ 

  cut-ident-right : ∀ {p q} {α : q ≥ p} {A B} → (D : A [ α ]⊢ B)
                  → cut D (ident B) == D
  cut-ident-right (hypp x) = id
  cut-ident-right (hypq x) = id
  cut-ident-right (FL D) = {!!}
  cut-ident-right (FR γ x D) = {!!}
  cut-ident-right (UL γ x D) = {!!}
  cut-ident-right (UR D) = ap UR (cut-ident-right D ∘ transport⊢1 _)
  cut-ident-right (Inl D) = {!!}
  cut-ident-right (Inr D) = {!!}
  cut-ident-right (Case D D₁) = {!!}

  cut-ident-left : ∀ {p q} {α : q ≥ p} {A B} → (D : A [ α ]⊢ B)
                  → cut (ident A) D == D
  cut-ident-left (hypp x) = id
  cut-ident-left (hypq x) = id
  cut-ident-left (FL D) = ap FL (cut-ident-left D ∘ transport⊢1 _)
  cut-ident-left {A = A} (FR γ x D) = ap (FR γ x) (cut-ident-left D) ∘ cutFR {D = ident A} {γ = γ} {e = x} {E = D}
  cut-ident-left (UL γ x D) = {!!} ∘ ap (transport⊢ x) {!!}
  cut-ident-left (UR D) = {!!}
  cut-ident-left (Inl D) = {!!}
  cut-ident-left (Inr D) = {!!}
  cut-ident-left (Case D D₁) = ap2 Case (cut-ident-left _) (cut-ident-left _)

  cut-assoc : ∀ {p q r s} {α : p ≥ q} {β : q ≥ r} {γ : r ≥ s} {A : Tp p} {B : Tp q} {C : Tp r} {D : Tp s}
            (D1 : A [ α ]⊢ B) (D2 : B [ β ]⊢ C) (D3 : C [ γ ]⊢ D) →
            cut D1 (cut D2 D3) == cut (cut D1 D2) D3
  cut-assoc = {!!}

  -- FIXME: focusing? 
  postulate
    Fη : ∀ {p q r} {α : q ≥ p} {β : p ≥ r} {A : Tp q} {C : Tp r}
         (D : F α A [ β ]⊢ C) → 
         D == FL (cut (FR 1m 1⇒ hyp) D) 

    Uη : ∀ {p q r} {α : p ≥ q} {β : q ≥ r} {A : Tp p} {C : Tp r}
         (D : A [ α ]⊢ U β C) → 
         D == UR (cut D (UL 1m 1⇒ hyp))

  record QEquiv {p : Mode} (A B : Tp p) : Set where
    constructor qequiv
    field
      f : A [ 1m ]⊢ B
      g : B [ 1m ]⊢ A
      α : cut f g == hyp
      β : cut g f == hyp


  -- ----------------------------------------------------------------------
  -- F α and F β are different for two parallel but different α and β

  diff1 : {p q : Mode} {α β : q ≥ p} {A : Tp q} → F α A [ 1m ]⊢ F β A
  diff1 = FL (FR 1m {!NO!} hyp)

  diff2 : {p q : Mode} {α β : q ≥ p} {A : Tp p} → U α A [ 1m ]⊢ U β A
  diff2 = UR (UL 1m {!NO!} hyp)


  -- ----------------------------------------------------------------------
  -- functoriality of F and U on 1-cells in the diagrams

  -- F is contravariant
  
  Ffunc11 : ∀ {p} {A : Tp p} → F 1m A [ 1m ]⊢ A
  Ffunc11 = FL {α = 1m} {β = 1m} hyp

  Ffunc12 : ∀ {p} {A : Tp p} → A [ 1m ]⊢ F 1m A
  Ffunc12 = FR 1m 1⇒ hyp

  Ffunc1-composite-1 : ∀ {p} {A : Tp p} → (cut (Ffunc11 {p = p} {A}) Ffunc12) == hyp {_}{F 1m A}
  Ffunc1-composite-1 = ap (λ x → FL (FR 1m 1⇒ x)) (cut-ident-left _ ∘ transport⊢1 _) ∘ (Fη (FR 1m 1⇒ (FL {α = 1m} {β = 1m} hyp)) ∘ ap (FR 1m 1⇒) (cut-ident-right _))

  Ffunc1-composite-2 : ∀ {p} {A : Tp p} → (cut Ffunc12 (Ffunc11 {p = p} {A})) == hyp
  Ffunc1-composite-2 = cut-ident-left _ ∘ transport⊢1 _

  Ffunc1 : {p : Mode} {A : Tp p} → QEquiv (F 1m A) A
  Ffunc1 = qequiv Ffunc11 Ffunc12 Ffunc1-composite-1 Ffunc1-composite-2 


  Ffunc∘1 : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _}
          → F α (F β A) [ 1m ]⊢ F (β ∘1 α) A
  Ffunc∘1 = FL (FL (FR 1m 1⇒ hyp))

  Ffunc∘2 : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _}
          → F (β ∘1 α) A [ 1m ]⊢ F α (F β A)
  Ffunc∘2 {α = α} {β = β} = FL {α = β ∘1 α} {β = 1m} (FR β 1⇒ (FR 1m 1⇒ hyp)) 

  Ffunc∘-composite-1 : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _}
          → cut (Ffunc∘1 {α = α} {β = β} {A = A}) Ffunc∘2 == hyp
  Ffunc∘-composite-1 {α = α} {β = β} =
    cut Ffunc∘1 Ffunc∘2 =〈 ap FL (ap FL (transport⊢1 _)) 〉 
    FL (FL (cut (ident _) (FR β 1⇒ (FR 1m 1⇒ hyp)))) =〈 ap (λ x → FL (FL x)) (cut-ident-left _) 〉 
    FL (FL (FR β 1⇒ (FR 1m 1⇒ hyp))) =〈 ! (ap (λ x → FL (FL (FR β 1⇒ x))) (cut-ident-left _)) 〉
    FL (FL (FR β 1⇒ (cut (ident _) (FR 1m 1⇒ hyp)))) =〈 ! (ap (λ x → FL (FL (FR β 1⇒ x))) (transport⊢1 _)) 〉 
    FL (FL (FR β 1⇒ (transport⊢ 1⇒ (cut hyp (FR 1m 1⇒ hyp))))) =〈 ap FL (! (Fη (FR 1m 1⇒ (FL (FR 1m 1⇒ hyp))))) 〉 
    hyp ∎

  Ffunc∘-composite-2 : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _}
          → cut Ffunc∘2 (Ffunc∘1 {α = α} {β = β} {A = A}) == hyp
  Ffunc∘-composite-2 = ap FL ((cut-ident-left _ ∘ transport⊢1 _) ∘ transport⊢1 _)

  Ffunc∘ : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _} → QEquiv (F α (F β A)) (F (β ∘1 α) A)
  Ffunc∘ = qequiv Ffunc∘1 Ffunc∘2 Ffunc∘-composite-1 Ffunc∘-composite-2


  Ufunc11 : ∀ {p} {A : Tp p} → U 1m A [ 1m ]⊢ A
  Ufunc11 = UL 1m 1⇒ hyp

  Ufunc12 : ∀ {p} {A : Tp p} → A [ 1m ]⊢ U 1m A
  Ufunc12 = UR {α = 1m} {β = 1m} hyp

  Ufunc∘1 : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _}
          → U β (U α A) [ 1m ]⊢ U (β ∘1 α) A
  Ufunc∘1 {α = α} {β = β} = UR {α = β ∘1 α} {β = 1m} (UL α 1⇒ (UL 1m 1⇒ hyp))

  Ufunc∘2 : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _}
          → U (β ∘1 α) A [ 1m ]⊢ U β (U α A)
  Ufunc∘2 {α = α} {β = β} = UR {α = β} {β = 1m} (UR (UL 1m 1⇒ hyp)) 

  -- FIXME: equations for U for U


  -- ----------------------------------------------------------------------
  -- F and U respect 2-cells in one direction
  -- F is contravariant; U is covariant

  F2 : ∀ {p q} {A B : Tp q} {α β : q ≥ p} → β ⇒ α → F α A [ 1m ]⊢ F β A
  F2 {α = α} e = FL {α = α} {β = 1m} (FR 1m e hyp)

  F21 : ∀ {p q} {A B : Tp q} {α : q ≥ p} → F2 {A = A} {B = B} (1⇒ {α = α}) == hyp 
  F21 = id

  F2· : ∀ {p q} {A B : Tp q} {α β γ : q ≥ p} {e1 : β ⇒ α} {e2 : γ ⇒ β} → F2 {A = A} {B = B} (e2 ·2 e1) == cut (F2 {A = A} {B = B} e1) (F2 {A = A} {B = B} e2)
  F2· = ap FL (! (ap (transport⊢ _) (cut-ident-left _)))

  U2 : ∀ {p q} {A B : Tp p} {α β : q ≥ p} → α ⇒ β → U α A [ 1m ]⊢ U β A
  U2 {α = α} {β = β} e = UR {α = β} {β = 1m} (UL 1m e hyp)

  -- FIXME dually for U


  -- ----------------------------------------------------------------------
  -- functoriality of F and U on terms

  Ffunc : ∀ {p q : Mode} {α : q ≥ p} {A B} → A [ 1m ]⊢ B → F α A [ 1m ]⊢ F α B
  Ffunc {α = α} D =  FL {α = α} {β = 1m} (FR 1m 1⇒ D)

  Ffunc-ident : ∀ {p q : Mode} {α : q ≥ p} {A} → Ffunc (ident A) == (ident (F α A))
  Ffunc-ident = id

  Ffunc-cut : ∀ {p q : Mode} {α : q ≥ p} {A B C} {D : A [ 1m ]⊢ B} {E : B [ 1m ]⊢ C} → Ffunc {α = α} (cut D E) == cut (Ffunc D) (Ffunc E)
  Ffunc-cut {D = D} {E = E} = FL (FR 1m 1⇒ (cut D E))  =〈 ap FL (! (cutFR {D = D} {E = E})) 〉 
                              FL (cut D (FR 1m 1⇒ E)) =〈 ! (ap FL (transport⊢1 _)) 〉
                              _ ∎

  Ufunc : ∀ {p q : Mode} {α : q ≥ p} {A B} → A [ 1m ]⊢ B → U α A [ 1m ]⊢ U α B
  Ufunc {α = α} D =  UR {α = α} {β = 1m} (UL 1m 1⇒ D)

  -- FIXME equations for U


  -- ----------------------------------------------------------------------
  -- F -| U

  UFadjunction1 : ∀ {p q} {A B} {α : q ≥ p} → F α A [ 1m ]⊢ B → A [ 1m ]⊢ U α B
  UFadjunction1 {α = α} D = UR {α = α} {β = 1m} (cut (FR 1m 1⇒ hyp) D) 

  UFadjunction2 : ∀ {p q} {A B} {α : q ≥ p} → A [ 1m ]⊢ U α B → F α A [ 1m ]⊢ B 
  UFadjunction2 {α = α} D = FL {α = α} {β = 1m} (cut D (UL 1m 1⇒ hyp)) 

  UFadj-composite2 : ∀ {p q} {A B} {α : q ≥ p} (D : F α A [ 1m ]⊢ B ) -> UFadjunction2 (UFadjunction1 D) == D
  UFadj-composite2 D = (! (Fη D) ∘ ap FL (cut-ident-right _ ∘ transport⊢1 _))

  UFadj-composite1 : ∀ {p q} {A B} {α : q ≥ p} (D : A [ 1m ]⊢ U α B) -> UFadjunction1 (UFadjunction2 D) == D
  UFadj-composite1 D = ! (Uη D) ∘ ap UR (cut-ident-left _ ∘ transport⊢1 _)


  ----------------------------------------------------------------------
  -- monads

  □ : ∀ {p q} (α : q ≥ p) → Tp p → Tp p 
  □ α A = F α (U α A)

  ◯ : ∀ {p q} (α : q ≥ p) → Tp q → Tp q 
  ◯ α A = U α (F α A)

  □func : ∀ {p q : Mode} {α : q ≥ p} {A B} → A [ 1m ]⊢ B → □ α A [ 1m ]⊢ □ α B
  □func D = Ffunc (Ufunc D)

  ◯func : ∀ {p q : Mode} {α : q ≥ p} {A B} → A [ 1m ]⊢ B → ◯ α A [ 1m ]⊢ ◯ α B
  ◯func D = Ufunc (Ffunc D)

  □counit : {p q : Mode} {A : Tp p} {α : q ≥ p} → □ α A [ 1m ]⊢ A
  □counit {α = α} = FL {α = α} {β = 1m} (UL 1m 1⇒ hyp)

  □comult : {p q : Mode} {A : Tp p} {α : q ≥ p} → □ α A [ 1m ]⊢ □ α (□ α A)
  □comult {α = α} = FL {α = α} {β = 1m} (FR 1m 1⇒ (UR (FR 1m 1⇒ hyp))) 

  ◯unit : {p q : Mode} {A : Tp q} {α : q ≥ p} → A [ 1m ]⊢ ◯ α A
  ◯unit {α = α} = UR (FR 1m 1⇒ hyp)

  ◯mult : {p q : Mode} {A : Tp q} {α : q ≥ p} → ◯ α (◯ α A) [ 1m ]⊢ ◯ α A
  ◯mult {α = α} = UR {α = α} {β = 1m} (UL 1m 1⇒ (FL (UL 1m 1⇒ hyp))) 

  ◯assoc : ∀ {p q : Mode} {A : Tp q} {α : q ≥ p} 
          -> _==_ {◯ α (◯ α (◯ α A)) [ 1m ]⊢ ◯ α A} (cut (◯func ◯mult) ◯mult) (cut ◯mult ◯mult)
  ◯assoc = id

  ◯unit1 : ∀ {p q : Mode} {A : Tp q} {α : q ≥ p} 
              -> _==_ {◯ α A [ 1m ]⊢ ◯ α A} (cut ◯unit ◯mult) hyp
  ◯unit1 {α = α} = ap (λ x → UR {α = α} {β = 1m} (UL 1m 1⇒ (FL x))) (cut-ident-left _ ∘ transport⊢1 _)

  ◯unit2 : ∀ {p q : Mode} {A : Tp q} {α : q ≥ p} 
              -> _==_ {◯ α A [ 1m ]⊢ ◯ α A} (cut (◯func ◯unit) ◯mult) hyp
  ◯unit2 {α = α} = ap (λ x → UR {α = α} {β = 1m} (UL 1m 1⇒ (FL x))) (cut-ident-left _ ∘ (transport⊢1 _ ∘ (transport⊢1 _ ∘ transport⊢1 _)))

  -- FIXME equations for □

  -- need β such that 1m ⇒ α ∘1 β 
  badcounit : {p q : Mode} {A : Tp q} {α : q ≥ p} → ◯ α A [ 1m ]⊢ A
  badcounit = UL {!!} {!NO!} (FL {!!}) 

  -- need β such that 
  badunit : {p q : Mode} {A : Tp p} {α : q ≥ p} → A [ 1m ]⊢ □ α A
  badunit = FR {!!} {!NO!} (UR {!!})


  -- ----------------------------------------------------------------------
  -- rules needed for specific theories

  -- FIXME do these make sense?
  postulate
    FR2 : ∀ {p q r} {α : q ≥ p} {β : r ≥ p} {A : Tp q} {C : Tp r}
         → {γ γ' : r ≥ q} → {e : (γ ∘1 α) ⇒ β} {e' : (γ' ∘1 α) ⇒ β } {D : C [ γ ]⊢ A}  {D' : C [ γ' ]⊢ A} 
         → (γ2 : γ' ⇒ γ) (e2 : ((γ2 ∘1cong 1⇒) ·2 e) == e') (D2 : D == transport⊢ γ2 D')
         → FR γ e D == FR γ' e' D' 

    UL2 : ∀ {p q r} {α : p ≥ r} {β : p ≥ q} {A : Tp q} {C : Tp r}
         → {γ γ' : r ≥ q} → {e : (α ∘1 γ) ⇒ β } {e' : (α ∘1 γ') ⇒ β } {D : C [ γ ]⊢ A}  {D' : C [ γ' ]⊢ A} 
         → (γ2 : γ' ⇒ γ) (e2 : ((1⇒ ∘1cong γ2) ·2 e) == e') (D2 : D == transport⊢ γ2  D')
         → UL γ e D == UL γ' e' D' 


  -- ----------------------------------------------------------------------

  -- we want a triple adjunction 
  -- Δ -| Γ -| ∇

  -- this gives rise to 
  -- ♭ = ΔΓ 
  -- ♯ = ∇Γ 
  -- where ♭ -| #

  -- so we want 
  -- Δ -| ∇
  -- which is generated by ∇ o Δ having a unit and Δ o ∇ having a counit
  module TripleAdjunction (c : Mode)
                          (s : Mode)
                          (∇m : c ≥ s)
                          (Δm : s ≥ c)
                          (∇Δunit   : 1m ⇒ (∇m ∘1 Δm))
                          (Δ∇counit : (Δm ∘1 ∇m) ⇒ 1m) 

                          -- F -| G
                          -- F unit · counit F = 1 
                          -- unit G · G counit = 1   
                          (adjeq1 : ((1⇒{s}{c}{Δm} ∘1cong ∇Δunit) ·2 (Δ∇counit ∘1cong 1⇒{_}{_}{Δm})) == 1⇒)
                          (adjeq2 : ((∇Δunit ∘1cong  1⇒{_}{_}{∇m})  ·2 (1⇒{_}{_}{∇m} ∘1cong Δ∇counit)) == 1⇒)
                          where

    -- ----------------------------------------------------------------------
    -- F -| U so we want U Δ to be the same as F ∇
    -- we actually get an "hiso" -- a map with both a left and a right inverse, but they're different

    mergeUF : ∀ {A : Tp c} → U Δm A [ 1m ]⊢ F ∇m A
    mergeUF = FR Δm Δ∇counit (UL 1m 1⇒ hyp) 

    mergeUF' : ∀ {A : Tp c} → U Δm A [ 1m ]⊢ F ∇m A 
    mergeUF' = UL ∇m Δ∇counit (FR 1m 1⇒ hyp)

    mergeFU : ∀ {A : Tp c} → F ∇m A [ 1m ]⊢ U Δm A
    mergeFU = FL {α = ∇m} {β = 1m} (UR (transport⊢ ∇Δunit hyp))

    inv1 : cut (mergeUF{P}) (mergeFU {P}) == ident (U Δm P)
    inv1 = ap (UR {α = Δm} {β = 1m ∘1 1m}) (UL2 {D = cut hyp (hypp ∇Δunit)} {D' = ident P} ∇Δunit adjeq1 id) 

    inv2 : cut (mergeFU {P}) (mergeUF'{P}) == ident (F ∇m P)
    inv2 = ap (FL {α = ∇m} {β = 1m ∘1 1m}) (FR2 {D = cut (hypp ∇Δunit) hyp} {D' = ident P} ∇Δunit adjeq2 id) 

    badmergeUF : ∀ {A : Tp s} → U ∇m A [ 1m ]⊢ F Δm A
    badmergeUF = UL Δm {!NO!} (FR 1m 1⇒ hyp)
  
    badmergeUF' : ∀ {A : Tp s} → U ∇m A [ 1m ]⊢ F Δm A
    badmergeUF' = FR ∇m {!NO!} (UL 1m 1⇒ hyp) 
  
    badmergeFU : ∀ {A : Tp s} → F Δm A [ 1m ]⊢ U ∇m A
    badmergeFU = FL (UR (transport⊢ {!!} hyp))
  
    -- -------------------------------------------------------------------------------

    ♭ = □ Δm
    ♯ = ◯ ∇m
  
    badunit' : {A : Tp c}→ A [ 1m ]⊢ ♭ A
    badunit' = FR ∇m {! NO!} (UR (transport⊢ {!!} hyp))
  
    badcounit' : {A : Tp c} → ♯ A [ 1m ]⊢ A
    badcounit' = UL Δm {! NO!} (FL (transport⊢ {!!} hyp))

    -- they are adjoint

    ♭♯adjunction1 : ∀ {A B} → ♭ A [ 1m ]⊢ B → A [ 1m ]⊢ ♯ B
    ♭♯adjunction1 {A}{B} start = UFadjunction1 step2 where
      step1 : U Δm A [ 1m ]⊢ U Δm B
      step1 = UFadjunction1 start
  
      step2 : F ∇m A [ 1m ]⊢ F ∇m B
      step2 = cut (cut mergeFU step1) mergeUF

    ♭♯adjunction2 : ∀ {A B} → A [ 1m ]⊢ ♯ B → ♭ A [ 1m ]⊢ B 
    ♭♯adjunction2 {A}{B} start = UFadjunction2 (cut mergeUF (cut (UFadjunction2 start) mergeFU))

    -- one of these should be a mergeUF' and then these should be an equivalence 

    -- ----------------------------------------------------------------------
    -- ♭ preserves coproducts

    pres-coprod1 : ∀ {A B} → ♭ (A ⊕ B) [ 1m ]⊢ (♭ A ⊕ ♭ B)
    pres-coprod1 = ♭♯adjunction2 (Case (♭♯adjunction1 (Inl hyp)) (♭♯adjunction1 (Inr hyp)))

    pres-coprod2 : ∀ {A B} → (♭ A ⊕ ♭ B) [ 1m ]⊢ ♭ (A ⊕ B)
    pres-coprod2 = Case (□func (Inl hyp)) (□func (Inr hyp))

    pres-coprod2-composite-1 : cut (pres-coprod1 {P}{Q}) (pres-coprod2 {P}{Q}) == hyp
    pres-coprod2-composite-1 = {!!}

    pres-coprod2-composite-2 : cut (pres-coprod2 {P}{Q}) (pres-coprod1 {P}{Q}) == hyp
    pres-coprod2-composite-2 = {!!}

    
    -- ----------------------------------------------------------------------
    -- ♭ absorbing ♯ and vice versa
    
    ♭absorbs♯1 : ∀ {A} → ♭ A [ 1m ]⊢ ♭ (♯ A) 
    ♭absorbs♯1 = □func ◯unit

    ♭absorbs♯1' : ∀ {A} → ♭ A [ 1m ]⊢ ♭ (♯ A) 
    ♭absorbs♯1' = {!!}

    ♭absorbs♯2 : ∀ {A} → ♭ (♯ A) [ 1m ]⊢ ♭ A
    ♭absorbs♯2 = FL {α = Δm} {β = 1m} (FR 1m 1⇒ (UL ∇m Δ∇counit (UL 1m 1⇒ mergeFU))) 

    ♭absorbs♯-composite-1 : cut (♭absorbs♯1 {P}) (♭absorbs♯2 {P}) == hyp
    ♭absorbs♯-composite-1 = ap (λ x → FL (FR 1m 1⇒ x)) (ap (UR {α = Δm} {β = 1m}) (UL2 {D = cut (UR (hypp ∇Δunit)) (UL 1m 1⇒ hyp)} {D' = ident P} ∇Δunit adjeq1 id) ∘ Uη (UL ∇m Δ∇counit (UR (hypp ∇Δunit))))

    -- FIXME
    ♭absorbs♯-composite-2 : cut (♭absorbs♯2 {P}) (♭absorbs♯1 {P}) == hyp
    ♭absorbs♯-composite-2 = ap (λ x → FL (FR 1m 1⇒ (UR x)))
                          (UL2 {D = cut (UL 1m 1⇒ mergeFU) (UL 1m 1⇒ ◯unit)} {D' = ident (♯ P)} ∇Δunit adjeq1
                               (ap UR (UL2 {!!} {!!} (ap FL (FR2 {D = cut (hypp ∇Δunit) (ident P)} {D' = ident P} ∇Δunit {!!} id))) ∘ Uη (UL Δm 1⇒ (FL (UR {α = ∇m} {β = ∇m ∘1 Δm} (FR (∇m ∘1 Δm) 1⇒ (hypp ∇Δunit)))))))

    ♯absorbs♭1 : ∀ {A} → ♯ A [ 1m ]⊢ ♯ (♭ A) 
    ♯absorbs♭1 = UR {α = ∇m} {β = 1m} (UL 1m 1⇒ (FR Δm Δ∇counit (FR 1m 1⇒ mergeFU))) 

    ♯absorbs♭2 : ∀ {A} → ♯ (♭ A) [ 1m ]⊢ ♯ A
    ♯absorbs♭2 = ◯func □counit

  
  module Reflection where
    postulate
      c : Mode
      s : Mode
      ∇m : c ≥ s
      Δm : s ≥ c
      Δ∇identity : _==_ {s ≥ s} (Δm ∘1 ∇m) (1m {s}) 
      ∇Δunit   : 1m ⇒ (∇m ∘1 Δm)

    {-# REWRITE Δ∇identity #-}
    postulate
      ∇Δidentity' : Δ∇identity == id
    
{-
    FIXME
    postulate
      adjeq1 : (Δ∇counit ∘1cong 1⇒{_}{_}{Δm}) == 1⇒
      adjeq2 : (1⇒{_}{_}{∇m} ∘1cong Δ∇counit) == 1⇒' (! (∘1-assoc {_} {_} {_} {_} {∇m} {Δm} {∇m}))
-}

    module A = TripleAdjunction c s ∇m Δm ∇Δunit (1⇒' (! Δ∇identity)) {!!} {!!}
    open A

    -- we don't want the identity that collapses ♭ and ♯
    wrongdirection : ∀ {A} → A [ 1m ]⊢ ♭ A
    wrongdirection {A} = cut (cut {!NO!} (Ffunc∘2 {α = Δm} {β = ∇m})) (Ffunc {α = Δm} mergeFU)

    wrongdirection2 : ∀ {A} → ♯ A [ 1m ]⊢ A
    wrongdirection2 {A} = cut (Ufunc mergeFU) (cut Ufunc∘1 {!NO!}) 

    -- each of these three steps should be an equivalence, so the whole thing should be
    collapseΔ1 : ∀ {A} → ◯ Δm A [ 1m ]⊢ A
    collapseΔ1 = cut mergeUF (cut (Ffunc∘1 {α = ∇m} {β = Δm}) Ffunc11)

    -- each of these three steps should be an equivalence, so the whole thing should be
    collapse∇1 : ∀ {A} → A [ 1m ]⊢ □ ∇m A
    collapse∇1 = cut (cut Ufunc12 (Ufunc∘2 {α = ∇m} {β = Δm})) mergeUF

    collapse∇2 : ∀ {A} → □ ∇m A [ 1m ]⊢ A
    collapse∇2 = (cut mergeFU (cut (Ufunc∘1 {α = ∇m} {β = Δm}) Ufunc11))

    -- ap of U on an equivalence, should be an equivalence
    ♯idempotent : ∀ {A} → ♯ A [ 1m ]⊢ ♯ (♯ A)
    ♯idempotent = Ufunc collapse∇1

    -- ap of F on an equivalence, should be an equivalence
    ♭idempotent : ∀ {A} → ♭ (♭ A) [ 1m ]⊢ ♭ A
    ♭idempotent = Ffunc collapseΔ1



    --Δ (F Δm) and ∇ (U ∇m) are full and faithful but Γ (the other two) is not

    FΔ-fullandfaithful : ∀ {A B} → F Δm A [ 1m ]⊢ F Δm B -> A [ 1m ]⊢ B
    FΔ-fullandfaithful D = cut (cut Ffunc12 (Ffunc∘2 {α = ∇m} {β = Δm})) (cut (Ffunc {α = ∇m} D) (cut (Ffunc∘1 {α = ∇m} {β = Δm}) Ffunc11))

    -- seems like it works
    FΔ-fullandfaithful-composite-1 : (D : P [ 1m ]⊢ Q) → FΔ-fullandfaithful (Ffunc D) == D
    FΔ-fullandfaithful-composite-1 D = {!!}

    FΔ-fullandfaithful-composite-2 : (D : F Δm P [ 1m ]⊢ F Δm Q) → (Ffunc (FΔ-fullandfaithful D)) == D 
    FΔ-fullandfaithful-composite-2 D = {!!}
{-
      Ffunc (FΔ-fullandfaithful D) =〈 {! cancel some transports !} 〉 
      FL {α = Δm} {β = 1m} (FR 1m 1⇒ (cut (FR 1m 1⇒ (hypp 1⇒)) (cut D (FL {α = Δm} {β = ∇m} (hypq 1⇒))))) =〈 {!reassociate!} 〉 
      FL {α = Δm} {β = 1m} (FR 1m 1⇒ (cut D' (FL {α = Δm} {β = ∇m} (hypq 1⇒)))) =〈 ! (ap (FL {α = Δm} {β = 1m}) (FIXME D')) 〉 
      FL {α = Δm} {β = 1m} D' =〈 ! (Fη D) 〉 
      D ∎ where
        D' : P [ Δm ]⊢ F Δm Q
        D' = (cut (FR 1m 1⇒ (hypp 1⇒)) D)

        FIXME : ∀ {A B} → (D : A [ Δm ]⊢ F Δm B) → D == FR 1m 1⇒ ((cut D (FL {α = Δm} {β = ∇m} hyp))) -- 1m is only endomorphism of s
        FIXME = {! !}
-}

    U∇-fullandfaithful : ∀ {A B} → U ∇m A [ 1m ]⊢ U ∇m B -> A [ 1m ]⊢ B
    U∇-fullandfaithful D = cut collapse∇1 (cut (Ffunc {α = ∇m} D) collapse∇2)

    -- seems OK
    U∇-fullandfaithful-composite-1 : (D : P [ 1m ]⊢ Q) -> D == (U∇-fullandfaithful (Ufunc D))
    U∇-fullandfaithful-composite-1 D = {!!}

    -- ??? 
    U∇-fullandfaithful-composite-2 : (D : U ∇m P [ 1m ]⊢ U ∇m Q) -> D == (Ufunc (U∇-fullandfaithful D))
    U∇-fullandfaithful-composite-2 D = {!♭!}



{-
  module IdempotentMonad where
    postulate
      m    : Mode
      T    : m ≥ m
      unit : 1m ⇒ T
      mult : (T ·1 T) ⇒ T 
      -- monad laws for unit and mult
      -- equations that mult and l(unit) are mutually inverse
-}

      

