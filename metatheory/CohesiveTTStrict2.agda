-- requires Agda 2.4.2.3 or later for the rewrite stuff

open import Agda.Primitive

module metatheory.CohesiveTTStrict2 where

  -- REWRITE seems to need the level-polymorphic identity type
  data _==_ {A : Set} (M : A) : A → Set where
    id : M == M

  ap :  {A B : Set} {M N : A}
       (f : A → B) → M == N → (f M) == (f N)
  ap f id = id

  ! :  {A : Set} {M N : A} → M == N → N == M
  ! id = id

 
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


  -- FIXME does this make sense?
  postulate
    FR2 : ∀ {p q r} {α : q ≥ p} {β : r ≥ p} {A : Tp q} {C : Tp r}
         → {γ γ' : r ≥ q} → {e : (γ ∘1 α) ⇒ β} {e' : (γ' ∘1 α) ⇒ β } {D : C [ γ ]⊢ A}  {D' : C [ γ' ]⊢ A} 
         → (γ2 : γ' ⇒ γ) (e2 : ((γ2 ∘1cong 1⇒) ·2 e) == e') (D2 : D == transport⊢ γ2 D')
         → FR γ e D == FR γ' e' D' 

    UL2 : ∀ {p q r} {α : p ≥ r} {β : p ≥ q} {A : Tp q} {C : Tp r}
         → {γ γ' : r ≥ q} → {e : (α ∘1 γ) ⇒ β } {e' : (α ∘1 γ') ⇒ β } {D : C [ γ ]⊢ A}  {D' : C [ γ' ]⊢ A} 
         → (γ2 : γ' ⇒ γ) (e2 : ((1⇒ ∘1cong γ2) ·2 e) == e') (D2 : D == transport⊢ γ2  D')
         → UL γ e D == UL γ' e' D' 

  -- seems to only work for 1m
  eta : ∀ {p} (A : Tp p) → A [ 1m ]⊢ A
  eta P = hypp 1⇒
  eta Q = hypq 1⇒
  eta (U α A) = (UR {α = α} {β = 1m} (UL 1m 1⇒ (eta A)))  -- need to annote because it infers the wrong association
  eta (F α A) = FL (FR 1m 1⇒ (eta A)) 
  eta (A ⊕ B) = Case (Inl (eta A)) (Inr (eta B))

  cut : ∀ {p q r} {α : q ≥ p} {β : r ≥ q} {A : Tp r} {B : Tp q} {C : Tp p}
      → A [ β ]⊢ B
      → B [ α ]⊢ C
      → A [ β ∘1 α ]⊢ C
  -- atom
  cut (hypp p) (hypp q) = hypp (p ∘1cong q)
  cut (hypq p) (hypq q) = hypq (p ∘1cong q)
  -- principal 
  cut {α = α} {β = β} (FR γ e D) (FL {α = α1} E) = transport⊢ (e ∘1cong 1⇒) (cut D E)
  cut {α = α} {β = β} (UR {α = α1} D) (UL γ₁ e E) = transport⊢ (1⇒ ∘1cong e) (cut D E)
  cut {α = α} {β = β} (Inl D) (Case E1 E2) = cut D E1
  cut {α = α} {β = β} (Inr D) (Case E1 E2) = cut D E2
  -- right commutative
  cut {α = α} {β = β} D (FR {α = α'} γ e E) = FR (β ∘1 γ) (1⇒ ∘1cong e) (cut D E)
  cut {α = α} {β = β} D (UR {α = α1} E) = UR {α = α1} {β = β ∘1 α} (cut D E)
  cut {α = α} {β = β} D (Inl E) = Inl (cut D E)
  cut {α = α} {β = β} D (Inr E) = Inr (cut D E)
  -- left commutative
  cut {α = α} {β = β} (FL {α = α1} D) E = FL {α = α1} {β = β ∘1 α} (cut D E)
  cut {α = α} {β = β} (UL {α = α'} γ e D) E = UL (γ ∘1 α) (e  ∘1cong 1⇒) (cut D E)
  cut {α = α} {β = β} (Case D1 D2) E = Case (cut D1 E) (cut D2 E)
    
  hyp : ∀ {p} {A : Tp p} → A [ 1m ]⊢ A
  hyp = eta _ 

{-
  cut-eta-right : ∀ {p q} {α : q ≥ p} {A B} → (D : A [ α ]⊢ B)
                  → cut D (eta B) == D
  cut-eta-right (hypp e) = id
  cut-eta-right (FL D) = {!!} 
  cut-eta-right (FR γ e D) = {!!}
  cut-eta-right (UL γ e D) = {!!}
  cut-eta-right (UR D) = {!!}
  cut-eta-right (Inl D) = {!ap Inl (cut-eta-right D)!}
  cut-eta-right (Inr D) = {!!}
  cut-eta-right (Case D1 D2) = {!!}
-}

  -- ----------------------------------------------------------------------
  -- examples

  -- F α and F β are different for two parallel but different α and β
  diff1 : {p q : Mode} {α β : q ≥ p} {A : Tp q} → F α A [ 1m ]⊢ F β A
  diff1 = FL (FR 1m {!NO!} hyp)

  diff2 : {p q : Mode} {α β : q ≥ p} {A : Tp p} → U α A [ 1m ]⊢ U β A
  diff2 = UR (UL 1m {!NO!} hyp)

  -- functoriality of F and U in the category
  -- F is contravariant
  
  Ffunc11 : ∀ {p} {A : Tp p} → F 1m A [ 1m ]⊢ A
  Ffunc11 = FL {α = 1m} {β = 1m} hyp

  Ffunc12 : ∀ {p} {A : Tp p} → A [ 1m ]⊢ F 1m A
  Ffunc12 = FR 1m 1⇒ hyp

  Ffunc1-composite-1 : ∀ {p} → (cut (Ffunc11 {p = p} {A = P}) Ffunc12) == hyp
  Ffunc1-composite-1 = {!focusing? off by where FL is!}

  Ffunc1-composite-2 : ∀ {p} → (cut Ffunc12 (Ffunc11 {p = p} {A = P})) == hyp
  Ffunc1-composite-2 = id

  Ffunc∘1 : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _}
          → F α (F β A) [ 1m ]⊢ F (β ∘1 α) A
  Ffunc∘1 = FL (FL (FR 1m 1⇒ hyp))

  Ffunc∘2 : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _}
          → F (β ∘1 α) A [ 1m ]⊢ F α (F β A)
  Ffunc∘2 {α = α} {β = β} = FL {α = β ∘1 α} {β = 1m} (FR β 1⇒ (FR 1m 1⇒ hyp)) 

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

  -- functors are actually functors
  Ffunc : ∀ {p q : Mode} {α : q ≥ p} {A B} → A [ 1m ]⊢ B → F α A [ 1m ]⊢ F α B
  Ffunc {α = α} D =  FL {α = α} {β = 1m} (FR 1m 1⇒ D)

  Ufunc : ∀ {p q : Mode} {α : q ≥ p} {A B} → A [ 1m ]⊢ B → U α A [ 1m ]⊢ U α B
  Ufunc {α = α} D =  UR {α = α} {β = 1m} (UL 1m 1⇒ D)

  -- adjoints are actually adjoint
  UFadjunction1 : ∀ {p q} {A B} {α : q ≥ p} → F α A [ 1m ]⊢ B → A [ 1m ]⊢ U α B
  UFadjunction1 {α = α} D = UR {α = α} {β = 1m} (cut (FR 1m 1⇒ hyp) D) 

  UFadjunction2 : ∀ {p q} {A B} {α : q ≥ p} → A [ 1m ]⊢ U α B → F α A [ 1m ]⊢ B 
  UFadjunction2 {α = α} D = FL {α = α} {β = 1m} (cut D (UL 1m 1⇒ hyp)) 

  -- needs some eta/cut cancellation and some eta expansion for D (maybe would be true with focusing?) ? 
  {-
  UFadj-composite1 : ∀ {p q} {A B} {α : q ≥ p} (D : A [ 1m ]⊢ U α B) -> D == UFadjunction1 (UFadjunction2 D)
  UFcomposite1 D = {!!}

  UFadj-composite2 : ∀ {p q} {A B} {α : q ≥ p} (D : F α A [ 1m ]⊢ B ) -> D == UFadjunction2 (UFadjunction1 D)
  UFadj-composite2 D = {!!}
  -}

  -- monads

  □ : ∀ {p q} (α : q ≥ p) → Tp p → Tp p 
  □ α A = F α (U α A)

  ◯ : ∀ {p q} (α : q ≥ p) → Tp q → Tp q 
  ◯ α A = U α (F α A)

  □func : ∀ {p q : Mode} {α : q ≥ p} {A B} → A [ 1m ]⊢ B → □ α A [ 1m ]⊢ □ α B
  □func D = Ffunc (Ufunc D)

  ◯func : ∀ {p q : Mode} {α : q ≥ p} {A B} → A [ 1m ]⊢ B → ◯ α A [ 1m ]⊢ ◯ α B
  ◯func D = Ufunc (Ffunc D)

  unit : {p q : Mode} {A : Tp q} {α : q ≥ p} → A [ 1m ]⊢ ◯ α A
  unit {α = α} = UR (FR 1m 1⇒ hyp)

  mult : {p q : Mode} {A : Tp q} {α : q ≥ p} → ◯ α (◯ α A) [ 1m ]⊢ ◯ α A
  mult {α = α} = UR {α = α} {β = 1m} (UL 1m 1⇒ (FL (UL 1m 1⇒ hyp))) 

  counit : {p q : Mode} {A : Tp p} {α : q ≥ p} → □ α A [ 1m ]⊢ A
  counit {α = α} = FL {α = α} {β = 1m} (UL 1m 1⇒ hyp)

  comult : {p q : Mode} {A : Tp p} {α : q ≥ p} → □ α A [ 1m ]⊢ □ α (□ α A)
  comult {α = α} = FL {α = α} {β = 1m} (FR 1m 1⇒ (UR (FR 1m 1⇒ hyp))) 

  -- need β such that 1m ⇒ α ∘1 β 
  badcounit : {p q : Mode} {A : Tp q} {α : q ≥ p} → ◯ α A [ 1m ]⊢ A
  badcounit = UL {!!} {!NO!} (FL {!!}) 

  -- need β such that 
  badunit : {p q : Mode} {A : Tp p} {α : q ≥ p} → A [ 1m ]⊢ □ α A
  badunit = FR {!!} {!NO!} (UR {!!})

  -- F and U respect 2-cells in one direction
  -- F is covariant; U is contravariant

  F2 : ∀ {p q} {A B : Tp q} {α β : q ≥ p} → β ⇒ α → F α A [ 1m ]⊢ F β A
  F2 {α = α} e = FL {α = α} {β = 1m} (FR 1m e hyp)

  U2 : ∀ {p q} {A B : Tp p} {α β : q ≥ p} → α ⇒ β → U α A [ 1m ]⊢ U β A
  U2 {α = α} {β = β} e = UR {α = β} {β = 1m} (UL 1m e hyp)



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

    -- F -| U so we want U Δ to be the same as F ∇

    mergeUF : ∀ {A : Tp c} → U Δm A [ 1m ]⊢ F ∇m A
    mergeUF = FR Δm Δ∇counit (UL 1m 1⇒ hyp) 

    mergeUF' : ∀ {A : Tp c} → U Δm A [ 1m ]⊢ F ∇m A 
    mergeUF' = UL ∇m Δ∇counit (FR 1m 1⇒ hyp)

    mergeFU : ∀ {A : Tp c} → F ∇m A [ 1m ]⊢ U Δm A
    mergeFU = FL {α = ∇m} {β = 1m} (UR (transport⊢ ∇Δunit hyp))

    inv1 : cut (mergeUF{P}) (mergeFU {P}) == eta (U Δm P)
    inv1 = ap (UR {α = Δm} {β = 1m ∘1 1m}) (UL2 {D = cut hyp (hypp ∇Δunit)} {D' = eta P} ∇Δunit adjeq1 id) 

    inv2 : cut (mergeFU {P}) (mergeUF'{P}) == eta (F ∇m P)
    inv2 = ap (FL {α = ∇m} {β = 1m ∘1 1m}) (FR2 {D = cut (hypp ∇Δunit) hyp} {D' = eta P} ∇Δunit adjeq2 id) 

    badmergeUF : ∀ {A : Tp s} → U ∇m A [ 1m ]⊢ F Δm A
    badmergeUF = UL Δm {!NO!} (FR 1m 1⇒ hyp)
  
    badmergeUF' : ∀ {A : Tp s} → U ∇m A [ 1m ]⊢ F Δm A
    badmergeUF' = FR ∇m {!NO!} (UL 1m 1⇒ hyp) 
  
    badmergeFU : ∀ {A : Tp s} → F Δm A [ 1m ]⊢ U ∇m A
    badmergeFU = FL (UR (transport⊢ {!!} hyp))
  
    ♭ = □ Δm
    ♯ = ◯ ∇m
  
    badunit' : {A : Tp c}→ A [ 1m ]⊢ ♭ A
    badunit' = FR ∇m {! NO!} (UR (transport⊢ {!!} hyp))
  
    badcounit' : {A : Tp c} → ♯ A [ 1m ]⊢ A
    badcounit' = UL Δm {! NO!} (FL (transport⊢ {!!} hyp))

    ♭♯adjunction1 : ∀ {A B} → ♭ A [ 1m ]⊢ B → A [ 1m ]⊢ ♯ B
    ♭♯adjunction1 {A}{B} start = UFadjunction1 step2 where
      step1 : U Δm A [ 1m ]⊢ U Δm B
      step1 = UFadjunction1 start
  
      step2 : F ∇m A [ 1m ]⊢ F ∇m B
      step2 = cut (cut mergeFU step1) mergeUF

    ♭♯adjunction2 : ∀ {A B} → A [ 1m ]⊢ ♯ B → ♭ A [ 1m ]⊢ B 
    ♭♯adjunction2 {A}{B} start = UFadjunction2 (cut mergeUF (cut (UFadjunction2 start) mergeFU))

    pres-coprod1 : ∀ {A B} → ♭ (A ⊕ B) [ 1m ]⊢ (♭ A ⊕ ♭ B)
    pres-coprod1 = ♭♯adjunction2 (Case (♭♯adjunction1 (Inl hyp)) (♭♯adjunction1 (Inr hyp)))

    pres-coprod2 : ∀ {A B} → (♭ A ⊕ ♭ B) [ 1m ]⊢ ♭ (A ⊕ B)
    pres-coprod2 = Case (□func (Inl hyp)) (□func (Inr hyp))

    -- ♭ absorbing ♯ and vice versa
    
    ♭absorbs♯1 : ∀ {A} → ♭ A [ 1m ]⊢ ♭ (♯ A) 
    ♭absorbs♯1 = □func unit

    ♭absorbs♯2 : ∀ {A} → ♭ (♯ A) [ 1m ]⊢ ♭ A
    ♭absorbs♯2 = FL {α = Δm} {β = 1m} (FR 1m 1⇒ (UL ∇m Δ∇counit (UL 1m 1⇒ mergeFU))) 

    ♯absorbs♭1 : ∀ {A} → ♯ A [ 1m ]⊢ ♯ (♭ A) 
    ♯absorbs♭1 = UR {α = ∇m} {β = 1m} (UL 1m 1⇒ (FR Δm Δ∇counit (FR 1m 1⇒ mergeFU))) 

    ♯absorbs♭2 : ∀ {A} → ♯ (♭ A) [ 1m ]⊢ ♯ A
    ♯absorbs♭2 = ◯func counit

  
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



    -- seems like Δ (F Δm) and ∇ (U ∇m) are full and faithful but Γ (the other two) is not?

    FΔ-fullandfaithful : ∀ {A B} → F Δm A [ 1m ]⊢ F Δm B -> A [ 1m ]⊢ B
    FΔ-fullandfaithful D = cut {α = 1m} {β = 1m} (cut {α = 1m} {β = 1m} Ffunc12 (Ffunc∘2 {α = ∇m} {β = Δm})) (cut {α = 1m} {β = 1m} (Ffunc {α = ∇m} D) (cut (Ffunc∘1 {α = ∇m} {β = Δm}) Ffunc11))

    -- seems like it works
    FΔ-fullandfaithful-composite-1 : (D : P [ 1m ]⊢ Q) → FΔ-fullandfaithful (Ffunc D) == D
    FΔ-fullandfaithful-composite-1 D = {!!}

    -- FIXME ????
    FΔ-fullandfaithful-composite-2 : (D : F Δm P [ 1m ]⊢ F Δm Q) → (Ffunc (FΔ-fullandfaithful D)) == D
    FΔ-fullandfaithful-composite-2 D = {!!}


    U∇-fullandfaithful : ∀ {A B} → U ∇m A [ 1m ]⊢ U ∇m B -> A [ 1m ]⊢ B
    U∇-fullandfaithful D = cut collapse∇1 (cut (Ffunc {α = ∇m} D) collapse∇2)

    -- seems OK
    U∇-fullandfaithful-composite-1 : (D : P [ 1m ]⊢ Q) -> D == (U∇-fullandfaithful (Ufunc D))
    U∇-fullandfaithful-composite-1 D = {!!}

    -- ??? 
    U∇-fullandfaithful-composite-2 : (D : U ∇m P [ 1m ]⊢ U ∇m Q) -> D == (Ufunc (U∇-fullandfaithful D))
    U∇-fullandfaithful-composite-2 D = {!♭!}


    -- doesn't seem like this exists?
    F∇-fullandfaithful : ∀ {A B} → F ∇m A [ 1m ]⊢ F ∇m B -> A [ 1m ]⊢ B
    F∇-fullandfaithful D = cut {α = 1m} {β = 1m} (cut {!F2 ∇Δunit!} (Ffunc∘2 {α = Δm} {β = ∇m})) (cut {α = 1m} {β = 1m} (Ffunc {α = Δm} D) (cut (Ffunc∘1 {α = Δm} {β = ∇m}) (cut (F2 ∇Δunit) Ffunc11)))
      -- cut {α = 1m} {β = 1m} (cut {!NO!} (Ffunc mergeUF)) (cut {α = 1m} {β = 1m} (Ffunc {α = Δm} D) (cut (Ffunc∘1 {α = Δm} {β = ∇m}) (cut (F2 ∇Δunit) Ffunc11)))




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

      

