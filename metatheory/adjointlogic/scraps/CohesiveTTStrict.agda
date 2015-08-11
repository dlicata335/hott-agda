-- requires Agda 2.4.2.3 or later for the rewrite stuff

open import Agda.Primitive

module metatheory.CohesiveTTStrict where

  -- REWRITE seems to need the level-polymorphic identity type
  data _==_ {A : Set} (M : A) : A → Set where
    id : M == M

  ap :  {A B : Set} {M N : A}
       (f : A → B) → M == N → (f M) == (f N)
  ap f id = id

 
  -- use postulates rather than variables so the rewrite mechanism works
  -- don't want a datatype because we don't want elims

  {-# BUILTIN REWRITE _==_ #-}

  postulate
    Mode : Set 

    _≤_ : Mode -> Mode -> Set 
    1m : {m : Mode} → m ≤ m
    _·1_ : {x y z : Mode} → x ≤ y → y ≤ z → x ≤ z

    ·1-unit-l : ∀ {x y : Mode} {α : x ≤ y} → (1m ·1 α) == α
    ·1-unit-r : ∀ {x y : Mode} {α : x ≤ y} → (α ·1 1m) == α
    ·1-assoc  : ∀ {x y z w : Mode} {α : x ≤ y} {β : y ≤ z} {γ : z ≤ w} → ((α ·1 β) ·1 γ) == (α ·1 (β ·1 γ))

  {-# REWRITE ·1-unit-l #-}
  {-# REWRITE ·1-unit-r #-}
  {-# REWRITE ·1-assoc #-}

  postulate
    _⇒_ : ∀ {p q} → (α β : p ≤ q) → Set 
    1⇒ : ∀ {p q} → {α : p ≤ q} → α ⇒ α
    _·2_ : {x y : Mode} {p q r : x ≤ y} → p ⇒ q → q ⇒ r → p ⇒ r
    _·1cong_ : {x y z : Mode} {p p' : x ≤ y} {q q' : y ≤ z} → p ⇒ p' → q ⇒ q' → (p ·1 q) ⇒ (p' ·1 q')

  postulate
    ·1cong-unit-l : {x z : Mode} {q q' : x ≤ z} (β : q ⇒ q') → (1⇒ {_}{_}{1m} ·1cong β) == β
    ·1cong-unit-r : {x z : Mode} {q q' : x ≤ z} (β : q ⇒ q') → (β ·1cong 1⇒ {_}{_}{1m} ) == β
    ·2-unit-r : {x y : Mode} {p q : x ≤ y} (α : p ⇒ q) → (α ·2 1⇒) == α
    ·2-unit-l : {x y : Mode} {p q : x ≤ y} (α : p ⇒ q) → (1⇒ ·2 α) == α
    ·1cong-1⇒ : {x y z : Mode} {p : x ≤ y} {q : y ≤ z} → (1⇒ {_}{_}{p} ·1cong 1⇒ {_}{_}{q}) == 1⇒
    -- FIXME more equations on 2-cells?

  {-# REWRITE ·1cong-unit-l #-}
  {-# REWRITE ·1cong-unit-r #-}
  {-# REWRITE ·2-unit-r #-}
  {-# REWRITE ·2-unit-l #-}
  {-# REWRITE ·1cong-1⇒ #-}
  
  data Tp : Mode → Set where
    P : ∀ {m} → Tp m
    F : ∀ {p q} (α : p ≤ q) → Tp q → Tp p
    U : ∀ {p q} (α : p ≤ q) → Tp p → Tp q 
    _⊕_ : ∀ {p} (A B : Tp p) → Tp p

  data _[_]⊢_ : {p q : Mode} → Tp q → p ≤ q → Tp p -> Set where
    hypp : ∀ {p} {α : p ≤ p} → α ⇒ 1m → P [ α ]⊢ P 
    FL : ∀ {p q r} {α : p ≤ q} {β : r ≤ p} {A : Tp q} {C : Tp r}
       → A [ β ·1 α ]⊢ C
       → F α A [ β ]⊢ C
    FR : ∀ {p q r} {α : p ≤ q} {β : p ≤ r} {A : Tp q} {C : Tp r}
       → (γ : q ≤ r) → β ⇒ (α ·1 γ)
       → C [ γ ]⊢ A
       → C [ β ]⊢ F α A
    UL : ∀ {p q r} {α : q ≤ p} {β : r ≤ p} {A : Tp q} {C : Tp r}
       → (γ : r ≤ q) → β ⇒ (γ ·1 α)
       → A [ γ ]⊢ C
       → U α A [ β ]⊢ C
    UR : ∀ {p q r} {α : q ≤ p} {β : p ≤ r} {A : Tp q} {C : Tp r}
       → C [ α ·1 β ]⊢ A
       → C [ β ]⊢ U α A
    Inl : ∀ {p q} {α : p ≤ q} {C : Tp q} {A B : Tp p} → C [ α ]⊢ A → C [ α ]⊢ (A ⊕ B)
    Inr : ∀ {p q} {α : p ≤ q} {C : Tp q} {A B : Tp p} → C [ α ]⊢ B → C [ α ]⊢ (A ⊕ B)
    Case : ∀ {p q} {α : p ≤ q} {C : Tp p} {A B : Tp q} → A [ α ]⊢ C → B [ α ]⊢ C → (A ⊕ B) [ α ]⊢ C

  transport⊢ : {p q : Mode} → {A : Tp q} → {α β : p ≤ q} {B : Tp p} 
             → β ⇒ α
             → A [ α ]⊢ B 
             → A [ β ]⊢ B 
  transport⊢ e (hypp e') = hypp (e ·2 e')
  transport⊢ e (FL D) = FL (transport⊢ (e ·1cong 1⇒) D)
  transport⊢ e (FR γ e' D) = FR γ (e ·2 e') D
  transport⊢ e (UL γ e' D) = UL γ (e ·2 e') D
  transport⊢ e (UR D) = UR (transport⊢ (1⇒ ·1cong e) D)
  transport⊢ e (Inl D) = Inl (transport⊢ e D)
  transport⊢ e (Inr D) = Inr (transport⊢ e D)
  transport⊢ e (Case D1 D2) = Case (transport⊢ e D1) (transport⊢ e D2)

  -- FIXME does this make sense?
  postulate
    FR2 : ∀ {p q r} {α : p ≤ q} {β : p ≤ r} {A : Tp q} {C : Tp r}
         → {γ γ' : q ≤ r} → {e : β ⇒ (α ·1 γ)} {e' : β ⇒ (α ·1 γ')} {D : C [ γ ]⊢ A}  {D' : C [ γ' ]⊢ A} 
         → (γ2 : γ ⇒ γ') (e2 : (e ·2 (1⇒ ·1cong γ2)) == e') (D2 : D == (transport⊢ γ2 D'))
         → FR γ e D == FR γ' e' D' 

    UL2 : ∀ {p q r} {α : r ≤ p} {β : q ≤ p} {A : Tp q} {C : Tp r}
         → {γ γ' : q ≤ r} → {e : β ⇒ (γ ·1 α)} {e' : β ⇒ (γ' ·1 α)} {D : C [ γ ]⊢ A}  {D' : C [ γ' ]⊢ A} 
         → (γ2 : γ ⇒ γ') (e2 : (e ·2 (γ2 ·1cong 1⇒)) == e') (D2 : D == (transport⊢ γ2 D'))
         → UL γ e D == UL γ' e' D' 


  -- seems to only work for 1m
  eta : ∀ {p} (A : Tp p) → A [ 1m ]⊢ A
  eta P = hypp 1⇒
  eta (U α A) = (UR {α = α} {β = 1m} (UL 1m 1⇒ (eta A)))  -- need to annote because it infers the wrong association
  eta (F α A) = FL (FR 1m 1⇒ (eta A)) 
  eta (A ⊕ B) = Case (Inl (eta A)) (Inr (eta B))

  cut : ∀ {p q r} {α : p ≤ q} {β : q ≤ r} {A : Tp r} {B : Tp q} {C : Tp p}
      → A [ β ]⊢ B
      → B [ α ]⊢ C
      → A [ α ·1 β ]⊢ C
  -- atom
  cut (hypp p) (hypp q) = hypp (q ·1cong p)
  -- principal 
  cut {α = α} {β = β} (FR γ e D) (FL {α = α1} E) = transport⊢ (1⇒ ·1cong e) (cut D E)
  cut {α = α} {β = β} (UR {α = α1} D) (UL γ₁ e E) = transport⊢ (e ·1cong 1⇒) (cut D E)
  cut {α = α} {β = β} (Inl D) (Case E1 E2) = cut D E1
  cut {α = α} {β = β} (Inr D) (Case E1 E2) = cut D E2
  -- right commutative
  cut {α = α} {β = β} D (FR {α = α'} γ e E) = FR (γ ·1 β) (e ·1cong 1⇒) (cut D E)
  cut {α = α} {β = β} D (UR {α = α1} E) = UR (cut D E)
  cut {α = α} {β = β} D (Inl E) = Inl (cut D E)
  cut {α = α} {β = β} D (Inr E) = Inr (cut D E)
  -- left commutative
  cut {α = α} {β = β} (FL {α = α1} D) E = FL {α = α1} {β = α ·1 β} (cut D E)
  cut {α = α} {β = β} (UL {α = α'} γ e D) E = UL (α ·1 γ) (1⇒ ·1cong e) (cut D E)
  cut {α = α} {β = β} (Case D1 D2) E = Case (cut D1 E) (cut D2 E)
    
  hyp : ∀ {p} {A : Tp p} → A [ 1m ]⊢ A
  hyp = eta _ 
{-

    hyp' : ∀ {p} {A : Tp p} {α : p ≤ p} → α ⇒ 1m → A [ α ]⊢ A
    hyp' e = transport⊢ e hyp

    cut1 : ∀ {p q} {α : q ≤ p} {A : Tp p} {B : Tp q} {C : Tp q}
          → A [ α ]⊢ B → B [ 1m ]⊢ C → A [ α ]⊢ C
    cut1 D E = transport⊢ !·1-unit-l (cut D E)

    cut1' : ∀ {p q} {α : q ≤ p} {A : Tp p} {B : Tp p} {C : Tp q}
          → A [ 1m ]⊢ B → B [ α ]⊢ C → A [ α ]⊢ C
    cut1' D E = transport⊢ !·1-unit-r (cut D E)
-}

  cut-eta-right : ∀ {p q} {α : p ≤ q} {A B} → (D : A [ α ]⊢ B)
                  → cut D (eta B) == D
  cut-eta-right (hypp e) = id
  cut-eta-right (FL D) = {!!} 
  cut-eta-right (FR γ e D) = {!!}
  cut-eta-right (UL γ e D) = {!!}
  cut-eta-right (UR D) = {!!}
  cut-eta-right (Inl D) = {!ap Inl (cut-eta-right D)!}
  cut-eta-right (Inr D) = {!!}
  cut-eta-right (Case D1 D2) = {!!}

{-
    -- ----------------------------------------------------------------------
    -- examples

    -- F α and F β are different for two parallel but different α and β
    diff1 : {p q : Mode} {α β : p ≤ q} {A : Tp q} → F α A [ 1m ]⊢ F β A
    diff1 = FL (FR 1m {!NO!} hyp)

    diff2 : {p q : Mode} {α β : p ≤ q} {A : Tp p} → U α A [ 1m ]⊢ U β A
    diff2 = UR (UL 1m {!NO!} hyp)

    -- functoriality of F and U in the category
    -- U is contravariant
  
    Ffunc11 : ∀ {p} {A : Tp p} → F 1m A [ 1m ]⊢ A
    Ffunc11 = FL (hyp' ·1-unit-l)

    Ffunc12 : ∀ {p} {A : Tp p} → A [ 1m ]⊢ F 1m A
    Ffunc12 = FR 1m !·1-unit-l hyp
  
    Ffunc·1 : ∀ {x y z : Mode} {α : x ≤ y} {β : y ≤ z} {A : Tp _}
            → F α (F β A) [ 1m ]⊢ F (α ·1 β) A
    Ffunc·1 {β = β} = FL (FL (FR 1m ((·1-unit-l ·1cong 1⇒) ·2 !·1-unit-r) hyp))

    Ffunc·2 : ∀ {x y z : Mode} {α : x ≤ y} {β : y ≤ z} {A : Tp _}
            → F (α ·1 β) A [ 1m ]⊢ F α (F β A)
    Ffunc·2 {α = α} {β = β} = FL (FR β ·1-unit-l (FR 1m !·1-unit-r hyp))
    
    Ufunc11 : ∀ {p} {A : Tp p} → U 1m A [ 1m ]⊢ A
    Ufunc11 = UL 1m !·1-unit-l hyp

    Ufunc12 : ∀ {p} {A : Tp p} → A [ 1m ]⊢ U 1m A
    Ufunc12 = UR (hyp' ·1-unit-r)
  
    Ufunc·1 : ∀ {x y z : Mode} {α : x ≤ y} {β : y ≤ z} {A : Tp _}
            → U β (U α A) [ 1m ]⊢ U (α ·1 β) A
    Ufunc·1 {α = α} {β = β} = UR (UL α ·1-unit-r (UL 1m !·1-unit-l hyp))

    Ufunc·2 : ∀ {x y z : Mode} {α : x ≤ y} {β : y ≤ z} {A : Tp _}
            → U (α ·1 β) A [ 1m ]⊢ U β (U α A)
    Ufunc·2 {α = α} {β = β} = UR (UR (UL 1m ((1⇒ ·1cong ·1-unit-r) ·2 !·1-unit-l) hyp)) 

    -- functors are actually functors
    Ffunc : ∀ {p q : Mode} {α : p ≤ q} {A B} → A [ 1m ]⊢ B → F α A [ 1m ]⊢ F α B
    Ffunc D =  FL (FR 1m (·1-unit-l ·2 !·1-unit-r) D)

    Ufunc : ∀ {p q : Mode} {α : p ≤ q} {A B} → A [ 1m ]⊢ B → U α A [ 1m ]⊢ U α B
    Ufunc D =  UR (UL 1m (·1-unit-r ·2 !·1-unit-l) D)

    -- adjoints are actually adjoint
    UFadjunction1 : ∀ {p q} {A B} {α : p ≤ q} → F α A [ 1m ]⊢ B → A [ 1m ]⊢ U α B
    UFadjunction1 {α = α} start = UR (cut1 (FR 1m 1⇒ hyp) start)

    UFadjunction2 : ∀ {p q} {A B} {α : p ≤ q} → A [ 1m ]⊢ U α B → F α A [ 1m ]⊢ B 
    UFadjunction2 {α = α} start = FL (cut1' start (UL 1m 1⇒ hyp))

    -- monads

    □ : ∀ {p q} (α : p ≤ q) → Tp p → Tp p 
    □ α A = F α (U α A)

    ◯ : ∀ {p q} (α : p ≤ q) → Tp q → Tp q 
    ◯ α A = U α (F α A)

    □func : ∀ {p q : Mode} {α : p ≤ q} {A B} → A [ 1m ]⊢ B → □ α A [ 1m ]⊢ □ α B
    □func D = Ffunc (Ufunc D)

    ◯func : ∀ {p q : Mode} {α : p ≤ q} {A B} → A [ 1m ]⊢ B → ◯ α A [ 1m ]⊢ ◯ α B
    ◯func D = Ufunc (Ffunc D)

    unit : {p q : Mode} {A : Tp q} {α : p ≤ q} → A [ 1m ]⊢ ◯ α A
    unit {α = α} = UR (FR 1m 1⇒ hyp)

    mult : {p q : Mode} {A : Tp q} {α : p ≤ q} → ◯ α (◯ α A) [ 1m ]⊢ ◯ α A
    mult {α = α} = UR (UL 1m (·1-unit-r ·2 !·1-unit-l) (FL (UL 1m 1⇒ hyp))) 

    counit : {p q : Mode} {A : Tp p} {α : p ≤ q} → □ α A [ 1m ]⊢ A
    counit = FL (UL 1m 1⇒ hyp)

    comult : {p q : Mode} {A : Tp p} {α : p ≤ q} → □ α A [ 1m ]⊢ □ α (□ α A)
    comult {α = α} = FL (FR 1m (·1-unit-l ·2 !·1-unit-r) (UR (FR 1m 1⇒ hyp))) 

    -- need α "inverse"  β · α ⇒ 1m
    badcounit : {p q : Mode} {A : Tp q} {α : p ≤ q} → ◯ α A [ 1m ]⊢ A
    badcounit = UL {!!} {!NO!} (FL {!!}) 

    -- need α "inverse" on the other side  α · β ⇒ 1
    badunit : {p q : Mode} {A : Tp p} {α : p ≤ q} → A [ 1m ]⊢ □ α A
    badunit = FR {!!} {!NO!} (UR {!!})

    F2 : ∀ {p q} {A B : Tp q} {α β : p ≤ q} → α ⇒ β → F α A [ 1m ]⊢ F β A
    F2 e = FL (FR 1m ((·1-unit-l ·2 e) ·2 !·1-unit-r) hyp)

    U2 : ∀ {p q} {A B : Tp p} {α β : p ≤ q} → β ⇒ α → U α A [ 1m ]⊢ U β A
    U2 e = UR (UL 1m ((·1-unit-r ·2 e) ·2 !·1-unit-l) hyp)

-}

  module TripleAdjunction where
    postulate
      c : Mode
      s : Mode
      ∇m : s ≤ c
      Δm : c ≤ s
      ∇Δunit   : 1m ⇒ (∇m ·1 Δm)
      Δ∇counit : (Δm ·1 ∇m) ⇒ 1m 

      -- η = unit
      -- ε = counit
      -- F = ∇ 
      -- G = Δ

      -- ηG · Gε = 1   but 1-composition is backwards so   Gη · εG  = 1
      adjeq1 : ((1⇒{c}{s}{Δm} ·1cong ∇Δunit) ·2 (Δ∇counit ·1cong 1⇒{_}{_}{Δm})) == 1⇒
 
      -- Fη · εF = 1   but 1-composition is backwards so   ηF · Fε
      adjeq2 : ((∇Δunit ·1cong  1⇒{_}{_}{∇m})  ·2 (1⇒{_}{_}{∇m} ·1cong Δ∇counit)) == 1⇒

    mergeUF : ∀ {A : Tp c} → U Δm A [ 1m ]⊢ F ∇m A
    mergeUF = FR Δm ∇Δunit (UL 1m 1⇒ hyp) 

    mergeUF' : ∀ {A : Tp c} → U Δm A [ 1m ]⊢ F ∇m A 
    mergeUF' = UL ∇m ∇Δunit (FR 1m 1⇒ hyp)

    mergeFU : ∀ {A : Tp c} → F ∇m A [ 1m ]⊢ U Δm A
    mergeFU = FL {α = ∇m} {β = 1m} (UR (transport⊢ Δ∇counit hyp))

    inv1 : cut (mergeUF{P}) (mergeFU {P}) == eta (U Δm P)
    inv1 = ap (UR {α = Δm} {β = 1m ·1 1m}) (UL2 {D = cut hyp (hypp (Δ∇counit ·2 1⇒))} {D' = eta P} Δ∇counit adjeq1 id)

    inv2 : cut (mergeFU {P}) (mergeUF'{P}) == eta (F ∇m P)
    inv2 = ap (FL {α = ∇m} {β = 1m ·1 1m}) (FR2 {D = cut (hypp (Δ∇counit ·2 1⇒)) hyp} {D' = eta P} Δ∇counit adjeq2 id) 
      
{-  
      badmergeUF : ∀ {A : Tp s} → U ∇m A [ 1m ]⊢ F Δm A
      badmergeUF = UL Δm {!NO!} (FR 1m !·1-unit-r hyp)
  
      badmergeUF' : ∀ {A : Tp s} → U ∇m A [ 1m ]⊢ F Δm A
      badmergeUF' = FR ∇m {!NO!} (UL 1m !·1-unit-l hyp) 
  
      badmergeFU : ∀ {A : Tp s} → F Δm A [ 1m ]⊢ U ∇m A
      badmergeFU = FL (UR (hyp' {!NO!}))
  
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
        step2 = cut1 (cut1 mergeFU step1) mergeUF
  
      ♭♯adjunction2 : ∀ {A B} → A [ 1m ]⊢ ♯ B → ♭ A [ 1m ]⊢ B 
      ♭♯adjunction2 {A}{B} start = UFadjunction2 (cut1 mergeUF (cut1 (UFadjunction2 start) mergeFU))

      pres-coprod1 : ∀ {A B} → ♭ (A ⊕ B) [ 1m ]⊢ (♭ A ⊕ ♭ B)
      pres-coprod1 = ♭♯adjunction2 (Case (♭♯adjunction1 (Inl hyp)) (♭♯adjunction1 (Inr hyp)))

      pres-coprod2 : ∀ {A B} → (♭ A ⊕ ♭ B) [ 1m ]⊢ ♭ (A ⊕ B)
      pres-coprod2 = Case (□func (Inl hyp)) (□func (Inr hyp))


      -- mike's rules from the pfenning-davies style

      -- rule 1
      
      -- Δ ; · ⊢ M :~ A  
      -- ---------------
      -- Δ ; · ⊢ M : A

      rule1 : ∀ {D A} 
             → D [ 1m ]⊢ F ∇m A
             → D [ 1m ]⊢ U Δm A
      rule1 E = cut1 E mergeFU

      -- ♭ ♯ A → A
      rule1prop : ∀ {A} → ♭ (♯ A) [ 1m ]⊢ A
      rule1prop = ♭♯adjunction2 hyp
      
      -- rule 2:
      -- ♭ A ⊢ ♯ C    A valid ⊢ C lax
      -- ---------   ----------------
      -- A ⊢ ♯ C      A true ⊢ C lax

      rule2 : ∀ {A C} 
             → U Δm A [ 1m ]⊢ F ∇m C
             → A [ ∇m ]⊢ F ∇m C 
      rule2 D = cut1 (FR 1m !·1-unit-r hyp) (cut1 mergeFU D)

      rule2prop : ∀ {A C} → ♭ A [ 1m ]⊢ ♯ C  →  A [ 1m ]⊢ ♯ C
      rule2prop D = cut1 (♭♯adjunction1 D) mult

      
      -- ♭ absorbing ♯ and vice versa
      
      ♭absorbs♯1 : ∀ {A} → ♭ A [ 1m ]⊢ ♭ (♯ A) 
      ♭absorbs♯1 = □func unit

      ♭absorbs♯2 : ∀ {A} → ♭ (♯ A) [ 1m ]⊢ ♭ A
      ♭absorbs♯2 = FL (transport⊢ ·1-unit-l (FR 1m !·1-unit-r (UL ∇m ∇Δunit (UL 1m !·1-unit-l mergeFU))))

      ♯absorbs♭1 : ∀ {A} → ♯ A [ 1m ]⊢ ♯ (♭ A) 
      ♯absorbs♭1 = UR (transport⊢ ·1-unit-r (UL 1m !·1-unit-l (FR Δm ∇Δunit (FR 1m !·1-unit-r mergeFU))))

      ♯absorbs♭2 : ∀ {A} → ♯ (♭ A) [ 1m ]⊢ ♯ A
      ♯absorbs♭2 = ◯func counit


      -- idempotence 

      ♯idempotent1 : ∀ {A} → ♯ A [ 1m ]⊢ ♯ (♯ A)
      ♯idempotent1 = unit

      ♯idempotent2 : ∀ {A} → ♯ (♯ A) [ 1m ]⊢ ♯ A
      ♯idempotent2 = mult

      ♯idempotent12 : cut1 (♯idempotent1 {P}) ♯idempotent2 == eta (♯ P)
      ♯idempotent12 = {!!} where
        
        afterind : Path{ P [ 1m ]⊢ ♯ P} (cut1 unit (cut1 (♯idempotent1 {P}) ♯idempotent2)) unit
        afterind = {!!}

      ♯idempotent21 : cut1 ♯idempotent2 (♯idempotent1 {P}) == eta (♯ (♯ P))
      ♯idempotent21 = {!!} where
        
        afterind : Path{ ♯ P [ 1m ]⊢ ♯ (♯ P)} (cut1 unit (cut1 (♯idempotent2 {P}) ♯idempotent1)) unit
        afterind = {!!}

      -- ♯idempotent12 : ∀ {A} → cut1 cut1 (♯idempotent1 {A}) ♯idempotent2 == eta (♯ A)
      -- ♯idempotent12 = {!!}

-}

  module IdempotentMonad where
    postulate
      m    : Mode
      T    : m ≤ m
      unit : 1m ⇒ T
      mult : (T ·1 T) ⇒ T 
      -- monad laws for unit and mult
      -- equations that mult and l(unit) are mutually inverse


      
