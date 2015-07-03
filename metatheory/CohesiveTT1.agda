
{-# OPTIONS --type-in-type #-}

open import lib.Prelude

module metatheory.CohesiveTT1 where

module TT (Mode : Set) 
          (_≤_ : Mode -> Mode -> Set)
          (1m : {m : Mode} → m ≤ m)
          (_·m_ : {x y z : Mode} → x ≤ y → y ≤ z → x ≤ z)
          (CanFoc : {x y z : Mode} → x ≤ y → y ≤ z → x ≤ z → Set)
          (CanInv : {x y z : Mode} → x ≤ y → y ≤ z → x ≤ z → Set)
          (ci1 : ∀ {x y} {α : x ≤ y} → CanInv 1m α α)
          (ci1' : ∀ {x y} {α : x ≤ y} → CanInv α 1m α)
          (cf1 : ∀ {x y} {α : x ≤ y} → CanFoc 1m α α)
          (cf1' : ∀ {x y} {α : x ≤ y} → CanFoc α 1m α)
          (CanCut : {x y z : Mode} → x ≤ y → y ≤ z → x ≤ z → Set)
          (cc1 : ∀ {x} {α : x ≤ x} → CanCut 1m 1m α → α == 1m)
          (cc2 : {x y z : Mode} → {α : x ≤ y} → {β : y ≤ z} → CanCut α β (α ·m β))
          -- category 
          where

    data Tp : Mode → Set where
      ⊤ : ∀ {m} → Tp m 
      P : ∀ {m} → Tp m
      F : ∀ {p q} (α : p ≤ q) → Tp q → Tp p
      U : ∀ {p q} (α : p ≤ q) → Tp p → Tp q 

    data _[_]⊢_ : {p q : Mode} → Tp q → p ≤ q → Tp p -> Set where
      hypp : ∀ {p} → P [ 1m{p} ]⊢ P
      ⊤R : ∀ {p r} {α : p ≤ r} {C : Tp r} → C [ α ]⊢ ⊤
      FL : ∀ {p q r} {α : p ≤ q} {β : r ≤ p} {A : Tp q} {C : Tp r}
         → (γ : r ≤ q) → CanInv β α γ
         → A [ γ ]⊢ C
         → F α A [ β ]⊢ C
      FR : ∀ {p q r} {α : p ≤ q} {β : p ≤ r} {A : Tp q} {C : Tp r}
         → (γ : q ≤ r) → CanFoc α γ β 
         → C [ γ ]⊢ A
         → C [ β ]⊢ F α A
      UL : ∀ {p q r} {α : q ≤ p} {β : r ≤ p} {A : Tp q} {C : Tp r}
         → (γ : r ≤ q) → CanFoc γ α β
         → A [ γ ]⊢ C
         → U α A [ β ]⊢ C
      UR : ∀ {p q r} {α : q ≤ p} {β : p ≤ r} {A : Tp q} {C : Tp r}
         → (γ : q ≤ r) → CanInv α β γ
         → C [ γ ]⊢ A
         → C [ β ]⊢ U α A

    eta : ∀ {p} (A : Tp p) → A [ 1m ]⊢ A
    eta P = hypp
    eta ⊤ = ⊤R
    eta (F α A) = FL α ci1 (FR 1m cf1' (eta A))
    eta (U α A) = UR α ci1' (UL 1m cf1 (eta A))
      
    hyp : ∀ {p} {A : Tp p} → A [ 1m ]⊢ A
    hyp = eta _

{-
    cut : ∀ {p q r} {α : p ≤ q} {β : q ≤ r} {A : Tp r} {B : Tp q} {C : Tp p}
        → A [ β ]⊢ B
        → B [ α ]⊢ C
        → A [ α ·m β ]⊢ C
    -- principal 
    cut (FR γ c D) (FL γ₁ c₁ E) = {!cut D E!}
    cut (UR γ c D) (UL γ₁ c₁ E) = {!cut D E!}
    -- right commutative
    cut _ ⊤R = ⊤R
    cut {α = α} {β = β} D (FR {α = α'} γ c E) = FR (γ ·m β) {!congruence c!} (cut D E)
    cut {α = α} {β = β} D (UR {α = α'} γ c E) = UR (γ ·m β) {!congruence c!} (cut D E)
    -- left commutative
    cut {α = α} {β = β} (FL {α = α'} γ c D) E = FL (α ·m γ) {!congruence c!} (cut D E)
    cut {α = α} {β = β} (UL {α = α'} γ c D) E = UL (α ·m γ) {!congruence c!} (cut D E)
-}

    cut : ∀ {p q r} {α : p ≤ q} {β : q ≤ r} {A : Tp r} {B : Tp q} {C : Tp p}
        → A [ β ]⊢ B
        → B [ α ]⊢ C
        → (δ : p ≤ r) → CanCut α β δ → A [ δ ]⊢ C
    -- principal 
    cut hypp hypp δ cc = transport (λ x → P [ x ]⊢ P) (! (cc1 cc)) hyp
    cut (FR γ c D) (FL γ₁ c₁ E) δ cc = cut D E δ {!!}
    cut (UR γ c D) (UL γ₁ c₁ E) δ cc = cut D E δ {!!}
    -- right commutative
    cut _ ⊤R δ cc = ⊤R
    cut {α = α} {β = β} D (FR {α = α'} γ c E) δ cc = FR (γ ·m β) {! c!} (cut D E (γ ·m β) cc2)
    cut {α = α} {β = β} D (UR {α = α'} γ c E) δ cc = UR (γ ·m β) {! c!} (cut D E (γ ·m β) cc2)
    -- left commutative
    cut {α = α} {β = β} (FL {α = α'} γ c D) E δ cc = FL (α ·m γ) {! c!} (cut D E (α ·m γ) cc2)
    cut {α = α} {β = β} (UL {α = α'} γ c D) E δ cc = UL (α ·m γ) {! c!} (cut D E (α ·m γ) cc2)

    -- FIXME generalize
    cut1 : ∀ {p q} {α : q ≤ p} {A : Tp p} {B : Tp q} {C : Tp q}
          → A [ α ]⊢ B
          → B [ 1m ]⊢ C
          → A [ α ]⊢ C
    cut1 = {!!}

    cut1' : ∀ {p q} {α : q ≤ p} {A : Tp p} {B : Tp p} {C : Tp q}
          → A [ 1m ]⊢ B
          → B [ α ]⊢ C
          → A [ α ]⊢ C
    cut1' = {!!}

module TripleAdjunction where

  data Mode : Set where
    c : Mode
    s : Mode

  data _≤_ : Mode → Mode → Set where
    1m : {m : Mode} → m ≤ m
    ∇m : s ≤ c 
    Δm : c ≤ s
    _·m_ : {x y z : Mode} → x ≤ y → y ≤ z → x ≤ z
    
  data CanFoc : {x y z : Mode} → x ≤ y → y ≤ z → x ≤ z → Set where
    cf1 : ∀ {x y} {α : x ≤ y} → CanFoc 1m α α
    cf1' : ∀ {x y} {α : x ≤ y} → CanFoc α 1m α
    cf3 : CanFoc ∇m Δm 1m

  data CanInv : {x y z : Mode} → x ≤ y → y ≤ z → x ≤ z → Set where
    ci1' : ∀ {x y} {α : x ≤ y} → CanInv α 1m α
    ci1 : ∀ {x y} {α : x ≤ y} → CanInv 1m α α
    ci2 : CanInv Δm ∇m 1m

  data CanCut : {x y z : Mode} → x ≤ y → y ≤ z → x ≤ z → Set where
    cc2 : {x y z : Mode} → {α : x ≤ y} → {β : y ≤ z} → CanCut α β (α ·m β)

  cc1 : ∀ {x} {α : x ≤ x} → CanCut 1m 1m α → α == 1m
  cc1 = {!!}

  module TTI = TT Mode _≤_ 1m _·m_ CanFoc CanInv ci1 ci1' cf1 cf1' CanCut cc1 cc2
  open TTI

  -- two possible definitions of Γ are (logically) equivalent

  Γeqv1 : ∀ {A : Tp c} → U Δm A [ 1m ]⊢ F ∇m A
  Γeqv1 = UL ∇m cf3 (FR 1m cf1' hyp) 

  Γeqv1' : ∀ {A : Tp c} → U Δm A [ 1m ]⊢ F ∇m A
  Γeqv1' = FR Δm cf3 (UL 1m cf1 hyp)

  Γeqv2 : ∀ {A : Tp c} → F ∇m A [ 1m ]⊢ U Δm A
  Γeqv2 = UR Δm ci1' (FL 1m ci2 hyp)

  Γeqv2' : ∀ {A : Tp c} → F ∇m A [ 1m ]⊢ U Δm A
  Γeqv2' = FL ∇m ci1 (UR 1m ci2 hyp)

  badΓeqv1 : ∀ {A : Tp s} → U ∇m A [ 1m ]⊢ F Δm A
  badΓeqv1 = FR ∇m {!NO!} (UL 1m cf1 hyp)

  badΓeqv1' : ∀ {A : Tp s} → U ∇m A [ 1m ]⊢ F Δm A
  badΓeqv1' = UL Δm {!NO!} (FR 1m cf1' hyp)

  badΓeqv2 : ∀ {A : Tp s} → F Δm A [ 1m ]⊢ U ∇m A
  badΓeqv2 = UR ∇m ci1' (FL 1m {!NO!} hyp)

  badΓeqv2' : ∀ {A : Tp s} → F Δm A [ 1m ]⊢ U ∇m A
  badΓeqv2' = FL Δm ci1 (UR 1m {!NO!} hyp)

  -- monad/comonad stuff
  □ : ∀ {p q} (α : p ≤ q) → Tp p → Tp p 
  □ α A = F α (U α A)

  ◯ : ∀ {p q} (α : p ≤ q) → Tp q → Tp q 
  ◯ α A = U α (F α A)

  unit : {p q : Mode} {A : Tp q} {α : p ≤ q} → A [ 1m ]⊢ ◯ α A
  unit {α = α} = UR α ci1' (FR 1m cf1' hyp)

  mult : {p q : Mode} {A : Tp q} {α : p ≤ q} → ◯ α (◯ α A) [ 1m ]⊢ ◯ α A
  mult {α = α} = UR α ci1' (UL 1m cf1 (FL α ci1 (UL 1m cf1 hyp)))

  counit : {p q : Mode} {A : Tp p} {α : p ≤ q} → □ α A [ 1m ]⊢ A
  counit { α =  α } = FL α ci1 (UL 1m cf1 hyp)

  comult : {p q : Mode} {A : Tp p} {α : p ≤ q} → □ α A [ 1m ]⊢ □ α (□ α A)
  comult {α = α} = FL α ci1 (FR 1m cf1' (UR α ci1' (FR 1m cf1' hyp)))

  -- need α "inverse"
  badcounit : {p q : Mode} {A : Tp q} {α : p ≤ q} → ◯ α A [ 1m ]⊢ A
  badcounit = UL {!!} {!!} (FL 1m {!!} hyp)

  -- need α "inverse" on the other side
  badunit : {p q : Mode} {A : Tp p} {α : p ≤ q} → A [ 1m ]⊢ □ α A
  badunit = FR {!!} {!!} (UR 1m {!!} hyp)

  ♭ = □ Δm
  ♯ = ◯ ∇m

  badunit' : {A : Tp c}→ A [ 1m ]⊢ ♭ A
  badunit' = FR ∇m {!NO!} (UR 1m ci2 hyp)

  badcounit' : {A : Tp c} → ♯ A [ 1m ]⊢ A
  badcounit' = UL Δm {!NO!} (FL 1m ci2 hyp)

  UFadjunction1 : ∀ {p q} {A B} {α : p ≤ q} → F α A [ 1m ]⊢ B → A [ 1m ]⊢ U α B
  UFadjunction1 {α = α} start = UR α ci1' (cut1 (FR 1m cf1' hyp) start)

  UFadjunction2 : ∀ {p q} {A B} {α : p ≤ q} → A [ 1m ]⊢ U α B → F α A [ 1m ]⊢ B 
  UFadjunction2 {α = α} start = FL α ci1 (cut1' start (UL 1m cf1 hyp))

  adjunction1 : ∀ {A B} → ♭ A [ 1m ]⊢ B → A [ 1m ]⊢ ♯ B
  adjunction1 {A}{B} start = UFadjunction1 step2 where
    step1 : U Δm A [ 1m ]⊢ U Δm B
    step1 = UFadjunction1 start

    step2 : F ∇m A [ 1m ]⊢ F ∇m B
    step2 = cut1 (cut1 Γeqv2 step1) Γeqv1

  adjunction2 : ∀ {A B} → A [ 1m ]⊢ ♯ B → ♭ A [ 1m ]⊢ B 
  adjunction2 {A}{B} start = UFadjunction2 (cut1 Γeqv1 (cut1 (UFadjunction2 start) Γeqv2))

  loop1 : ∀ {p} {A : Tp p} {α : p ≤ p} → A [ 1m ]⊢ F α A
  loop1 {α = α} = FR 1m {!!} hyp -- need CanFoc α 1m 1m
                  -- FR α {!!} {!!} -- need  CanFoc α α 1m
