
{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude

module metatheory.CohesiveTT1 where

module TT (Mode : Type) 
          (_≤_ : Mode -> Mode -> Type)
          (1m : {m : Mode} → m ≤ m)
          (CanFoc : {x y z : Mode} → x ≤ y → y ≤ z → x ≤ z → Type)
          (CanInv : {x y z : Mode} → x ≤ y → y ≤ z → x ≤ z → Type)
          -- category 
          where

    data Tp : Mode → Type where
      ⊤ : ∀ {m} → Tp m 
      F : ∀ {p q} (α : p ≤ q) → Tp q → Tp p
      U : ∀ {p q} (α : p ≤ q) → Tp p → Tp q 

    data _[_]⊢_ : {p q : Mode} → Tp q → p ≤ q → Tp p -> Type where
      ⊤R : ∀ {p r} {α : p ≤ r} (C : Tp r) → C [ α ]⊢ ⊤
      hyp : ∀ {p} {A : Tp p} → A [ 1m ]⊢ A
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

    hyp' : ∀ {p} {A : Tp p} {α : p ≤ p} → α == 1m → A [ α ]⊢ A
    hyp' id = hyp 


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

  data Mode : Type where
    c : Mode
    s : Mode

  -- FIXME: make a HIT
  data _≤_ : Mode → Mode → Type where
    1m : {m : Mode} → m ≤ m
    ∇m : s ≤ c 
    Δm : c ≤ s
    
  data CanFoc : {x y z : Mode} → x ≤ y → y ≤ z → x ≤ z → Type where
    cf1 : ∀ {x y} {α : x ≤ y} → CanFoc 1m α α
    cf1' : ∀ {x y} {α : x ≤ y} → CanFoc α 1m α
    cf3 : CanFoc ∇m Δm 1m

  data CanInv : {x y z : Mode} → x ≤ y → y ≤ z → x ≤ z → Type where
    ci1' : ∀ {x y} {α : x ≤ y} → CanInv α 1m α
    ci1 : ∀ {x y} {α : x ≤ y} → CanInv 1m α α
    ci2 : CanInv Δm ∇m 1m

  module TTI = TT Mode _≤_ 1m CanFoc CanInv
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
  badcounit : {p q : Mode} {A : Tp q} {α : p ≤ q} → U α (F α A) [ 1m ]⊢ A
  badcounit = UL {!!} {!!} (FL 1m {!!} hyp)

  -- need α "inverse" on the other side
  badunit : {p q : Mode} {A : Tp p} {α : p ≤ q} → A [ 1m ]⊢ □ α A
  badunit = FR {!!} {!!} (UR 1m {!!} hyp)

  ♭ = □ Δm
  ♯ = ◯ ∇m

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

