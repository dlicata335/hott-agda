
{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude

module metatheory.CohesiveTT where

module TT (Mode : Type) 
          (_≤_ : Mode -> Mode -> Type)
          (1m : {m : Mode} → m ≤ m)
          (_·m_ : {x y z : Mode} → x ≤ y → y ≤ z → x ≤ z)
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
         → A [ β ·m α ]⊢ C
         → F α A [ β ]⊢ C
      FR : ∀ {p q r} {α : p ≤ q} {β : p ≤ r} {A : Tp q} {C : Tp r}
         → (γ : q ≤ r) → α ·m γ == β
         → C [ γ ]⊢ A
         → C [ β ]⊢ F α A
      UL : ∀ {p q r} {α : q ≤ p} {β : r ≤ p} {A : Tp q} {C : Tp r}
         → (γ : r ≤ q) → γ ·m α == β
         → A [ γ ]⊢ C
         → U α A [ β ]⊢ C
      UR : ∀ {p q r} {α : q ≤ p} {β : p ≤ r} {A : Tp q} {C : Tp r}
         → C [ α ·m β ]⊢ A
         → C [ β ]⊢ U α A

    hyp' : ∀ {p} {A : Tp p} {α : p ≤ p} → α == 1m → A [ α ]⊢ A
    hyp' id = hyp 

{-    
module TripleAdjunction where

  data Mode : Type where
    c : Mode
    s : Mode

  -- FIXME: make a HIT
  data _≤_ : Mode → Mode → Type where
    1m : {m : Mode} → m ≤ m
    _·m_ : {x y z : Mode} → x ≤ y → y ≤ z → x ≤ z
    ∇m : s ≤ c 
    Δm : c ≤ s
    
  postulate 
    retract : Δm ·m ∇m == 1m {c}
    ·m-unit-l : ∀ {x y : Mode} {α : x ≤ y} → 1m ·m α == α
    ·m-unit-r : ∀ {x y : Mode} {α : x ≤ y} → α ·m 1m == α
    -- FIXME : assoc

  module TTI = TT Mode _≤_ 1m _·m_
  open TTI

  -- two possible definitions of Γ are (logically) equivalent

  Γeqv1 : ∀ {A : Tp c} → U Δm A [ 1m ]⊢ F ∇m A
  Γeqv1 = UL ∇m {!!} (FR 1m ·m-unit-r hyp) -- FR {!!} {!!} (UL {!!} {!retract!} {!!})

  Γeqv2 : ∀ {A : Tp c} → F ∇m A [ 1m ]⊢ U Δm A
  Γeqv2 = UR (FL (hyp' (retract ∘ ap (λ x → x ·m ∇m) ·m-unit-r)))

  bad : ∀ {A : Tp s} → U ∇m A [ 1m ]⊢ F Δm A
  bad = FR ∇m {!!} (UL 1m ·m-unit-l hyp)

  bad' : ∀ {A : Tp s} → F Δm A [ 1m ]⊢ U ∇m A
  bad' = UR (FL (hyp' ({!!} ∘ ap (λ x → x ·m Δm) ·m-unit-r)))

  -- monad/comonad stuff
  unit : {p q : Mode} {A : Tp q} {α : p ≤ q} → A [ 1m ]⊢ U α (F α A)
  unit = UR (FR 1m id hyp)

  counit : {p q : Mode} {A : Tp p} {α : p ≤ q} → F α (U α A) [ 1m ]⊢ A
  counit = FL (UL 1m id hyp)

  -- need α inverse
  badcounit : {p q : Mode} {A : Tp q} {α : p ≤ q} → U α (F α A) [ 1m ]⊢ A
  badcounit = UL {!!} {!!} (FL (hyp' {!!}))

  -- need α inverse on the other side
  badunit : {p q : Mode} {A : Tp p} {α : p ≤ q} → A [ 1m ]⊢ F α (U α A)
  badunit = FR {!!} {!!} (UR (hyp' {!!}))
-}

module TripleAdjunction where

  data Mode : Type where
    c : Mode
    s : Mode

  -- FIXME: make a HIT
  data _≤_ : Mode → Mode → Type where
    1m : {m : Mode} → m ≤ m
    _·m_ : {x y z : Mode} → x ≤ y → y ≤ z → x ≤ z
    ∇m : s ≤ c 
    Δm : s ≤ c
    
  postulate 
    ·m-unit-l : ∀ {x y : Mode} {α : x ≤ y} → 1m ·m α == α
    ·m-unit-r : ∀ {x y : Mode} {α : x ≤ y} → α ·m 1m == α
    -- FIXME : assoc

  module TTI = TT Mode _≤_ 1m _·m_
  open TTI

  -- two possible definitions of Γ are (logically) equivalent

  -- Γeqv1 : ∀ {A : Tp c} → U Δm A [ 1m ]⊢ F ∇m A
  -- Γeqv1 = UL ∇m {!!} (FR 1m ·m-unit-r hyp) -- FR {!!} {!!} (UL {!!} {!retract!} {!!})

  -- Γeqv2 : ∀ {A : Tp c} → F ∇m A [ 1m ]⊢ U Δm A
  -- Γeqv2 = UR (FL ?)

  -- bad : ∀ {A : Tp s} → U ∇m A [ 1m ]⊢ F Δm A
  -- bad = FR ∇m {!!} (UL 1m ·m-unit-l hyp)

  -- bad' : ∀ {A : Tp s} → F Δm A [ 1m ]⊢ U ∇m A
  -- bad' = UR (FL (hyp' ({!!} ∘ ap (λ x → x ·m Δm) ·m-unit-r)))

  -- monad/comonad stuff
  unit : {p q : Mode} {A : Tp q} {α : p ≤ q} → A [ 1m ]⊢ U α (F α A)
  unit = UR (FR 1m id hyp)

  counit : {p q : Mode} {A : Tp p} {α : p ≤ q} → F α (U α A) [ 1m ]⊢ A
  counit = FL (UL 1m id hyp)

  -- need α inverse
  badcounit : {p q : Mode} {A : Tp q} {α : p ≤ q} → U α (F α A) [ 1m ]⊢ A
  badcounit = UL {!!} {!!} (FL (hyp' {!!}))

  -- need α inverse on the other side
  badunit : {p q : Mode} {A : Tp p} {α : p ≤ q} → A [ 1m ]⊢ F α (U α A)
  badunit = FR {!!} {!!} (UR (hyp' {!!}))

  -- need α = β 
  diff1 : {p q : Mode} {α β : p ≤ q} {A : Tp q} → F α A [ 1m ]⊢ F β A
  diff1 = FL (FR 1m {!!} hyp)

  diff2 : {p q : Mode} {α β : p ≤ q} {A : Tp p} → U α A [ 1m ]⊢ U β A
  diff2 = UR (UL 1m {!!} hyp)

  want1 : {p q : Mode} {α : p ≤ q} {β : q ≤ p} {A : Tp q} → F α A [ 1m ]⊢ U β A
  want1 = FL (UR {!!})

  -- need α ·m β == 1m
  want2 : {p q : Mode} {α : p ≤ q} {β : q ≤ p} {A : Tp q} → U β A [ 1m ]⊢ F α A
  want2 {α = α} {β = β} = UL α {!!} (FR 1m ·m-unit-r hyp)

