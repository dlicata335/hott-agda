
-- try to add the equivalence explicitly; not sure how it is supposed to compute

{-# OPTIONS --type-in-type #-}

open import lib.Prelude

module metatheory.CohesiveTT3 where

    data Mode : Type where
      c s : Mode

    -- FIXME: make a HIT
    data _≤_ : Mode -> Mode -> Type where
       1m : {m : Mode} → m ≤ m
       _·m_ : {x y z : Mode} → x ≤ y → y ≤ z → x ≤ z
       ∇m : s ≤ c
       Δm : c ≤ s
    
    postulate 
      ·m-unit-l : ∀ {x y : Mode} {α : x ≤ y} → 1m ·m α == α
      ·m-unit-r : ∀ {x y : Mode} {α : x ≤ y} → α ·m 1m == α
      ·m-assoc  : ∀ {x y z w : Mode} {α : x ≤ y} {β : y ≤ z} {γ : z ≤ w} → (α ·m β) ·m γ == α ·m (β ·m γ)
      retract : ∇m ·m Δm == 1m{s}

    data Tp : Mode → Type where
      P : ∀ {m} → Tp m
      ⊤ : ∀ {m} → Tp m 
      F : ∀ {p q} (α : p ≤ q) → Tp q → Tp p
      U : ∀ {p q} (α : p ≤ q) → Tp p → Tp q 

    data _[_]⊢_ : {p q : Mode} → Tp q → p ≤ q → Tp p -> Type where
      ⊤R : ∀ {p r} {α : p ≤ r} {C : Tp r} → C [ α ]⊢ ⊤
      hypp : ∀ {p} → P [ 1m{p} ]⊢ P 
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
      mergeUF : ∀ {A : Tp c} → U Δm A [ 1m ]⊢ F ∇m A
      mergeFU : ∀ {A : Tp c} → F ∇m A [ 1m ]⊢ U Δm A

    -- could write out so that cut elim doesn't get stuck as often
    transport⊢ : {p q : Mode} → {A : Tp q} → {α β : p ≤ q} {B : Tp p} 
               → α == β
               → A [ α ]⊢ B 
               → A [ β ]⊢ B 
    transport⊢ id D = D

    -- seems to only work for 1m
    eta : ∀ {p} (A : Tp p) → A [ 1m ]⊢ A
    eta P = hypp
    eta ⊤ = ⊤R
    eta (F α A) = FL (FR 1m (! ·m-unit-l ∘ ·m-unit-r) (eta A)) 
    eta (U α A) = UR (UL 1m (! ·m-unit-r ∘ ·m-unit-l) (eta A))

    cut : ∀ {p q r} {α : p ≤ q} {β : q ≤ r} {A : Tp r} {B : Tp q} {C : Tp p}
        → A [ β ]⊢ B
        → B [ α ]⊢ C
        → A [ α ·m β ]⊢ C
    -- atom
    cut hypp hypp = transport⊢ (! ·m-unit-l) hypp
    -- principal 
    cut {α = α} {β = β} (FR γ c₁ D) (FL E) = transport⊢ (ap (λ x → α ·m x) c₁ ∘ ·m-assoc) (cut D E)
    cut {α = α} {β = β} (UR D) (UL γ₁ c₁ E) = transport⊢ (ap (λ x → x ·m β) c₁ ∘ ! ·m-assoc) (cut D E)
    -- right commutative
    cut _ ⊤R = ⊤R
    cut {α = α} {β = β} D (FR {α = α'} γ c₁ E) = FR (γ ·m β) (ap (λ x → x ·m β) c₁ ∘ ! ·m-assoc) (cut D E)
    cut {α = α} {β = β} D (UR E) = UR (transport⊢ ·m-assoc (cut D E))
    -- left commutative
    cut {α = α} {β = β} (FL D) E = FL (transport⊢ (! ·m-assoc) (cut D E))
    cut {α = α} {β = β} (UL {α = α'} γ c₁ D) E = UL (α ·m γ) (ap (λ x → α ·m x) c₁ ∘ ·m-assoc) (cut D E)
    -- merging
    cut (FR γ c₁ D) mergeFU = UR (transport⊢ {!BUSTED!} D) 
    cut {β = β} (UR D) mergeUF = FR (Δm ·m β) (ap (λ x → x ·m β) retract ∘ ! ·m-assoc) D 
    cut {α = α} mergeUF (FL D) = UL (α ·m ∇m) (ap (λ x → α ·m x) retract ∘ ·m-assoc) D
    cut mergeFU (UL γ c₁  D) = FL (transport⊢ {!BUSTED!} D) 
    cut mergeUF mergeFU = transport⊢ (! ·m-unit-l) (eta _)
    cut mergeFU mergeUF = transport⊢ (! ·m-unit-l) (eta _)

    hyp' : ∀ {p} {A : Tp p} {α : p ≤ p} → α == 1m → A [ α ]⊢ A
    hyp' id = eta _ 

    hyp : ∀ {p} {A : Tp p} → A [ 1m ]⊢ A
    hyp = eta _ 

    cut1 : ∀ {p q} {α : q ≤ p} {A : Tp p} {B : Tp q} {C : Tp q}
          → A [ α ]⊢ B → B [ 1m ]⊢ C → A [ α ]⊢ C
    cut1 D E = transport⊢ ·m-unit-l (cut D E)

    cut1' : ∀ {p q} {α : q ≤ p} {A : Tp p} {B : Tp p} {C : Tp q}
          → A [ 1m ]⊢ B → B [ α ]⊢ C → A [ α ]⊢ C
    cut1' D E = transport⊢ ·m-unit-r (cut D E)

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
    Ffunc11 = FL (hyp' ·m-unit-l)

    Ffunc12 : ∀ {p} {A : Tp p} → A [ 1m ]⊢ F 1m A
    Ffunc12 = FR 1m ·m-unit-l hyp
  
    Ffunc·1 : ∀ {x y z : Mode} {α : x ≤ y} {β : y ≤ z} {A : Tp _}
            → F α (F β A) [ 1m ]⊢ F (α ·m β) A
    Ffunc·1 {β = β} = FL (FL (FR 1m (ap (λ x → x ·m β) (! ·m-unit-l) ∘ ·m-unit-r) hyp))

    Ffunc·2 : ∀ {x y z : Mode} {α : x ≤ y} {β : y ≤ z} {A : Tp _}
            → F (α ·m β) A [ 1m ]⊢ F α (F β A)
    Ffunc·2 {α = α} {β = β} = FL (FR β (! ·m-unit-l) (FR 1m ·m-unit-r hyp))
    
    Ufunc11 : ∀ {p} {A : Tp p} → U 1m A [ 1m ]⊢ A
    Ufunc11 = UL 1m ·m-unit-l hyp

    Ufunc12 : ∀ {p} {A : Tp p} → A [ 1m ]⊢ U 1m A
    Ufunc12 = UR (hyp' ·m-unit-l)
  
    Ufunc·1 : ∀ {x y z : Mode} {α : x ≤ y} {β : y ≤ z} {A : Tp _}
            → U β (U α A) [ 1m ]⊢ U (α ·m β) A
    Ufunc·1 {α = α} {β = β} = UR (UL α (! ·m-unit-r) (UL 1m ·m-unit-l hyp))

    Ufunc·2 : ∀ {x y z : Mode} {α : x ≤ y} {β : y ≤ z} {A : Tp _}
            → U (α ·m β) A [ 1m ]⊢ U β (U α A)
    Ufunc·2 {α = α} {β = β} = UR (UR (UL 1m (ap (λ x → α ·m x) (! ·m-unit-r) ∘ ·m-unit-l) hyp)) 


    -- adjoints are actually adjoint
    UFadjunction1 : ∀ {p q} {A B} {α : p ≤ q} → F α A [ 1m ]⊢ B → A [ 1m ]⊢ U α B
    UFadjunction1 {α = α} start = UR (cut1 (FR 1m id hyp) start)

    UFadjunction2 : ∀ {p q} {A B} {α : p ≤ q} → A [ 1m ]⊢ U α B → F α A [ 1m ]⊢ B 
    UFadjunction2 {α = α} start = FL (cut1' start (UL 1m id hyp))


    -- monads

    □ : ∀ {p q} (α : p ≤ q) → Tp p → Tp p 
    □ α A = F α (U α A)

    ◯ : ∀ {p q} (α : p ≤ q) → Tp q → Tp q 
    ◯ α A = U α (F α A)

    unit : {p q : Mode} {A : Tp q} {α : p ≤ q} → A [ 1m ]⊢ ◯ α A
    unit {α = α} = UR (FR 1m id hyp)

    mult : {p q : Mode} {A : Tp q} {α : p ≤ q} → ◯ α (◯ α A) [ 1m ]⊢ ◯ α A
    mult {α = α} = UR (UL 1m (! ·m-unit-r ∘ ·m-unit-l) (FL (UL 1m id hyp))) 

    counit : {p q : Mode} {A : Tp p} {α : p ≤ q} → □ α A [ 1m ]⊢ A
    counit = FL (UL 1m id hyp)

    comult : {p q : Mode} {A : Tp p} {α : p ≤ q} → □ α A [ 1m ]⊢ □ α (□ α A)
    comult {α = α} = FL (FR 1m (! ·m-unit-l ∘ ·m-unit-r) (UR (FR 1m id hyp))) 

    -- need α "inverse"
    badcounit : {p q : Mode} {A : Tp q} {α : p ≤ q} → ◯ α A [ 1m ]⊢ A
    badcounit = UL {!!} {!NO!} (FL (hyp' {!NO!})) 

    -- need α "inverse" on the other side
    badunit : {p q : Mode} {A : Tp p} {α : p ≤ q} → A [ 1m ]⊢ □ α A
    badunit = FR {!!} {!NO!} (UR (hyp' {!NO!}))

    ♭ = □ Δm
    ♯ = ◯ ∇m

    badunit' : {A : Tp c}→ A [ 1m ]⊢ ♭ A
    badunit' = FR ∇m {!NO!} (UR (hyp' {!NO!}))

    badcounit' : {A : Tp c} → ♯ A [ 1m ]⊢ A
    badcounit' = UL Δm {!NO!} (FL (hyp' {!NO!}))

    adjunction1 : ∀ {A B} → ♭ A [ 1m ]⊢ B → A [ 1m ]⊢ ♯ B
    adjunction1 {A}{B} start = UFadjunction1 step2 where
      step1 : U Δm A [ 1m ]⊢ U Δm B
      step1 = UFadjunction1 start

      step2 : F ∇m A [ 1m ]⊢ F ∇m B
      step2 = cut1 (cut1 mergeFU step1) mergeUF

    adjunction2 : ∀ {A B} → A [ 1m ]⊢ ♯ B → ♭ A [ 1m ]⊢ B 
    adjunction2 {A}{B} start = UFadjunction2 (cut1 mergeUF (cut1 (UFadjunction2 start) mergeFU))
