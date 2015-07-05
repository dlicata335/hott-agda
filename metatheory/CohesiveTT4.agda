
{-# OPTIONS --type-in-type #-}

open import lib.Prelude 

module metatheory.CohesiveTT4 where

  module TT (Mode : Type) 
            (_≤_ : Mode -> Mode -> Type)
            (1m : {m : Mode} → m ≤ m)
            (_·1_ : {x y z : Mode} → x ≤ y → y ≤ z → x ≤ z)
            (_⇒_ : ∀ {p q} → (α β : p ≤ q) → Type) 
            (1⇒ : ∀ {p q} → {α : p ≤ q} → α ⇒ α)
            (_·2_ : {x y : Mode} {p q r : x ≤ y} → p ⇒ q → q ⇒ r → p ⇒ r)
            (_·1cong_ : {x y z : Mode} {p p' : x ≤ y} {q q' : y ≤ z} → p ⇒ p' → q ⇒ q' → (p ·1 q) ⇒ (p' ·1 q'))
            (·1-unit-l : ∀ {x y : Mode} {α : x ≤ y} → (1m ·1 α) ⇒ α)
            (!·1-unit-l : ∀ {x y : Mode} {α : x ≤ y} → α ⇒ (1m ·1 α))
            (·1-unit-r : ∀ {x y : Mode} {α : x ≤ y} → (α ·1 1m) ⇒ α)
            (!·1-unit-r : ∀ {x y : Mode} {α : x ≤ y} → α ⇒ (α ·1 1m))
            (·1-assoc  : ∀ {x y z w : Mode} {α : x ≤ y} {β : y ≤ z} {γ : z ≤ w} → ((α ·1 β) ·1 γ) ⇒ (α ·1 (β ·1 γ)))
            (!·1-assoc  : ∀ {x y z w : Mode} {α : x ≤ y} {β : y ≤ z} {γ : z ≤ w} →  (α ·1 (β ·1 γ)) ⇒ ((α ·1 β) ·1 γ))
            (whiskerr : ∀ {p q r} → {α β : p ≤ q} → {γ : q ≤ r} → α ⇒ β → (α ·1 γ) ⇒ (β ·1 γ) )
            (whiskerl : ∀ {p q r} → {α β : p ≤ q} → {γ : r ≤ p} → α ⇒ β → (γ ·1 α) ⇒ (γ ·1 β) )
            where

    data Tp : Mode → Type where
      P : ∀ {m} → Tp m
      F : ∀ {p q} (α : p ≤ q) → Tp q → Tp p
      U : ∀ {p q} (α : p ≤ q) → Tp p → Tp q 

    data _[_]⊢_ : {p q : Mode} → Tp q → p ≤ q → Tp p -> Type where
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

    transport⊢ : {p q : Mode} → {A : Tp q} → {α β : p ≤ q} {B : Tp p} 
               → β ⇒ α
               → A [ α ]⊢ B 
               → A [ β ]⊢ B 
    transport⊢ e (hypp e') = hypp (e ·2 e')
    transport⊢ e (FL D) = FL (transport⊢ (whiskerr e) D)
    transport⊢ e (FR γ e' D) = FR γ (e ·2 e') D
    transport⊢ e (UL γ e' D) = UL γ (e ·2 e') D
    transport⊢ e (UR D) = UR (transport⊢ (whiskerl e) D)

    -- seems to only work for 1m
    eta : ∀ {p} (A : Tp p) → A [ 1m ]⊢ A
    eta P = hypp 1⇒
    eta (F α A) = FL (FR 1m (·1-unit-l ·2 !·1-unit-r) (eta A)) 
    eta (U α A) = UR (UL 1m (·1-unit-r ·2 !·1-unit-l) (eta A))

    cut : ∀ {p q r} {α : p ≤ q} {β : q ≤ r} {A : Tp r} {B : Tp q} {C : Tp p}
        → A [ β ]⊢ B
        → B [ α ]⊢ C
        → A [ α ·1 β ]⊢ C
    -- atom
    cut (hypp p) (hypp q) = hypp ((q ·1cong p) ·2 ·1-unit-l)
    -- principal 
    cut {α = α} {β = β} (FR γ e D) (FL {α = α1} E) = transport⊢ ((1⇒ ·1cong e) ·2 !·1-assoc) (cut D E)
    cut {α = α} {β = β} (UR {α = α1} D) (UL γ₁ e E) = transport⊢ ((e ·1cong 1⇒) ·2 ·1-assoc) (cut D E)
    -- right commutative
    cut {α = α} {β = β} D (FR {α = α'} γ e E) = FR (γ ·1 β) ((e ·1cong 1⇒) ·2 ·1-assoc) (cut D E)
    cut {α = α} {β = β} D (UR {α = α1} E) = UR (transport⊢ !·1-assoc (cut D E))
    -- left commutative
    cut {α = α} {β = β} (FL {α = α1} D) E = FL (transport⊢ ·1-assoc (cut D E))
    cut {α = α} {β = β} (UL {α = α'} γ e D) E = UL (α ·1 γ) ((1⇒ ·1cong e) ·2 !·1-assoc) (cut D E)

    hyp : ∀ {p} {A : Tp p} → A [ 1m ]⊢ A
    hyp = eta _ 

    hyp' : ∀ {p} {A : Tp p} {α : p ≤ p} → α ⇒ 1m → A [ α ]⊢ A
    hyp' e = transport⊢ e hyp

    cut1 : ∀ {p q} {α : q ≤ p} {A : Tp p} {B : Tp q} {C : Tp q}
          → A [ α ]⊢ B → B [ 1m ]⊢ C → A [ α ]⊢ C
    cut1 D E = transport⊢ !·1-unit-l (cut D E)

    cut1' : ∀ {p q} {α : q ≤ p} {A : Tp p} {B : Tp p} {C : Tp q}
          → A [ 1m ]⊢ B → B [ α ]⊢ C → A [ α ]⊢ C
    cut1' D E = transport⊢ !·1-unit-r (cut D E)

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

    postulate
      c : Mode
      s : Mode
      ∇m : s ≤ c
      Δm : c ≤ s
      ∇Δunit : 1m ⇒ (∇m ·1 Δm)
      Δ∇counit : (Δm ·1 ∇m) ⇒ 1m 

    mergeUF : ∀ {A : Tp c} → U Δm A [ 1m ]⊢ F ∇m A
    mergeUF = UL ∇m ∇Δunit (FR 1m !·1-unit-r hyp)

    mergeFU : ∀ {A : Tp c} → F ∇m A [ 1m ]⊢ U Δm A
    mergeFU = FL (UR (transport⊢ ((1⇒ ·1cong ·1-unit-l) ·2 Δ∇counit) hyp))

    ♭ = □ Δm
    ♯ = ◯ ∇m

    badunit' : {A : Tp c}→ A [ 1m ]⊢ ♭ A
    badunit' = FR ∇m {! NO!} (UR (transport⊢ {!!} hyp))

    badcounit' : {A : Tp c} → ♯ A [ 1m ]⊢ A
    badcounit' = UL Δm {! NO!} (FL (transport⊢ {!!} hyp))

    adjunction1 : ∀ {A B} → ♭ A [ 1m ]⊢ B → A [ 1m ]⊢ ♯ B
    adjunction1 {A}{B} start = UFadjunction1 step2 where
      step1 : U Δm A [ 1m ]⊢ U Δm B
      step1 = UFadjunction1 start

      step2 : F ∇m A [ 1m ]⊢ F ∇m B
      step2 = cut1 (cut1 mergeFU step1) mergeUF

    adjunction2 : ∀ {A B} → A [ 1m ]⊢ ♯ B → ♭ A [ 1m ]⊢ B 
    adjunction2 {A}{B} start = UFadjunction2 (cut1 mergeUF (cut1 (UFadjunction2 start) mergeFU))

