
{-# OPTIONS --type-in-type #-}

open import lib.Prelude 

module metatheory.CohesiveTT4 where

  module TT (Mode : Type) 
            (_≤_ : Mode -> Mode -> Type)
            (1m : {m : Mode} → m ≤ m)
            (_·1_ : {x y z : Mode} → x ≤ y → y ≤ z → x ≤ z)
            (_⇒_ : ∀ {p q} → (α β : p ≤ q) → Type) 
            (_·⇒_ : {x y : Mode} {p q r : x ≤ y} → p ⇒ q → q ⇒ r → p ⇒ r)
            (·≤-unit-l : ∀ {x y : Mode} {α : x ≤ y} → (1m ·1 α) ⇒ α)
            (!·≤-unit-l : ∀ {x y : Mode} {α : x ≤ y} → α ⇒ (1m ·1 α))
            (·≤-unit-r : ∀ {x y : Mode} {α : x ≤ y} → (α ·1 1m) ⇒ α)
            (!·≤-unit-r : ∀ {x y : Mode} {α : x ≤ y} → α ⇒ (α ·1 1m))
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
      hypp : ∀ {p} {α : p ≤ p} → 1m ⇒ α → P [ α ]⊢ P 
      FL : ∀ {p q r} {α : p ≤ q} {β : r ≤ p} {A : Tp q} {C : Tp r}
         → A [ β ·1 α ]⊢ C
         → F α A [ β ]⊢ C
      FR : ∀ {p q r} {α : p ≤ q} {β : p ≤ r} {A : Tp q} {C : Tp r}
         → (γ : q ≤ r) → (α ·1 γ) ⇒ β
         → C [ γ ]⊢ A
         → C [ β ]⊢ F α A
      UL : ∀ {p q r} {α : q ≤ p} {β : r ≤ p} {A : Tp q} {C : Tp r}
         → (γ : r ≤ q) → (γ ·1 α) ⇒ β
         → A [ γ ]⊢ C
         → U α A [ β ]⊢ C
      UR : ∀ {p q r} {α : q ≤ p} {β : p ≤ r} {A : Tp q} {C : Tp r}
         → C [ α ·1 β ]⊢ A
         → C [ β ]⊢ U α A

    transport⊢ : {p q : Mode} → {A : Tp q} → {α β : p ≤ q} {B : Tp p} 
               → α ⇒ β
               → A [ α ]⊢ B 
               → A [ β ]⊢ B 
    transport⊢ e (hypp p) = hypp (p ·⇒ e)
    transport⊢ e (FL D) = FL (transport⊢ (whiskerr e) D)
    transport⊢ e (FR γ x D) = FR γ (x ·⇒ e) D
    transport⊢ e (UL γ x D) = UL γ (x ·⇒ e) D
    transport⊢ e (UR D) = UR (transport⊢ (whiskerl e) D)

    -- seems to only work for 1m
    eta : ∀ {p} (A : Tp p) → A [ 1m ]⊢ A
    eta P = hypp {!!}
    eta (F α A) = FL (FR 1m {!!} (eta A)) 
    eta (U α A) = UR (UL 1m {!!} (eta A))

    cut : ∀ {p q r} {α : p ≤ q} {β : q ≤ r} {A : Tp r} {B : Tp q} {C : Tp p}
        → A [ β ]⊢ B
        → B [ α ]⊢ C
        → A [ α ·1 β ]⊢ C
    -- atom
    cut (hypp p) (hypp q) = {!OK!}
    -- principal 
    cut {α = α} {β = β} (FR γ c₁ D) (FL {α = α1} E) = transport⊢ {!OK!} (cut D E)
    cut {α = α} {β = β} (UR {α = α1} D) (UL γ₁ c₁ E) = transport⊢ {! OK!} (cut D E)
    -- right commutative
    cut {α = α} {β = β} D (FR {α = α'} γ c₁ E) = FR (γ ·1 β) {!OK!} (cut D E)
    cut {α = α} {β = β} D (UR {α = α1} E) = UR (transport⊢ {!OK!} (cut D E))
    -- left commutative
    cut {α = α} {β = β} (FL {α = α1} D) E = FL (transport⊢ {!OK!} (cut D E))
    cut {α = α} {β = β} (UL {α = α'} γ c₁ D) E = UL (α ·1 γ) {!OK!} (cut D E)

    hyp : ∀ {p} {A : Tp p} → A [ 1m ]⊢ A
    hyp = eta _ 

    cut1 : ∀ {p q} {α : q ≤ p} {A : Tp p} {B : Tp q} {C : Tp q}
          → A [ α ]⊢ B → B [ 1m ]⊢ C → A [ α ]⊢ C
    cut1 D E = transport⊢ {!!} (cut D E)

    cut1' : ∀ {p q} {α : q ≤ p} {A : Tp p} {B : Tp p} {C : Tp q}
          → A [ 1m ]⊢ B → B [ α ]⊢ C → A [ α ]⊢ C
    cut1' D E = transport⊢ {!!} (cut D E)

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
    Ffunc11 = FL {!OK!}

    Ffunc12 : ∀ {p} {A : Tp p} → A [ 1m ]⊢ F 1m A
    Ffunc12 = FR 1m {!OK!} hyp
  
    Ffunc·1 : ∀ {x y z : Mode} {α : x ≤ y} {β : y ≤ z} {A : Tp _}
            → F α (F β A) [ 1m ]⊢ F (α ·1 β) A
    Ffunc·1 {β = β} = FL (FL (FR 1m {!OK!} hyp))

    Ffunc·2 : ∀ {x y z : Mode} {α : x ≤ y} {β : y ≤ z} {A : Tp _}
            → F (α ·1 β) A [ 1m ]⊢ F α (F β A)
    Ffunc·2 {α = α} {β = β} = FL (FR β {!OK!} (FR 1m {!OK!} hyp))
    
    Ufunc11 : ∀ {p} {A : Tp p} → U 1m A [ 1m ]⊢ A
    Ufunc11 = UL 1m {!OK!} hyp

    Ufunc12 : ∀ {p} {A : Tp p} → A [ 1m ]⊢ U 1m A
    Ufunc12 = UR {!OK!}
  
    Ufunc·1 : ∀ {x y z : Mode} {α : x ≤ y} {β : y ≤ z} {A : Tp _}
            → U β (U α A) [ 1m ]⊢ U (α ·1 β) A
    Ufunc·1 {α = α} {β = β} = UR (UL α {!OK!} (UL 1m {!OK!} hyp))

    Ufunc·2 : ∀ {x y z : Mode} {α : x ≤ y} {β : y ≤ z} {A : Tp _}
            → U (α ·1 β) A [ 1m ]⊢ U β (U α A)
    Ufunc·2 {α = α} {β = β} = UR (UR (UL 1m {!OK!} hyp)) 


    -- adjoints are actually adjoint
    UFadjunction1 : ∀ {p q} {A B} {α : p ≤ q} → F α A [ 1m ]⊢ B → A [ 1m ]⊢ U α B
    UFadjunction1 {α = α} start = UR (cut1 (FR 1m {!OK!} hyp) start)

    UFadjunction2 : ∀ {p q} {A B} {α : p ≤ q} → A [ 1m ]⊢ U α B → F α A [ 1m ]⊢ B 
    UFadjunction2 {α = α} start = FL (cut1' start (UL 1m {!OK!} hyp))

    -- monads

    □ : ∀ {p q} (α : p ≤ q) → Tp p → Tp p 
    □ α A = F α (U α A)

    ◯ : ∀ {p q} (α : p ≤ q) → Tp q → Tp q 
    ◯ α A = U α (F α A)

    unit : {p q : Mode} {A : Tp q} {α : p ≤ q} → A [ 1m ]⊢ ◯ α A
    unit {α = α} = UR (FR 1m {!OK!} hyp)

    mult : {p q : Mode} {A : Tp q} {α : p ≤ q} → ◯ α (◯ α A) [ 1m ]⊢ ◯ α A
    mult {α = α} = UR (UL 1m {!OK!} (FL (UL 1m {!OK!} hyp))) 

    counit : {p q : Mode} {A : Tp p} {α : p ≤ q} → □ α A [ 1m ]⊢ A
    counit = FL (UL 1m {!OK!} hyp)

    comult : {p q : Mode} {A : Tp p} {α : p ≤ q} → □ α A [ 1m ]⊢ □ α (□ α A)
    comult {α = α} = FL (FR 1m {!OK!} (UR (FR 1m {!OK!} hyp))) 

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
      Δ∇unit : 1m ⇒ (Δm ·1 ∇m)
      ∇Δcounit : (∇m ·1 Δm) ⇒ 1m 

    mergeUF : ∀ {A : Tp c} → U Δm A [ 1m ]⊢ F ∇m A
    mergeUF = UL ∇m ? (FR 1m {!OK!} hyp)

    mergeFU : ∀ {A : Tp c} → F ∇m A [ 1m ]⊢ U Δm A
    mergeFU = FL (UR (transport⊢ {!fact1!} hyp))

    ♭ = □ Δm
    ♯ = ◯ ∇m

    badunit' : {A : Tp c}→ A [ 1m ]⊢ ♭ A
    badunit' = FR ∇m {! NO!} (UR (transport⊢ ? hyp))

    badcounit' : {A : Tp c} → ♯ A [ 1m ]⊢ A
    badcounit' = UL Δm {! NO!} (FL (transport⊢ ? hyp))

    adjunction1 : ∀ {A B} → ♭ A [ 1m ]⊢ B → A [ 1m ]⊢ ♯ B
    adjunction1 {A}{B} start = UFadjunction1 step2 where
      step1 : U Δm A [ 1m ]⊢ U Δm B
      step1 = UFadjunction1 start

      step2 : F ∇m A [ 1m ]⊢ F ∇m B
      step2 = cut1 (cut1 mergeFU step1) mergeUF

    adjunction2 : ∀ {A B} → A [ 1m ]⊢ ♯ B → ♭ A [ 1m ]⊢ B 
    adjunction2 {A}{B} start = UFadjunction2 (cut1 mergeUF (cut1 (UFadjunction2 start) mergeFU))

