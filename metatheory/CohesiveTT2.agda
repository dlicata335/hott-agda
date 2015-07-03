
{-# OPTIONS --type-in-type #-}

open import lib.Prelude

module metatheory.CohesiveTT2 where

module TT (Mode : Type) 
          (_≤_ : Mode -> Mode -> Type)
          (1m : {m : Mode} → m ≤ m)
          (_·m_ : {x y z : Mode} → x ≤ y → y ≤ z → x ≤ z)
          (·m-unit-l : ∀ {x y : Mode} {α : x ≤ y} → 1m ·m α == α)
          (·m-unit-r : ∀ {x y : Mode} {α : x ≤ y} → α ·m 1m == α)
          (·m-assoc  : ∀ {x y z w : Mode} {α : x ≤ y} {β : y ≤ z} {γ : z ≤ w} → (α ·m β) ·m γ == α ·m (β ·m γ))
          where

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
    cut {α = α} {β = β} (FR γ c D) (FL E) = transport⊢ (ap (λ x → α ·m x) c ∘ ·m-assoc) (cut D E)
    cut {α = α} {β = β} (UR D) (UL γ₁ c₁ E) = transport⊢ (ap (λ x → x ·m β) c₁ ∘ ! ·m-assoc) (cut D E)
    -- right commutative
    cut _ ⊤R = ⊤R
    cut {α = α} {β = β} D (FR {α = α'} γ c E) = FR (γ ·m β) (ap (λ x → x ·m β) c ∘ ! ·m-assoc) (cut D E)
    cut {α = α} {β = β} D (UR E) = UR (transport⊢ ·m-assoc (cut D E))
    -- left commutative
    cut {α = α} {β = β} (FL D) E = FL (transport⊢ (! ·m-assoc) (cut D E))
    cut {α = α} {β = β} (UL {α = α'} γ c D) E = UL (α ·m γ) (ap (λ x → α ·m x) c ∘ ·m-assoc) (cut D E)

    hyp' : ∀ {p} {A : Tp p} {α : p ≤ p} → α == 1m → A [ α ]⊢ A
    hyp' id = eta _ 

    hyp : ∀ {p} {A : Tp p} → A [ 1m ]⊢ A
    hyp = eta _ 

    module Examples where

      -- unit and counit are definable
      unit : {p q : Mode} {A : Tp q} {α : p ≤ q} → A [ 1m ]⊢ U α (F α A)
      unit = UR (FR 1m id hyp)

      counit : {p q : Mode} {A : Tp p} {α : p ≤ q} → F α (U α A) [ 1m ]⊢ A
      counit = FL (UL 1m id hyp)

      -- "unit" of comonad and "counit" of monad are not
      -- need α inverse     
      badcounit : {p q : Mode} {A : Tp q} {α : p ≤ q} → U α (F α A) [ 1m ]⊢ A
      badcounit = UL {!!} {!!} (FL (hyp' {!!}))

      -- need α inverse on the other side
      badunit : {p q : Mode} {A : Tp p} {α : p ≤ q} → A [ 1m ]⊢ F α (U α A)
      badunit = FR {!!} {!!} (UR (hyp' {!!}))


      -- F α and F β are different for two parallel but different α and β
      diff1 : {p q : Mode} {α β : p ≤ q} {A : Tp q} → F α A [ 1m ]⊢ F β A
      diff1 = FL (FR 1m {!!} hyp)

      diff2 : {p q : Mode} {α β : p ≤ q} {A : Tp p} → U α A [ 1m ]⊢ U β A
      diff2 = UR (UL 1m {!!} hyp)

    
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


      -- I was hoping that we could make a triple adjunction by putting in 
      -- one of α . β = id or β · α = id, but it seems like we would need both...

      -- need β ·m α == 1m
      want1 : {p q : Mode} {α : p ≤ q} {β : q ≤ p} {A : Tp q} → F α A [ 1m ]⊢ U β A
      want1 = FL (UR {!!})

      -- need α ·m β == 1m
      want2 : {p q : Mode} {α : p ≤ q} {β : q ≤ p} {A : Tp q} → U β A [ 1m ]⊢ F α A
      want2 {α = α} {β = β} = UL α {!!} (FR 1m ·m-unit-r hyp)
