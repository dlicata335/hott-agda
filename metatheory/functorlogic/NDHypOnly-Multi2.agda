
open import functorlogic.Lib
open import functorlogic.ModesMultiSyn

module functorlogic.NDHypOnly-Multi2 where

  data ATp : Set where
    P Q : ATp

  data Tp : Mode → Set where
    At   : ∀ {p} → ATp → Tp p
    F    : ∀ {p q} (α : p ≤ q) → All Tp p → Tp q

  subst1m : ∀ {ps qs p} → qs ≤ p → (i : p ∈ ps) → replace qs i ≤s ps
  subst1m {p :: ps} {qs} t i0 = (t ∘m (r-to-s (all-from-in _ addright)) , mapAll (λ e → ren≤ (all-from-in _ (addleft qs)) e) (1ms ps)) 
  subst1m t (iS x₁) = (v i0 , subst1m t x₁ ∘s pm _)

  mutual
    data _[_]⊢_ : {p : Mode} {ps : List Mode} → (Γ : All Tp ps) (α : ps ≤ p) → Tp p -> Set where
        var : ∀ {p ps} {PP} {Γ : All Tp ps} {α : ps ≤ p}
                (x : p ∈ ps)
                (lx : lookup Γ x == (At PP))
                (e : α ⇒ v x)
                → Γ [ α ]⊢ (At PP)
        FL : ∀ {p r ps qs} {Γ : All Tp ps} {Δ : All Tp qs} {α : qs ≤ p} {β : ps ≤ r} {C : Tp r}
                (x : p ∈ ps)
                (lx : lookup Γ x == F α Δ)
                (D : all-replace Γ Δ x [ β ∘m (subst1m α x) ]⊢ C)
                → Γ [ β ]⊢ C
        FR : ∀ {ps qs r} → {Γ : All Tp ps} {β : ps ≤ r} {Δ : All Tp qs} {α : qs ≤ r}
             (γ : ps ≤s qs)
             (e : β ⇒ (α ∘m γ))
             (D : Γ [ γ ]⊢s Δ)
             → Γ [ β ]⊢ F α Δ

    _[_]⊢s_ : {ps qs : List Mode} → (Γ : All Tp ps) (α : ps ≤s qs) (Δ : All Tp qs) -> Set 
    _[_]⊢s_ {qs = []} Γ α Δ = Unit
    _[_]⊢s_ {qs = q :: qs} Γ α (A , Δ) = Γ [ fst α ]⊢ A × Γ [ snd α ]⊢s Δ

    ident : ∀ {p} (A : Tp p) → (A , <>) [ v i0 ]⊢ A
    ident (At PP) = var i0 id 1⇒ 
    ident (F α A) = FL i0 id (FR (r-to-s (all-from-in _ addright)) 1⇒ {!ident A!}) -- need some retyping

    transport⊢ : ∀ {ps p} {Γ : All Tp ps} {A} {α β : ps ≤ p} (e : β ⇒ α) 
               → Γ [ α ]⊢ A
               → Γ [ β ]⊢ A
    transport⊢ e (var x eq e') = var x eq (e ·2 e') 
    transport⊢ e (FL x eq D) = FL x eq (transport⊢ {!!} D) -- need congruence for ∘m
    transport⊢ e (FR γ e₁ D) = FR γ (e ·2 e₁) D

    cut : ∀ {p ps qs r} {Γ Δ A B} {α : qs ≤ p} {β : ps ≤ r} 
        → Δ [ α ]⊢ A
        → (x : p ∈ ps) → lookup Γ x == A
        → Γ [ β ]⊢ B
        → all-replace Γ Δ x [ β ∘m subst1m α x ]⊢ B
    cut (var x lx e) x₁ eq E  = {!!}
    cut D x₁ eq (var x₂ lx₁ e) = {!!}
    cut (FL x lx D) x₁ eq E = {!!}
    cut D x₁ eq (FR γ e D₁) = {!!}
    cut (FR γ e D) x eq (FL x₁ lx E) = {!!}

  -- FIXME sort out the notation for what gets flipped and what doesn't

  module Test {p : Mode} (⊗ : (p :: (p :: [])) ≤ p) where

    identity : ((F ⊗ (At P , At Q , <>)) , <>) [ v i0 ]⊢ F ⊗ (At P , At Q , <>)
    identity = FL i0 id (FR (1ms _) 1⇒ (var i0 id 1⇒ , var (iS i0) id 1⇒ , <>))

    swap : (swapt : (⊗ ∘m (v i0 , v (iS i0) , <>)) ⇒ (⊗ ∘m (v (iS i0) , v i0 , <>)))
           → ((F ⊗ (At P , At Q , <>)) , <>) [ v i0 ]⊢ F ⊗ (At Q , At P , <>)
    swap swapt = FL i0 id (FR ((v (iS i0)) , ((v i0) , <>)) swapt ((var (iS i0) id 1⇒) , (var i0 id 1⇒ , <>)) )
    
    contr : (contrt : v i0 ⇒ (⊗ ∘m (v i0 , v i0 , <>))) → (At{p} P , <>) [ v i0 ]⊢ F ⊗ (At P , At P , <>)
    contr contrt = FR (v i0 , v i0 , <>) contrt (var i0 id 1⇒ , var i0 id 1⇒ , <>)

    free : (nullary : [] ≤ p) → <> [ nullary ]⊢ At P
    free α = var {!!} {!!} {!!}

    free2 : (nullary : [] ≤ p) (α : (p :: []) ≤ p) → ((nullary ∘m <>) ⇒ α)
            → <> [ nullary ]⊢ F α (At P , <>)
    free2 nullary α e = FR ({!!} , <>) {!!} {!!}

    
  
