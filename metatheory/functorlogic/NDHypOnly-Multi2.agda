
open import functorlogic.Lib
open import functorlogic.ModesMulti

module functorlogic.NDHypOnly-Multi2 where

  data Tp : Mode → Set where
    P    : ∀ {m} → Tp m
    Q    : ∀ {m} → Tp m
    F    : ∀ {p q} (α : p ≤ q) → All Tp p → Tp q

  data Ctx : (p : Mode) → Set where
    ▸    : ∀ {p} → Tp p → Ctx p
    _[_] : ∀ {p ps} → All Ctx ps → (α : ps ≤ p) → Ctx p

  mutual
    data Ctx' : (q : Mode) (p : Mode) → Set where
      hole  : ∀ {p} → Ctx' p p
      const : ∀ {q p} → Ctx p → Ctx' q p
      _[_] : ∀ {q r ps} → Ctx's q ps → (α : ps ≤ r) → Ctx' q r
    
    Ctx's : (q : Mode) (ps : List Mode)  → Set
    Ctx's q [] = Unit
    Ctx's q (p :: ps) = Either (Ctx' q p × All Ctx ps) (Ctx p × Ctx's q ps)

  mutual
    fill : ∀ {p q} → Ctx' q p → Ctx q → Ctx p
    fill hole Δ = Δ
    fill (const Γ) Δ = Γ
    fill (_[_] Γ's α) Δ = fills Γ's Δ [ α ]

    fills : ∀ {q ps} → Ctx's q ps → Ctx q → All Ctx ps
    fills {ps = []} Γ's Δ = <>
    fills {ps = p :: ps} (Inl (Γ' , Γs)) Δ = fill Γ' Δ , Γs
    fills {ps = p :: ps} (Inr (Γ , Γ's)) Δ = Γ , fills Γ's Δ

  data _⇒c_ : ∀ {p} → Ctx p → Ctx p → Set where
    idc  : ∀ {p} {Γ : Ctx p} → Γ ⇒c Γ
    _·c_ : ∀ {p} {Γ1 Γ2 Γ3 : Ctx p} → Γ1 ⇒c Γ2 → Γ2 ⇒c Γ3 → Γ1 ⇒c Γ3
    nt : ∀ {p qs} {Γs Δs : All Ctx qs} {α β : qs ≤ p} (e : α ⇒ β) 
       → AllAll2 _⇒c_ Γs Δs
       → Γs [ α ] ⇒c Δs [ β ]
    unfuse  : ∀ {p ps qs} {α : ps ≤ p} {βs : All (_≤_ qs) ps} {Γs : All Ctx qs}
          → Γs [ βs ·1 α ] ⇒c ((mapAll (λ β → Γs [ β ]) βs) [ α ])
    fuse  : ∀ {p ps qs} {α : ps ≤ p} {βs : All (_≤_ qs) ps} {Γs : All Ctx qs}
            → ((mapAll (λ β → Γs [ β ]) βs) [ α ]) ⇒c Γs [ βs ·1 α ]
    [i0m] : ∀ {p ps} {Γ : Ctx p} {Γs : All Ctx ps} → ( (Γ , Γs) [ i0m ] ) ⇒c Γ
    ![i0m] : ∀ {p ps} {Γ : Ctx p} {Γs : All Ctx ps} → Γ ⇒c ( (Γ , Γs) [ i0m ] )
    [iSm] : ∀ {p q ps} {Γ : Ctx p} {Γs : All Ctx ps} {α : ps ≤ q} → ( (Γ , Γs) [ iSm α ] ) ⇒c (Γs [ α ])
    ![iSm] : ∀ {p q ps} {Γ : Ctx p} {Γs : All Ctx ps} {α : ps ≤ q} → (Γs [ α ]) ⇒c ( (Γ , Γs) [ iSm α ] )

  mutual
    data _⊢_ : {p : Mode} → Ctx p → Tp p -> Set where
      var : ∀ {p} {Γ : Ctx p} {A : Tp p} → Γ ⇒c (▸ A) → Γ ⊢ A
      FE  : ∀ {p q r} {Γ : Ctx p} {Δ : Ctx q} {α : r ≤ q} {As : All Tp r} {C : Tp p}
         → (Γ' : Ctx' q p) 
         → (s : Γ ⇒c fill Γ' Δ)
         → Δ ⊢ F α As
         → (fill Γ' (mapAll ▸ As [ α ])) ⊢ C
         → Γ ⊢ C
      FI : ∀ {p qs} → {Γ : Ctx p} {Γs : All Ctx qs} {As : All Tp qs} {α : qs ≤ p}
         → Γ ⇒c Γs [ α ] 
         → AllAll2 _⊢_ Γs As
         → Γ ⊢ F α As
  rename : ∀ {p} {C} {Γ Γ' : Ctx p} → Γ' ⊢ C → Γ ⇒c Γ' → Γ ⊢ C
  rename (var ρ1) ρ = var (ρ ·c ρ1)
  rename (FE Γ' ρ1 D D₁) ρ = FE Γ' (ρ ·c ρ1) D D₁
  rename (FI ρ1 D) ρ = FI (ρ ·c ρ1) D

  data _⊢s_ : ∀ {p} → Ctx p → Ctx p → Set where
    subst▸ : ∀  {p} {Γ : Ctx p} {A} → Γ ⊢ A → Γ ⊢s (▸ A)
    -- builds in some fusion
    substnt : ∀ {p qs rs} {Γ : Ctx p} {Γs : All Ctx rs} {Δs : All Ctx qs} 
                {β : qs ≤ p} {α : rs ≤ p} {αs : All (_≤_ qs) rs} (e : (αs ·1 α) ⇒ β) 
              → Γ ⇒c (Γs [ α ]) 
              → AllAll2 _⊢s_ Γs (mapAll (λ αi → Δs [ αi ]) αs) 
              → Γ ⊢s Δs [ β ]

  1⇒a : ∀ {ps qs} {βs : All (_≤_ ps) qs} → AllAll2 _⇒_ βs βs
  1⇒a {βs = βs} = allAll2refl _⇒_ (λ _ → 1⇒) βs

  idca : ∀ {ps} {Γs : All Ctx ps} → AllAll2 _⇒c_ Γs Γs
  idca {Γs = Γs} = allAll2refl _⇒c_ (λ _ → idc) Γs

  _·rs_ : ∀ {p} {Γ1 Γ2 Γ3 : Ctx p} → Γ1 ⇒c Γ2 → Γ2 ⊢s Γ3 → Γ1 ⊢s Γ3
  ρ ·rs subst▸ D = subst▸ (rename D ρ)
  ρ ·rs substnt e ρ' θ = substnt e (ρ ·c ρ') θ

  {-# NO_TERMINATION_CHECK #-}
  -- mapped recursive call
  ids : ∀ {p} (Γ : Ctx p) → Γ ⊢s Γ
  ids (▸ A) = subst▸ (var idc)
  ids (_[_] {p = p}{ps = ps} Γs α) = substnt {α = α}{αs = 1ms ps} 1⇒ idc {!!} 

  {-# NO_TERMINATION_CHECK #-}
  -- mapped recursive call
  _·sr_ : ∀ {p} {Γ1 Γ2 Γ3 : Ctx p} → Γ1 ⊢s Γ2 → Γ2 ⇒c Γ3 → Γ1 ⊢s Γ3
  θ ·sr idc = θ
  θ ·sr (ρ ·c ρ₁) = (θ ·sr ρ) ·sr ρ₁
  θ ·sr nt e ρs = {!!}
  θ ·sr unfuse = {!!}
  θ ·sr fuse = {!!}
  substnt e ρ θs ·sr [i0m] = {!!}
  θ ·sr ![i0m] = {!!}
  θ ·sr [iSm] = {!!}
  θ ·sr ![iSm] = {!!}
{-
  θ ·sr idc = θ
  θ ·sr (ρ ·c ρ₁) = (θ ·sr ρ) ·sr ρ₁
  (substnt e ρ1 θs) ·sr nt e' ρs = ? -- substnt (e ·2 e') ρ1 (allAll2Trans _ _ _ _·sr_ θs ρs) 
  θ ·sr ![i0m] = ? -- substnt 1⇒ ![i0m] (θ , allAll2refl _⊢s_ ids _)
  substnt e ρ θ ·sr [i0m] = ? -- (ρ ·c (nt e idca ·c [i0m])) ·rs θ
  substnt {ps}{q :: qs}{Γ}{Γs}{Δs}{α}{.(iSm _)} e ρ (θ , θs) ·sr ([iSm] {α = β}) = ?
          -- substnt 1⇒ (ρ ·c (nt e idca ·c [iSm])) θs 
  substnt e ρ θ ·sr (![iSm] {α = β}) = substnt (iScong e) (ρ ·c ![iSm]) (ids _ , θ)
  substnt e ρ θ ·sr unfuse {βs = βs} = 
    substnt 1⇒ (ρ ·c (nt e idca ·c unfuse)) (makeAllAll2 _ _ _⊢s_ (λ α → substnt 1⇒ idc θ) βs)
  substnt e ρs (substnt e1 ρs1 θ1 , substnt e2 ρs2 θ2 , <>) ·sr fuse {ps = p1 :: (p2 :: [])} {βs = β1 , β2 , <>} =
    {!!}
    -- substnt (1⇒a ·1cong e)
    --         (ρs ·c (nt 1⇒ (ρs1 ·c nt e1 idca , {!!} , <>) ·c fuse)) 
    --         {!!}
    -- problems
    -- substnt (1⇒a ·1cong e) (ρs ·c (nt 1⇒ ((ρs1 ·c nt e1 idca) , {!(ρs2 ·c nt e2 idca)!} , <>) ·c unfuse)) 
    --         {!!}
  substnt e ρ θ ·sr fuse = {!!}
-}

{-
  {-# NO_TERMINATION_CHECK #-}
  -- mapped recursive call
  subst : ∀ {p} {C} {Γ Γ' : Ctx p} → Γ' ⊢ C → Γ ⊢s Γ' → Γ ⊢ C
  subst (var ρ) θ with θ ·sr ρ 
  subst (var ρ) θ | subst▸ D = D
  subst (FE Γ' ρ D D₁) θ with θ ·sr ρ 
  ... | θ' = {!!}
  subst (FI ρ D) θ with θ ·sr ρ 
  subst (FI ρ D) θ | substnt e ρ' θ' = FI (ρ' ·c nt e idca) (allAll2Trans _⊢s_ _⊢_ _⊢_ (λ θ₁ D₁ → subst D₁ θ₁) θ' D)
-}
