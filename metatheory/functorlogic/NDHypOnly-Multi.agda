
-- FIXME: does this make sense?

open import functorlogic.Lib
open import functorlogic.ModesMulti

module functorlogic.NDHypOnly-Multi where

  data Tp : Mode → Set where
    P    : ∀ {m} → Tp m
    Q    : ∀ {m} → Tp m
    F    : ∀ {ps q} (α : ps ≤ q) → All Tp ps → Tp q

  data Ctx : (p : Mode) → Set where
    ▸    : ∀ {p} → Tp p → Ctx p
    _[_] : ∀ {ps q} → All Ctx ps → (α : ps ≤ q) → Ctx q

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

  data _⊢s_ : ∀ {p} → Ctx p → Ctx p → Set where
    subst▸ : ∀  {p} {Γ : Ctx p} {A} → Γ ⊢ A → Γ ⊢s (▸ A)
    substnt : ∀ {p qs} {Γ} {Γs Δs : All Ctx qs} {α β : qs ≤ p} (e : α ⇒ β) 
       → Γ ⇒c Γs [ α ]
       → AllAll2 _⊢s_ Γs Δs
       → Γ ⊢s Δs [ β ]

  1⇒a : ∀ {ps qs} {βs : All (_≤_ ps) qs} → AllAll2 _⇒_ βs βs
  1⇒a {βs = βs} = allAll2refl _⇒_ (λ _ → 1⇒) βs

  idca : ∀ {ps} {Γs : All Ctx ps} → AllAll2 _⇒c_ Γs Γs
  idca {Γs = Γs} = allAll2refl _⇒c_ (λ _ → idc) Γs

  {-# NO_TERMINATION_CHECK #-}
  -- mapped recursive call
  ids : ∀ {p} (Γ : Ctx p) → Γ ⊢s Γ
  ids (▸ A) = subst▸ (var idc)
  ids (Γs [ α ]) = substnt 1⇒ idc (allAll2refl _⊢s_ (λ Γ → ids Γ) Γs)

  rename : ∀ {p} {C} {Γ Γ' : Ctx p} → Γ' ⊢ C → Γ ⇒c Γ' → Γ ⊢ C
  rename (var ρ1) ρ = var (ρ ·c ρ1)
  rename (FE Γ' ρ1 D D₁) ρ = FE Γ' (ρ ·c ρ1) D D₁
  rename (FI ρ1 D) ρ = FI (ρ ·c ρ1) D

  _·rs_ : ∀ {p} {Γ1 Γ2 Γ3 : Ctx p} → Γ1 ⇒c Γ2 → Γ2 ⊢s Γ3 → Γ1 ⊢s Γ3
  ρ ·rs subst▸ D = subst▸ (rename D ρ)
  ρ ·rs substnt e ρ' θ = substnt e (ρ ·c ρ') θ

  {-# NO_TERMINATION_CHECK #-}
  -- mapped recursive call
  _·sr_ : ∀ {p} {Γ1 Γ2 Γ3 : Ctx p} → Γ1 ⊢s Γ2 → Γ2 ⇒c Γ3 → Γ1 ⊢s Γ3
  θ ·sr idc = θ
  θ ·sr (ρ ·c ρ₁) = (θ ·sr ρ) ·sr ρ₁
  (substnt e ρ1 θs) ·sr nt e' ρs = substnt (e ·2 e') ρ1 (allAll2Trans _ _ _ _·sr_ θs ρs) 
  θ ·sr ![i0m] = substnt 1⇒ ![i0m] (θ , allAll2refl _⊢s_ ids _)
  substnt e ρ (θ , θs) ·sr [i0m] = (ρ ·c (nt e idca ·c [i0m])) ·rs θ
  substnt {ps}{q :: qs}{Γ}{Γs}{Δs}{α}{.(iSm _)} e ρ (θ , θs) ·sr ([iSm] {α = β}) =
    substnt 1⇒ (ρ ·c (nt e idca ·c [iSm])) θs 
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

  {-# NO_TERMINATION_CHECK #-}
  -- mapped recursive call
  subst : ∀ {p} {C} {Γ Γ' : Ctx p} → Γ' ⊢ C → Γ ⊢s Γ' → Γ ⊢ C
  subst (var ρ) θ with θ ·sr ρ 
  subst (var ρ) θ | subst▸ D = D
  subst (FE Γ' ρ D D₁) θ with θ ·sr ρ 
  ... | θ' = {!!}
  subst (FI ρ D) θ with θ ·sr ρ 
  subst (FI ρ D) θ | substnt e ρ' θ' = FI (ρ' ·c nt e idca) (allAll2Trans _⊢s_ _⊢_ _⊢_ (λ θ₁ D₁ → subst D₁ θ₁) θ' D)

{-
  data _≡c_ : ∀ {p} → Ctx p → Ctx p → Set where
    _[·]_ : ∀ {p q r} {Γ : Ctx r} (α : r ≤ q) (β : q ≤ p)
          → (Γ [ α ]) [ β ] ≡c Γ [ α ·1 β ]
    [1] : ∀ {p} {Γ : Ctx p} → Γ [ 1m ] ≡c Γ
    [fst] : ∀ {p q} {Γ : Ctx p} {Δ : Ctx q} → (Γ , Δ) [ fstm ] ≡c Γ
    [snd] : ∀ {p q} {Γ : Ctx p} {Δ : Ctx q} → (Γ , Δ) [ sndm ] ≡c Δ
    [<>] : ∀ {p} {Γ : Ctx p} → Γ [ <>m ] ≡c ·
    [,] : ∀ {p q r} {α : p ≤ q} {β : p ≤ r}{Γ : Ctx p} → Γ [ (α ,m β) ] ≡c (Γ [ α ] , Γ [ β ]) 
    idc  : ∀ {p} {Γ : Ctx p} → Γ ≡c Γ
    !c   : ∀ {p} {Γ Δ : Ctx p} → Γ ≡c Δ → Δ ≡c Γ
    _·c_ : ∀ {p} {Γ1 Γ2 Γ3 : Ctx p} → Γ1 ≡c Γ2 → Γ2 ≡c Γ3 → Γ1 ≡c Γ3
    []≡c : ∀ {p q} {Γ Δ : Ctx q} {α : q ≤ p} 
       → Γ ≡c Δ
       → Γ [ α ] ≡c Δ [ α ]
    _,c_ : ∀ {p q} {Γ1 Δ1 : Ctx p} {Γ2 Δ2 : Ctx q} 
           → Γ1 ≡c Δ1
           → Γ2 ≡c Δ2 
           → (Γ1 , Γ2) ≡c (Δ1 , Δ2)

  ×cη : ∀ {q r} {Γ : Ctx (q ×m r)} → Γ ≡c (Γ [ fstm ] , Γ [ sndm ]) 
  ×cη = {!!}


  fill : ∀ { p q} → Ctx' q p → Ctx q → Ctx p
  fill hole Δ = Δ
  fill · Δ = ·
  fill (Γ' ,1 Γ'') Δ = fill Γ' Δ , Γ''
  fill (Γ' ,2 Γ'') Δ = Γ' , fill Γ'' Δ
  fill (▸ A) Δ = ▸ A
  fill (Γ' [ α ]) Δ = fill Γ' Δ [ α ]

  data _⇒c_ : ∀ {p} → Ctx p → Ctx p → Set where
    idc  : ∀ {p} {Γ : Ctx p} → Γ ⇒c Γ
    _·c_ : ∀ {p} {Γ1 Γ2 Γ3 : Ctx p} → Γ1 ⇒c Γ2 → Γ2 ⇒c Γ3 → Γ1 ⇒c Γ3
    nt : ∀ {p q} {Γ Δ : Ctx q} {α β : q ≤ p} (e : α ⇒ β) 
       → Γ ⇒c Δ
       → Γ [ α ] ⇒c Δ [ β ]
    _,c_ : ∀ {p q} {Γ1 Δ1 : Ctx p} {Γ2 Δ2 : Ctx q} 
           → Γ1 ⇒c Δ1
           → Γ2 ⇒c Δ2 
           → (Γ1 , Γ2) ⇒c (Δ1 , Δ2)
    eq  : ∀ {p} {Γ Δ : Ctx p} → Γ ≡c Δ → Γ ⇒c Δ

  fillcong : ∀ {p q} (Γ' : Ctx' p q) {Δ Δ'} → Δ ⇒c Δ' → fill Γ' Δ ⇒c fill Γ' Δ'
  fillcong hole ρ = ρ
  fillcong · _ = idc
  fillcong (Γ' ,1 Γ) ρ = fillcong Γ' ρ ,c idc
  fillcong (Γ ,2 Γ') ρ = idc ,c fillcong Γ' ρ
  fillcong (▸ _) _ = idc
  fillcong (Γ' [ α ]) ρ = nt 1⇒ (fillcong Γ' ρ)

  data _⊢_ : {p : Mode} → Ctx p → Tp p -> Set where
    var : ∀ {p} {Γ : Ctx p} {A : Tp p} → Γ ⇒c (▸ A) → Γ ⊢ A
    FE  : ∀ {p q r} {Γ : Ctx p} {Δ : Ctx q} {α : r ≤ q} {A : Tp r} {C : Tp p}
       → (Γ' : Ctx' q p) 
       → (s : Γ ⇒c fill Γ' Δ)
       → Δ ⊢ F α A 
       → (fill Γ' ((▸ A) [ α ])) ⊢ C
       → Γ ⊢ C
    FI : ∀ {p q} → {Γ : Ctx p} {Γ' : Ctx q} {A : Tp q} {α : q ≤ p}
       → Γ ⇒c Γ' [ α ] 
       → Γ' ⊢ A
       → Γ ⊢ F α A
    pair : ∀ {p q} {Γ : Ctx (p ×m q)} {A1 : Tp p} {A2 : Tp q}
        → Γ [ fstm ] ⊢ A1
        → Γ [ sndm ] ⊢ A2 
        → Γ ⊢ (A1 , A2)
    letpair : ∀ {p q1 q2} {Γ : Ctx p} {Δ : Ctx (q1 ×m q2)} {A : Tp _} {B : Tp _} {C : Tp p}
       → (Γ' : Ctx' (q1 ×m q2) p) 
       → (s : Γ ⇒c fill Γ' Δ)
       → Δ ⊢ (A , B) 
       → (fill Γ' (▸ A , ▸ B)) ⊢ C
       → Γ ⊢ C
    -- Inl : ∀ {p} → {Γ : Ctx p} {A B : Tp p} 
    --    → Γ ⊢ A
    --    → Γ ⊢ (A ⊕ B)
    -- Inr : ∀ {p} → {Γ : Ctx p} {A B : Tp p} 
    --    → Γ ⊢ B
    --    → Γ ⊢ (A ⊕ B)
    -- Case : ∀ {p} {Γ Γ1 Γ2 : Ctx p} {A B : Tp p} {C : Tp p}
    --      → (s : Γ ⇉ Γ2 , Γ1)
    --      → Γ1 ⊢ (A ⊕ B)
    --      → (Γ2 , ▸ A) ⊢ C 
    --      → (Γ2 , ▸ B) ⊢ C 
    --      → Γ ⊢ C 
    -- Lam : ∀ {p} {Γ : Ctx p} {A B : Tp p}
    --     → (Γ , ▸ A) ⊢ B
    --     → Γ ⊢ (A ⊸ B)


  rename : ∀ {p} {C} {Γ Γ' : Ctx p} → Γ' ⊢ C → Γ ⇒c Γ' → Γ ⊢ C
  rename (var ρ1) ρ = var (ρ ·c ρ1)
  rename (FE Γ' ρ1 D D₁) ρ = FE Γ' (ρ ·c ρ1) D D₁
  rename (FI ρ1 D) ρ = FI (ρ ·c ρ1) D
  rename (pair D1 D2) ρ = pair (rename D1 (nt 1⇒ ρ)) (rename D2 (nt 1⇒ ρ))
  rename (letpair Γ' ρ1 D1 D2) ρ = letpair Γ' (ρ ·c ρ1) D1 D2
{-
  rename (Inl D) ρ = Inl (rename D ρ)
  rename (Inr D) ρ = Inr (rename D ρ)
  rename (Case ρ1 D D₁ D₂) ρ = Case (ρ ·⇉ ρ1) D D₁ D₂
  rename (Lam D) ρ = Lam (rename D (ρ ,⇉ id⇉))
-}

  data _⊢s_ : {p : _} (Γ : Ctx p) → Ctx p → Set where
    subst· : ∀ {Γ : Ctx ⊤m} → Γ ⇒c · → Γ ⊢s ·
    subst▸ : ∀  {p} {Γ : Ctx p} {A} → Γ ⊢ A → Γ ⊢s (▸ A)
    subst, : ∀ {p q} {Γ : Ctx (p ×m q)} {Δ1 Δ2} 
           → Γ [ fstm ] ⊢s Δ1
           → Γ [ sndm ] ⊢s Δ2
           → Γ ⊢s (Δ1 , Δ2)
    subst[] : {p q : Mode} {Γ : Ctx p} → {Γ1 Γ2 : Ctx q} {α : q ≤ p} → Γ ⇒c Γ1 [ α ] → Γ1 ⊢s Γ2 → Γ ⊢s Γ2 [ α ]
    substnt : ∀ {p} {Γ Δ1 Δ2 : Ctx p}
            → Γ ⊢s Δ1 → Δ1 ⇒c Δ2 
            → Γ ⊢s Δ2

  invert▸ : ∀  {p} {Γ Δ : Ctx p} {A} → Γ ⊢s Δ → Δ ⇒c (▸ A) → Γ ⊢ A
  invert▸ (subst· ρ1) ρ = {!!}
  invert▸ (subst▸ D) idc = D
  invert▸ (subst▸ D) (ρ ·c ρ₁) = {!!}
  invert▸ (subst▸ D) (eq x) = {!!}
  invert▸ (subst, θ θ₁) ρ = {!!}
  invert▸ (subst[] ρ1 θ) ρ = {!!}
  invert▸ (substnt θ x) ρ = invert▸ θ (x ·c ρ)

  _·rs_ : ∀ {p} {Γ1 Γ2 Γ3 : Ctx p} → Γ1 ⇒c Γ2 → Γ2 ⊢s Γ3 → Γ1 ⊢s Γ3
  ρ ·rs subst· ρ' = subst· (ρ ·c ρ')
  ρ ·rs subst▸ D = subst▸ (rename D ρ)
  ρ ·rs subst, θ θ₁ = subst, (nt 1⇒ ρ ·rs θ) (nt 1⇒ ρ ·rs θ₁)
  ρ ·rs subst[] ρ' θ = subst[] (ρ ·c ρ') θ
  ρ ·rs substnt θ d = substnt (ρ ·rs θ) d

  ids : {p : _} (Γ : Ctx p) → Γ ⊢s Γ
  ids · = subst· idc
  ids (▸ A) = subst▸ (var idc)
  ids (Γ , Δ) = subst, (eq [fst] ·rs ids Γ) (eq [snd] ·rs ids Δ)
  ids (Γ [ α ]) = subst[] idc (ids Γ)

  subst : ∀ {p} {C} {Γ Γ' : Ctx p} → Γ' ⊢ C → Γ ⊢s Γ' → Γ ⊢ C
  subst (var ρ) θ = {!substnt θ ρ!}
--  subst (var ρ) θ | θ' = ?
  subst {Γ = Γ} {Γ'} (FE Γ'' ρ D E) θ = {!!}
  subst (FI ρ D) θ = {!substnt θ ρ!} -- FI ρ' (subst D θ') 
  subst (pair D1 D2) θ = pair (subst D1 (subst[] idc θ)) (subst D2 (subst[] idc θ))
  subst (letpair Γ' ρ D1 D2) θ = {!!}
{-
  -- subst (Inl D) θ = Inl (subst D θ)
  -- subst (Inr D) θ = Inr (subst D θ)
  -- subst (Case ρ D D₁ D₂) θ with θ ·sr ρ
  -- subst (Case s D D₁ D₂) θ | (subst, sΔ θ1 θ2) = Case sΔ (subst D θ2) (subst D₁ (subst, id⇉ θ1 (subst▸ (var id⇉)))) (subst D₂ (subst, id⇉ θ1 (subst▸ (var id⇉))))
  -- subst (Lam D) θ = Lam (subst D (subst, id⇉ θ (subst▸ (var id⇉))))
-}

  subst1 : ∀ {p q} {Γ' : Ctx' p q} {Δ} {A} {C}
        → fill Γ' (▸ A) ⊢ C
        → Δ ⊢ A
        → fill Γ' Δ ⊢ C
  subst1 (var x) E = {!!}
  subst1 (FE Γ'' s D D₁) E = {!!}
  subst1 (FI x D) E = {!!}
  subst1 (pair D D₁) E = {!!}
  subst1 (letpair Γ'' s D D₁) E = {!!}

  -- β steps type check
  reduce : ∀ {p : Mode} {Γ : Ctx p} {A : Tp p} → Γ ⊢ A → Γ ⊢ A
  reduce (FE Γ' ρ1 (FI ρ E) E₁) = {!!} 
  reduce (letpair Γ' ρ (pair D1 D2) D3) = rename (rename {!!} (fillcong Γ' (eq ×cη))) ρ
  reduce D = D

{-
  -- examples
  
  F∘1 : ∀ {p q r : Mode} {A : Tp r} {α : r ≥ q} {β : q ≥ p}
      → · ⊢ ((F β (F α A)) ⊸ F (α ∘1 β) A)
  F∘1 = Lam (FE (id⇉ ,⇉ [1]) (var id⇉) (FE id⇉ (var id⇉) (FI ·unitl (var id⇉)))) 

  F∘2 : ∀ {p q r : Mode} {A : Tp r} {α : r ≥ q} {β : q ≥ p}
      → · ⊢ (F (α ∘1 β) A ⊸ (F β (F α A)) )
  F∘2 {A = A}{α = α}{β} = Lam (FE {Γ1 = ·} {Γ2 = ▸ (F (α ∘1 β) A)} {β = 1m} (id⇉ ,⇉ [1]) (var id⇉) (FI (·unitl ·⇉ unfuse α β) (FI id⇉ (var id⇉))))

  Fnt : ∀ {p q : Mode} {A : Tp q} {α β : q ≥ p} (e : β ⇒ α)
      → · ⊢ (F α A ⊸ F β A)
  Fnt e = Lam (FE (id⇉ ,⇉ [1]) (var id⇉) (FI (·unitl ·⇉ nt e id⇉) (var id⇉)))
-}

{-
  module Tensor where
    -- all categories are strict monoidal
    postulate 
      ⊗m : ∀ {p} → (p ×m p) ≤ p
      -- FIXME: laws
  
    _,,_ : ∀ {p} → Ctx p → Ctx p → Ctx p
    _,,_ Γ Δ = (Γ , Δ) [ ⊗m ]
  
    _⊗_ : ∀ {p} → Tp p → Tp p → Tp p
    _⊗_ A B = F ⊗m (A , B)
    pair⊗ : ∀ {p} {A B : Tp p} {Γ Γ1 Γ2 : Ctx p}
         → Γ ⇒c (Γ1 ,, Γ2)
         → Γ1 ⊢ A
         → Γ2 ⊢ B
         → Γ ⊢ (A ⊗ B)
    pair⊗ {Γ = Γ} {Γ1} {Γ2} ρ D1 D2 = FI ρ (pair {Γ = (Γ1 , Γ2)} D1 D2)
-}
  
{-  
    let⊗ : ∀ {p} {A B C : Tp p} {Γ Γ1 Γ2 : Ctx p}
            → Γ ⇉ (Γ1 ,, Γ2)
            → Γ2 ⊢ (A ⊗ B)
            → (Γ1 ,, (▸ A ,, ▸ B)) ⊢ C
            → Γ ⊢ C
    let⊗{Γ1 = Γ1}  ρ D1 D2 = 
      FE ((Γ1 ,2 hole) [ ⊗m ]) ρ D1 (letpair ((Γ1 ,2 (hole [ ⊗m ])) [ ⊗m ]) id⇉ (var id⇉) D2)
-}

{-
    postulate
      contract : ∀ {q p} {α : p ≤ q} → α ⇒ ((α ,m α) ·1 ⊗m)

    foo : ∀ {q p } {α : p ≤ q} {A : Tp p} 
        → ▸ A [ α ] ⊢s (▸ A [ α ] ,, ▸ A [ α ])
    foo {α = α} {A} = nt contract idc ·rs ids (▸ A [ (α ,m α) ·1 ⊗m ])

    foo' : ∀ {q p } {α : p ≤ q} {A : Tp p} 
         → ▸ A ⊢ (A ⊗ A)
    foo' {A = A} = subst (FI idc (pair {Γ = ▸ A , ▸ A} (var idc) (var idc))) (foo {α = 1m}) 


    test = {!foo'!}
-}
-}
