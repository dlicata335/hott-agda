
-- difference from before: natural transformations go in the rules for F,
-- not in the operations on contexts

open import functorlogic.Lib
open import functorlogic.ModesProduct1

module functorlogic.NDHypOnly-NonStructural-Product6 where

  -- F is covariant in 1 and 2-cells in this version

  data Tp : Mode → Set where
    P    : ∀ {m} → Tp m
    Q    : ∀ {m} → Tp m
    F    : ∀ {p q} (α : p ≤ q) → Tp p → Tp q
    ·    : Tp ⊤m
    _,_  : ∀ {p q} → Tp p → Tp q → Tp (p ×m q)

  data Ctx : (p : Mode) → Set where
    ·    : Ctx ⊤m
    _,_  : ∀ {p q} → Ctx p → Ctx q → Ctx (p ×m q)
    ▸    : ∀ {p} → Tp p → Ctx p
    _[_] : ∀ {p q} → Ctx p → (α : p ≤ q) → Ctx q

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

  data Ctx' : (q : Mode) (p : Mode) → Set where
    hole : ∀ {p} → Ctx' p p
    ·    : ∀ {p} → Ctx' p ⊤m
    _,1_  : ∀ {p q r} → Ctx' r p → Ctx q → Ctx' r (p ×m q)
    _,2_  : ∀ {p q r} → Ctx p → Ctx' r q → Ctx' r (p ×m q)
    ▸    : ∀ {p q} → Tp p → Ctx' q p
    _[_] : ∀ {p q r} → Ctx' r p → (α : p ≤ ▸ q) → Ctx' r (▸ q)

  fill : ∀ { p q} → Ctx' q p → Ctx q → Ctx p
  fill hole Δ = Δ
  fill · Δ = ·
  fill (Γ' ,1 Γ'') Δ = fill Γ' Δ , Γ''
  fill (Γ' ,2 Γ'') Δ = Γ' , fill Γ'' Δ
  fill (▸ A) Δ = ▸ A
  fill (Γ' [ α ]) Δ = fill Γ' Δ [ α ]

  -- fillcong : ∀ {p q} (Γ' : Ctx' p q) {Δ Δ'} → Δ ⇒c Δ' → fill Γ' Δ ⇒c fill Γ' Δ'
  -- fillcong hole ρ = ρ
  -- fillcong · _ = idc
  -- fillcong (Γ' ,1 Γ) ρ = fillcong Γ' ρ ,c idc
  -- fillcong (Γ ,2 Γ') ρ = idc ,c fillcong Γ' ρ
  -- fillcong (▸ _) _ = idc
  -- fillcong (Γ' [ α ]) ρ = nt 1⇒ (fillcong Γ' ρ)

  data _⊢_ : {p : Mode} → Ctx p → Tp p -> Set where
    var : ∀ {p α} {Γ : Ctx p} {A : Tp p} → (ρ : Γ ≡c  (▸ A) [ α ]) → (e : α ⇒ 1m) → Γ ⊢ A
    FE  : ∀ {p q r} {Γ : Ctx p} {Δ : Ctx q} {α : r ≤ q} {A : Tp r} {C : Tp p}
        → (Γ' : Ctx' q p) 
        → (ρ : Γ ≡c fill Γ' Δ)
        → (D : Δ ⊢ F α A )
        → (E : fill Γ' ((▸ A) [ α ]) ⊢ C)
        → Γ ⊢ C
    FI : ∀ {p q r} → {Γ : Ctx p} {Δ : Ctx q} {A : Tp r} {α : r ≤ p} 
       → (β : q ≤ p)
       → (ρ : Γ ≡c Δ [ β ])
       → (γ : q ≤ r)
       → (e : β ⇒ (γ ·1 α)) -- covariant
       → (D : Δ [ γ ] ⊢ A)
       → Γ ⊢ F α A
    pair : ∀ {p q} {Γ : Ctx (p ×m q)} {A1 : Tp p} {A2 : Tp q}
        → (D1 : Γ [ fstm ] ⊢ A1)
        → (D2 : Γ [ sndm ] ⊢ A2)
        → Γ ⊢ (A1 , A2)
    letpair : ∀ {p q1 q2} {Γ : Ctx p} {Δ : Ctx (q1 ×m q2)} {A : Tp _} {B : Tp _} {C : Tp p}
       → (Γ' : Ctx' (q1 ×m q2) p) 
       → (s : Γ ≡c fill Γ' Δ)
       → (D : Δ ⊢ (A , B))
       → (E : (fill Γ' (▸ A , ▸ B)) ⊢ C)
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

  trc : ∀ {p} {C} {Γ Γ' : Ctx p} → Γ' ⊢ C → Γ ≡c Γ' → Γ ⊢ C
  trc (var x x₁) ρ = var (ρ ·c x) x₁
  trc (FE Γ' s D D₁) ρ = FE Γ' (ρ ·c s) D D₁
  trc (FI β x γ x₁ D) ρ = FI β (ρ ·c x) γ x₁ D
  trc (pair D D₁) ρ = pair (trc D ([]≡c ρ)) (trc D₁ ([]≡c ρ))
  trc (letpair Γ' s D D₁) ρ = letpair Γ' (ρ ·c s) D D₁

  data _⊢s_ : {p : _} (Γ : Ctx p) → Ctx p → Set where
    subst· : ∀ {Γ : Ctx ⊤m} → (ρ : Γ ≡c ·) → Γ ⊢s ·
    subst▸ : ∀ {p} {Γ : Ctx p} {A} → (D : Γ ⊢ A) → Γ ⊢s (▸ A)
    subst, : ∀ {p q} {Γ : Ctx (p ×m q)} {Δ1 Δ2} 
           → (θ1 : Γ [ fstm ] ⊢s Δ1)
           → (θ2 : Γ [ sndm ] ⊢s Δ2)
           → Γ ⊢s (Δ1 , Δ2)
    subst[] : {p q : Mode} {Γ : Ctx p} → {Γ1 Γ2 : Ctx q} {α : q ≤ p} → (ρ : Γ ≡c Γ1 [ α ]) → (θ : Γ1 ⊢s Γ2) → Γ ⊢s Γ2 [ α ]

  _·rs_ : ∀ {p} {Γ1 Γ2 Γ3 : Ctx p} → Γ1 ≡c Γ2 → Γ2 ⊢s Γ3 → Γ1 ⊢s Γ3
  ρ ·rs subst· ρ' = subst· (ρ ·c ρ')
  ρ ·rs subst▸ D = subst▸ (trc D ρ)
  ρ ·rs subst, θ θ₁ = subst, ([]≡c ρ ·rs θ) ([]≡c ρ ·rs θ₁)
  ρ ·rs subst[] ρ' θ = subst[] (ρ ·c ρ') θ

  mutual
    _·sr_ : ∀ {p} {Γ1 Γ2 Γ3 : Ctx p} → Γ1 ⊢s Γ2 → Γ2 ≡c Γ3 → Γ1 ⊢s Γ3
    subst[] ρ₁ (subst[] ρ θ) ·sr (α [·] β) = subst[] ((ρ₁ ·c []≡c ρ) ·c (α [·] β)) θ
    subst[] ρ θ ·sr [1] = (ρ ·c [1]) ·rs θ
    subst[] ρ (subst, θ θ₁) ·sr [fst] = ρ ·rs θ
    subst[] ρ (subst, θ θ₁) ·sr [snd] = ρ ·rs θ₁
    subst[] ρ θ ·sr [<>] = subst· (ρ ·c [<>])
    subst[] ρ θ ·sr [,] = subst, (([]≡c ρ ·c ((_ [·] _))) ·rs subst[] idc θ) (([]≡c ρ ·c (_ [·] _)) ·rs subst[] idc θ)
    θ ·sr idc = θ
    θ ·sr !c ρ = θ ·sr! ρ
    θ ·sr (ρ ·c ρ₁) = (θ ·sr ρ) ·sr ρ₁
    subst[] ρ θ ·sr []≡c ρ₁ = subst[] ρ (θ ·sr ρ₁)
    subst, θ θ₁ ·sr (ρ ,c ρ₁) = subst, (θ ·sr ρ) (θ₁ ·sr ρ₁)
  
    _·sr!_ : ∀ {p} {Γ1 Γ2 Γ3 : Ctx p} → Γ1 ⊢s Γ2 → Γ3 ≡c Γ2 → Γ1 ⊢s Γ3
    θ ·sr! (α [·] β) = {!!}
    θ ·sr! [1] = {!!}
    θ ·sr! [fst] = {!!}
    θ ·sr! [snd] = {!!}
    θ ·sr! [<>] = {!!}
    subst, θ θ₁ ·sr! [,] = {!!} -- FIXME: something is wrong here! not enough intros for contexts in product categories
    θ ·sr! idc = {!!}
    θ ·sr! !c ρ = {!!}
    θ ·sr! (ρ ·c ρ₁) = {!!}
    θ ·sr! []≡c ρ = {!!}
    θ ·sr! (ρ ,c ρ₁) = {!!}

  ids : {p : _} (Γ : Ctx p) → Γ ⊢s Γ
  ids · = subst· idc
  ids (▸ A) = subst▸ (var {α = 1m} (!c [1]) 1⇒)
  ids (Γ , Δ) = subst, ([fst] ·rs ids Γ) ([snd] ·rs ids Δ)
  ids (Γ [ α ]) = subst[] idc (ids Γ)

  subst : ∀ {p} {C} {Γ Γ' : Ctx p} → Γ' ⊢ C → Γ ⊢s Γ' → Γ ⊢ C
  subst (var ρ e) θ = {!!}
  subst (FE Γ' ρ D D₁) θ = {!!}
  subst (FI β ρ γ e D) θ = {!!}
  subst (pair D D₁) θ = {!!}
  subst (letpair Γ' s D D₁) θ = {!!}
{-
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
-}

  reduce : ∀ {p : Mode} {Γ : Ctx p} {A : Tp p} → Γ ⊢ A → Γ ⊢ A
  reduce (FE Γ' ρ1 (FI β ρ γ e D) E₁) = {!!}
  reduce (letpair Γ' ρ (pair D1 D2) D3) = {!!}
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
-}

{-
    foo : ∀ {q p } {α : p ≤ q} {A : Tp p} 
        → ▸ A [ α ] ⊢s (▸ A [ α ] ,, ▸ A [ α ])
    foo {α = α} {A} = nt contract idc ·rs ids (▸ A [ (α ,m α) ·1 ⊗m ])

    foo' : ∀ {q p } {α : p ≤ q} {A : Tp p} 
         → ▸ A ⊢ (A ⊗ A)
    foo' {A = A} = subst (FI idc (pair {Γ = ▸ A , ▸ A} (var idc) (var idc))) (foo {α = 1m}) 


    test = {!foo'!}
-}

  module Tensor (p : BaseMode) (⊗m : (▸ p ×m ▸ p) ≤ ▸ p) where
      -- FIXME: laws
  
    _,,_ : Ctx (▸ p) → Ctx (▸ p) → Ctx (▸ p)
    _,,_ Γ Δ = (Γ , Δ) [ ⊗m ]
  
    _⊗_ : Tp (▸ p) → Tp (▸ p) → Tp (▸ p)
    _⊗_ A B = F ⊗m (A , B)

    pair⊗ : {A B : Tp (▸ p)} {Γ Γ1 Γ2 : Ctx (▸ p)}
         → Γ ≡c (Γ1 ,, Γ2)
         → Γ1 ⊢ A
         → Γ2 ⊢ B
         → Γ ⊢ (A ⊗ B)
    pair⊗ {Γ = Γ} {Γ1} {Γ2} ρ D1 D2 = FI _ ρ 1m 1⇒ (pair (trc D1 ((1m [·] fstm) ·c [fst])) (trc D2 ((1m [·] sndm) ·c [snd])))

    let⊗ : {A B C : Tp (▸ p)} {Γ Γ1 Γ2 : Ctx (▸ p)}
            → Γ ≡c (Γ1 ,, Γ2)
            → Γ2 ⊢ (A ⊗ B)
            → (Γ1 ,, (▸ A ,, ▸ B)) ⊢ C
            → Γ ⊢ C
    let⊗{Γ1 = Γ1} ρ D1 D2 = FE ((Γ1 ,2 hole) [ ⊗m ]) ρ D1 (letpair ((Γ1 ,2 (hole [ ⊗m ])) [ ⊗m ]) idc (var {α = 1m} (!c [1]) 1⇒) D2)  

    contract : ∀ {q} {α : q ≤ ▸ p} {A : Tp q} → α ⇒ ((α ,m α) ·1 ⊗m) → (▸ A) [ α ] ⊢ (F α A ⊗ F α A)
    contract {α = α} {A} cα = FI α idc (α ,m α) cα (trc (pair (trc (FI α idc 1m 1⇒ (var idc 1⇒)) [fst]) (trc (FI α idc 1m 1⇒ (var idc 1⇒)) [snd])) [,])

  -- FIXME: how do you weaken/contract in context?
