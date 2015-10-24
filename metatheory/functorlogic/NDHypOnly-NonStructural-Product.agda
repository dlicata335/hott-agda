

open import functorlogic.Lib
open import functorlogic.ModesProduct

module functorlogic.NDHypOnly-NonStructural-Product where

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

  data Ctx' : (q : Mode) (p : Mode) → Set where
    hole : ∀ {p} → Ctx' p p
    ·    : ∀ {p} → Ctx' p ⊤m
    _,1_  : ∀ {p q r} → Ctx' r p → Ctx q → Ctx' r (p ×m q)
    _,2_  : ∀ {p q r} → Ctx p → Ctx' r q → Ctx' r (p ×m q)
    ▸    : ∀ {p q} → Tp p → Ctx' q p
    _[_] : ∀ {p q r} → Ctx' r p → (α : p ≤ q) → Ctx' r q

  fill : ∀ { p q} → Ctx' q p → Ctx q → Ctx p
  fill hole Δ = Δ
  fill · Δ = ·
  fill (Γ' ,1 Γ'') Δ = fill Γ' Δ , Γ''
  fill (Γ' ,2 Γ'') Δ = Γ' , fill Γ'' Δ
  fill (▸ A) Δ = ▸ A
  fill (Γ' [ α ]) Δ = fill Γ' Δ [ α ]

  infix 12 _⇉_

  data _⇉_ : ∀ {p} → Ctx p → Ctx p → Set where
    id⇉  : ∀ {p} {Γ : Ctx p} → Γ ⇉ Γ
    _·⇉_ : ∀ {p} {Γ1 Γ2 Γ3 : Ctx p} → Γ1 ⇉ Γ2 → Γ2 ⇉ Γ3 → Γ1 ⇉ Γ3
    -- pseudofunctor laws
    fuse : ∀ {p q r} {Γ : Ctx r} (α : r ≤ q) (β : q ≤ p)
         → (Γ [ α ]) [ β ] ⇉ Γ [ α ·1 β ]
    unfuse : ∀ {p q r} {Γ : Ctx r} (α : r ≤ q) (β : q ≤ p)
           → Γ [ α ·1 β ] ⇉ (Γ [ α ]) [ β ]
    [1] : ∀ {p} {Γ : Ctx p} → Γ ⇉ Γ [ 1m ]
    ![1] : ∀ {p} {Γ : Ctx p} → Γ [ 1m ] ⇉ Γ 
    nt : ∀ {p q} {Γ Δ : Ctx q} {α β : q ≤ p} (e : α ⇒ β) → Γ ⇉ Δ → Γ [ α ] ⇉ Δ [ β ]
    -- definition of morphism in product category
    _,⇉_ : ∀ {p q} {Γ1 Δ1 : Ctx p} {Γ2 Δ2 : Ctx q} 
           → Γ1 ⇉ Δ1
           → Γ2 ⇉ Δ2 
           → (Γ1 , Γ2) ⇉ (Δ1 , Δ2)
{-
    -- action of functors on product categories
    [,] : ∀ {p q r} {α : p ≤ q} {β : p ≤ r} {Γ : Ctx p} → Γ [ α ,m β ] ⇉ (Γ [ α ] , Γ [ β ])
    -- FIXME: sound?
    ![,] : ∀ {p q r} {α : p ≤ q} {β : p ≤ r} {Γ : Ctx p} → (Γ [ α ] , Γ [ β ]) ⇉ Γ [ α ,m β ]
    [<>m] : ∀ {p} {Γ : Ctx p} → Γ [ <>m ] ⇉ ·
    ![<>m] : ∀ {p} {Γ : Ctx p} → · ⇉ Γ [ <>m ]
    [fst] : ∀ {p q} {Γ : Ctx p} {Δ : Ctx q} → (Γ , Δ) [ fstm ] ⇉ Γ
    ![fst] : ∀ {p q} {Γ : Ctx p} {Δ : Ctx q} → Γ ⇉ (Γ , Δ) [ fstm ] 
    [snd] : ∀ {p q} {Γ : Ctx p} {Δ : Ctx q} → (Γ , Δ) [ sndm ] ⇉ Δ
    ![snd] : ∀ {p q} {Γ : Ctx p} {Δ : Ctx q} → Δ ⇉ (Γ , Δ) [ sndm ] 
    -- punctuation 
    ▸, : ∀ {p q} {A : Tp p} {B : Tp q} → (▸ A , ▸ B) ⇉ ▸ (A , B)
    !▸, : ∀ {p q} {A : Tp p} {B : Tp q} → ▸ (A , B) ⇉ (▸ A , ▸ B)
-}

  data _⊢_ : {p : Mode} → Ctx p → Tp p -> Set where
    var : ∀ {p} {Γ : Ctx p} {A : Tp p} → Γ ⇉ (▸ A) → Γ ⊢ A
    FE  : ∀ {p q r} {Γ : Ctx p} {Δ : Ctx q} {α : r ≤ q} {A : Tp r} {C : Tp p}
       → (Γ' : Ctx' q p) 
       → (s : Γ ⇉ fill Γ' Δ)
       → Δ ⊢ F α A 
       → (fill Γ' ((▸ A) [ α ])) ⊢ C
       → Γ ⊢ C
    FI : ∀ {p q} → {Γ : Ctx p} {Γ' : Ctx q} {A : Tp q} {α : q ≤ p}
       → Γ ⇉ Γ' [ α ] 
       → Γ' ⊢ A
       → Γ ⊢ F α A
    pair : ∀ {p q} {Γ : Ctx (p ×m q)} {Γ1 : Ctx p} {A1 : Tp p} {Γ2 : Ctx q} {A2 : Tp q}
        → Γ ⇉ (Γ1 , Γ2)
        → Γ1 ⊢ A1
        → Γ2 ⊢ A2 
        → Γ ⊢ (A1 , A2)
    letpair : ∀ {p q1 q2} {Γ : Ctx p} {Δ : Ctx (q1 ×m q2)} {A : Tp _} {B : Tp _} {C : Tp p}
       → (Γ' : Ctx' (q1 ×m q2) p) 
       → (s : Γ ⇉ fill Γ' Δ)
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

  rename : ∀ {p} {C} {Γ Γ' : Ctx p} → Γ' ⊢ C → Γ ⇉ Γ' → Γ ⊢ C
  rename (var ρ1) ρ = var (ρ ·⇉ ρ1)
  rename (FE Γ' ρ1 D D₁) ρ = FE Γ' (ρ ·⇉ ρ1) D D₁
  rename (FI ρ1 D) ρ = FI (ρ ·⇉ ρ1) D
  rename (pair ρ1 D1 D2) ρ = pair (ρ ·⇉ ρ1) D1 D2
  rename (letpair Γ' ρ1 D1 D2) ρ = {!!}
{-
  rename (Inl D) ρ = Inl (rename D ρ)
  rename (Inr D) ρ = Inr (rename D ρ)
  rename (Case ρ1 D D₁ D₂) ρ = Case (ρ ·⇉ ρ1) D D₁ D₂
  rename (Lam D) ρ = Lam (rename D (ρ ,⇉ id⇉))
-}

  data _⊢s_ : {p : _} (Γ : Ctx p) → Ctx p → Set where
    subst· : ∀ {Γ : Ctx ⊤m} → Γ ⇉ · → Γ ⊢s ·
    subst▸ : ∀  {p} {Γ : Ctx p} {A} → Γ ⊢ A → Γ ⊢s (▸ A)
    subst, : ∀ {p q} {Γ : Ctx (p ×m q)} {Γ1 Γ2 Δ1 Δ2} →
              Γ ⇉ Γ1 , Γ2
           → Γ1 ⊢s Δ1
           → Γ2 ⊢s Δ2  
           → Γ ⊢s (Δ1 , Δ2)
    subst[] : {p q : Mode} {Γ : Ctx p} → {Γ1 Γ2 : Ctx q} {α : q ≤ p} → Γ ⇉ Γ1 [ α ] → Γ1 ⊢s Γ2 → Γ ⊢s Γ2 [ α ]

  _·rs_ : ∀ {p} {Γ1 Γ2 Γ3 : Ctx p} → Γ1 ⇉ Γ2 → Γ2 ⊢s Γ3 → Γ1 ⊢s Γ3
  ρ ·rs subst· ρ' = subst· (ρ ·⇉ ρ')
  ρ ·rs subst▸ D = subst▸ (rename D ρ)
  ρ ·rs subst, ρ' θ θ₁ = subst, (ρ ·⇉ ρ') θ θ₁
  ρ ·rs subst[] ρ' θ = subst[] (ρ ·⇉ ρ') θ

  ids : {p : _} (Γ : Ctx p) → Γ ⊢s Γ
  ids · = subst· id⇉
  ids (▸ A) = subst▸ (var id⇉)
  ids (Γ , Δ) = subst, id⇉ (ids Γ) (ids Δ)
  ids (Γ [ α ]) = subst[] id⇉ (ids Γ)

  _·sr_ : ∀ {p} {Γ1 Γ2 Γ3 : Ctx p} → Γ1 ⊢s Γ2 → Γ2 ⇉ Γ3 → Γ1 ⊢s Γ3
  θ ·sr id⇉ = θ
  θ ·sr (ρ ·⇉ ρ₁) = (θ ·sr ρ) ·sr ρ₁
  (subst[] ρ1 (subst[] ρ2 θ)) ·sr (fuse α β) = subst[] (ρ1 ·⇉ (nt 1⇒ ρ2 ·⇉ fuse α β)) θ
  subst[] ρ1 θ ·sr unfuse α β = subst[] (ρ1 ·⇉ unfuse α β) (subst[] id⇉ θ)
  θ ·sr [1] = subst[] [1] θ
  subst[] ρ θ ·sr ![1] = (ρ ·⇉ ![1]) ·rs θ
  subst[] ρ1 θ ·sr nt e ρ = subst[] (ρ1 ·⇉ nt e id⇉) (θ ·sr ρ)
  subst, ρ θ1 θ2 ·sr (ρ1 ,⇉ ρ2) = subst, ρ (θ1 ·sr ρ1) (θ2 ·sr ρ2)
{-
  subst[] ρ θ ·sr [,] = subst, (ρ ·⇉ [,]) (subst[] id⇉ θ) (subst[] id⇉ θ)
  subst, ρ (subst[] ρ1 θ1) (subst[] ρ2 θ2) ·sr ![,] = {!!} -- subst[] (ρ ·⇉ ({!!} ·⇉ ![,])) {!!} 
--     subst[] (ρ ·⇉ ((ρ1 ,⇉ ρ2) ·⇉ ({!!} ·⇉ ![,]))) {!!}
  subst[] ρ θ ·sr [<>m] = subst· (ρ ·⇉ [<>m])
  subst· ρ ·sr ![<>m] = subst[] (ρ ·⇉ ![<>m]) (ids _) 
  subst[] ρ (subst, ρ1 θ θ₁) ·sr [fst] = (ρ ·⇉ (nt 1⇒ ρ1 ·⇉ [fst])) ·rs θ
  θ ·sr ![fst] = subst[] ![fst] (subst, id⇉ θ (ids _))
  subst[] ρ (subst, ρ1 θ θ₁) ·sr [snd] = (ρ ·⇉ (nt 1⇒ ρ1 ·⇉ [snd])) ·rs θ₁
  θ ·sr ![snd] = subst[] ![snd] (subst, id⇉ (ids _) θ)
  subst, ρ (subst▸ M1) (subst▸ M2) ·sr ▸, = subst▸ (pair ρ M1 M2) 
  -- doesn't make sense?
  subst▸ θ ·sr !▸, = {!x ·⇉ !▸,!}
-}

{-
  subst : ∀ {p} {C} {Γ Γ' : Ctx p} → Γ' ⊢ C → Γ ⊢s Γ' → Γ ⊢ C
  subst (var ρ) θ with θ ·sr ρ
  ... | subst▸ D = D
  subst {Γ = Γ} {Γ'} (FE {α = α} ρ D E) θ with θ ·sr ρ 
  ... | subst, sΔ θ1 (subst[] sΔ2 θ2') = 
    FE (sΔ ·⇉ (id⇉ ,⇉ sΔ2)) (subst D θ2') (subst E (subst, id⇉ θ1 (subst[] id⇉ (subst▸ (var id⇉)))))
  subst (FI ρ D) θ with θ ·sr ρ
  ... | (subst[] sΔ θ') = FI sΔ (subst D θ')
  subst (Inl D) θ = Inl (subst D θ)
  subst (Inr D) θ = Inr (subst D θ)
  subst (Case ρ D D₁ D₂) θ with θ ·sr ρ
  subst (Case s D D₁ D₂) θ | (subst, sΔ θ1 θ2) = Case sΔ (subst D θ2) (subst D₁ (subst, id⇉ θ1 (subst▸ (var id⇉)))) (subst D₂ (subst, id⇉ θ1 (subst▸ (var id⇉))))
  subst (Lam D) θ = Lam (subst D (subst, id⇉ θ (subst▸ (var id⇉))))

  -- β steps type check
  reduce : ∀ {p : Mode} {Γ : Ctx p} {A : Tp p} → Γ ⊢ A → Γ ⊢ A
  reduce (FE s (FI ρ E) E₁) = subst E₁ (subst, s (ids _) (subst[] (nt 1⇒ ρ ·⇉ fuse _ _) (subst▸ E))) 
  reduce (Case s (Inl E) E₁ E₂) = subst E₁ (subst, s (ids _) (subst▸ E))
  reduce (Case s (Inr E) E₁ E₂) = subst E₂ (subst, s (ids _) (subst▸ E))
  reduce D = D

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
         → Γ ⇉ (Γ1 ,, Γ2)
         → Γ1 ⊢ A
         → Γ2 ⊢ B
         → Γ ⊢ (A ⊗ B)
    pair⊗ ρ D1 D2 = FI ρ (pair id⇉ D1 D2)
  
    let⊗ : ∀ {p} {A B C : Tp p} {Γ Γ1 Γ2 : Ctx p}
            → Γ ⇉ (Γ1 ,, Γ2)
            → Γ2 ⊢ (A ⊗ B)
            → (Γ1 ,, (▸ A ,, ▸ B)) ⊢ C
            → Γ ⊢ C
    let⊗{Γ1 = Γ1}  ρ D1 D2 = 
      FE ((Γ1 ,2 hole) [ ⊗m ]) ρ D1 (letpair ((Γ1 ,2 (hole [ ⊗m ])) [ ⊗m ]) id⇉ (var id⇉) D2)

    postulate
      contract : ∀ {q p} {α : p ≤ q} → α ⇒ ((α ,m α) ·1 ⊗m)

    foo : ∀ {q p } {α : p ≤ q} {A : Tp p} 
        → ▸ A [ α ] ⊢s ((▸ A [ α ,m α ]) [ ⊗m ])
    foo = {!!}

    foo' : ∀ {q p } {α : p ≤ q} {A : Tp p} 
        → ▸ A [ α ] ⊢s ((▸ A [ α ] , ▸ A [ α ]) [ ⊗m ])
    foo' {α = α} {A = A} = {!▸ A [ α ] ,, ▸ A [ α ]!}
