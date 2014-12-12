
{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude

module computational-interp.presheaf.Presheaf 
       (O : Type)
       (Arr : O → O → Type)
       (1a : ∀ {w} → Arr w w)
       (_·a_ : ∀ {o1 o2 o3} → Arr o1 o2 → Arr o2 o3 → Arr o1 o3)
       where

  record Presheaf : Type where
   constructor ps 
   field
    ob  : O → Type
    arr : ∀ {w1 w2} → Arr w1 w2 → ob w1 → ob w2

  Tm : Presheaf → O → Presheaf → Type
  Tm (ps Γo Γ) w (ps Ao Aa) = ∀ {w'} → Arr w w' → Γo w' → Ao w'

  _×p_ : Presheaf → Presheaf → Presheaf
  (ps Ao Aa) ×p (ps Bo Ba) = ps (λ x → Ao x × Bo x) (λ ρ p → Aa ρ (fst p) , Ba ρ (snd p))

  _→p_ : Presheaf → Presheaf → Presheaf
  (ps Ao Aa) →p (ps Bo Ba) = ps (λ w → ∀ {w'} → Arr w w' → Ao w' → Bo w') {!!}


  ident : ∀ {Γ w} → Tm Γ w Γ
  ident = λ ρ x → x

  compose : ∀ {Γ1 Γ2 Γ3 w w'} → (ρ : Arr w w') → Tm Γ1 w Γ2 → Tm Γ2 w' Γ3 → Tm Γ1 w' Γ3
  compose ρ f g ρ' θ = g ρ' (f (ρ ·a ρ') θ)


  inst : ∀ {Γ A w1 w2} → Tm Γ w1 A → (Arr w1 w2) → Tm Γ w2 A
  inst f ρ = λ ρ' → f (ρ ·a ρ')



  -- pairs

  pair : ∀ {Γ A B w} → Tm Γ w A → Tm Γ w B → Tm Γ w (A ×p B)
  pair e1 e2 ρ θ = e1 ρ θ , e2 ρ θ

  -- on the nose
  pair-inst : ∀ {Γ A B w1 w2} → (ρ : Arr w1 w2) (e1 : Tm Γ w1 A) (e2 : Tm Γ w1 B) 
            → Path{Tm Γ w2 (A ×p B)} (inst {Γ}{A ×p B}{w1}{w2} (pair{Γ}{A}{B}{w1} e1 e2) ρ) 
                                     (pair {Γ}{A}{B}{w2} (inst {Γ}{A}{w1}{w2} e1 ρ) (inst {Γ}{B}{w1}{w2} e2 ρ) )
  pair-inst ρ e1 e2 = id

  fstp : ∀ {Γ A B w} → Tm Γ w (A ×p B) → Tm Γ w A
  fstp e ρ θ = fst (e ρ θ)

  -- on the nose
  fst-inst : ∀ {Γ A B w1 w2} → (ρ : Arr w1 w2) (e : Tm Γ w1 (A ×p B))
            → Path{Tm Γ w2 A} (inst {Γ}{A}{w1}{w2} (fstp{Γ}{A}{B}{w1} e) ρ) 
                               (fstp {Γ}{A}{B}{w2} (inst {Γ}{A ×p B}{w1}{w2} e ρ))
  fst-inst _ _ = id

  -- on the nose
  fst-β : ∀ {Γ A B w} → (e1 : Tm Γ w A) (e2 : Tm Γ w B) → Path{Tm Γ w A} (fstp{Γ}{A}{B}{w} (pair{Γ}{A}{B}{w} e1 e2)) e1
  fst-β _ _ = id
  

  -- functions

  lam : ∀ {Γ A B w} → Tm (Γ ×p A) w B → Tm Γ w (A →p B)
  lam {Γ = Γ} f ρ θ' ρ' a' = f (ρ ·a ρ') (Presheaf.arr Γ ρ' θ' , a')

  -- off by composition
  lam-inst : ∀ {Γ A B w1 w2} (ρ : Arr w1 w2) (e : Tm (Γ ×p A) w1 B) → Path{Tm Γ w2 (A →p B)} (inst {Γ}{A →p B}{w1}{w2} (lam{Γ}{A}{B}{w1} e) ρ) (lam {Γ}{A}{B}{w2} (inst{Γ ×p A}{B}{w1}{w2} e ρ))
  lam-inst ρ e = {!!}

  app : ∀ {Γ A B w} → Tm Γ w (A →p B) → Tm Γ w A → Tm Γ w B
  app f a ρ θ = f ρ θ 1a (a ρ θ)

  -- on the nose
  app-inst : ∀ {Γ A B w1 w2} (ρ : Arr w1 w2) 
           → (e1 : Tm Γ w1 (A →p B)) (e2 : Tm Γ w1 A)
           → Path{Tm Γ w2 B} (inst {Γ}{B}{w1}{w2} (app{Γ}{A}{B}{w1} e1 e2) ρ)
                             (app{Γ}{A}{B}{w2} (inst{Γ}{A →p B}{w1}{w2} e1 ρ) (inst{Γ}{A}{w1}{w2} e2 ρ))
  app-inst ρ e1 e2 = id

  -- unit and functor laws
  app-β : ∀ {Γ A B w1} (e1 : Tm (Γ ×p A) w1 B) (e2 : Tm Γ w1 A) → Path {Tm Γ w1 B} (app {Γ}{A}{B}{w1} (lam {Γ}{A}{B}{w1} e1) e2) (compose {Γ} {Γ ×p A} {B} 1a (pair {Γ} {Γ} {A} {w1} (ident{Γ}) e2) e1)
  app-β e1 e2 = {!!}

