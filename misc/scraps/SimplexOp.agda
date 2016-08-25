{-# OPTIONS --type-in-type #-}

open import lib.Prelude
open ListM

module misc.SimplexOp where

  data Variance : Set where
    + - : Variance

  Ctx : Set 
  Ctx = List String × Variance

  -- opv : Variance → Variance
  -- opv + = -
  -- opv - = +

  -- _op : Ctx → Ctx
  -- (Ψ , v) op = (rev Ψ , opv v)

  ⊥ : Variance → String
  ⊥ + = "0"
  ⊥ - = "1"

  ⊤ : Variance → String
  ⊤ + = "1"
  ⊤ - = "0"

  data _⊩_ : List String → List String → Set where
    Nil  : ∀ {Ψ} → Ψ ⊩ []
    Cons : ∀ {Ψ Ψ1 x Ψ2 y Ψ'}
         → Ψ == (Ψ1 ++ (x :: Ψ2)) 
         → (x :: Ψ2) ⊩ Ψ'
         → Ψ ⊩ (y :: Ψ')

  data _⊢_ : Ctx → Ctx → Set where
    co  : ∀ {Ψ1 Ψ2 v1 v2} → (⊥ v1 :: (Ψ1 ++ [ ⊤ v1 ])) ⊩ Ψ2 → (Ψ1 , v1) ⊢ (Ψ2 , v2) 
    con : ∀ {Ψ1 Ψ2 v1 v2} → (⊤ v1 :: (rev Ψ1 ++ [ ⊥ v1 ])) ⊩ Ψ2 → (Ψ1 , v1) ⊢ (Ψ2 , v2) 


  lweaken : ∀ {Ψ Ψ' x} → Ψ ⊩ Ψ' → (x :: Ψ ⊩ Ψ')
  lweaken Nil = Nil
  lweaken {x = x} (Cons {Ψ1 = Ψ1} s ρ) = Cons {Ψ1 = x :: Ψ1} (ap (_::_ x) s) ρ

  ident'' : ∀ Ψ → Ψ ⊩ Ψ
  ident'' [] = Nil
  ident'' (x₁ :: Ψ) = Cons {Ψ1 = []} id (lweaken (ident'' Ψ))

  rweaken : ∀ {Ψ x Ψ'} → Ψ ⊩ Ψ' → (Ψ ++ [ x ]) ⊩ Ψ'
  rweaken Nil = Nil
  rweaken {x = x0} (Cons {Ψ1 = Ψ1} {x = x} {Ψ2 = Ψ2} s ρ) = 
    Cons {Ψ1 = Ψ1} {x = x} {Ψ2 = Ψ2 ++ [ x0 ]} ({!assoc!} ∘ ap (λ h → h ++ [ x0 ]) s) (rweaken ρ)

  ident' : ∀ {x y} Ψ → (x :: (Ψ ++ [ y ])) ⊩ Ψ
  ident' Ψ = rweaken (lweaken (ident'' Ψ))

  ident : ∀ Ψ → Ψ ⊢ Ψ
  ident (Ψ , v) = co (ident' Ψ)

  ConsR : ∀ {Ψ Ψ1 x Ψ2 y Ψ'}
         → Ψ == (Ψ1 ++ (x :: Ψ2)) 
         → (Ψ1 ++ [ x ]) ⊩ Ψ'
         → Ψ ⊩ (Ψ' ++ [ y ])
  ConsR {Ψ1 = Ψ1} {x} {Ψ2} {Ψ' = []} s ρ = 
    Cons {Ψ1 = Ψ1} {x} {Ψ2} s Nil
  ConsR {Ψ1 = Ψ1} {x} {Ψ2} {Ψ' = a :: Ψ''} s (Cons {Ψ1 = Ψ1'} {x'} {Ψ2'} s' ρ) = 
    Cons {Ψ1 = Ψ1} {x} {Ψ2} s 
         (ConsR {Ψ1 = {!!}} {x = {!!}} {Ψ2 = {!!}} {!!} ρ) -- need (Ψ1'' ++ [ x'' ]) = x' :: Ψ2'

  extend : ∀ {Ψ Ψ' x y x' y'} 
           → (x :: (Ψ ++ [ y ])) ⊩ Ψ'
           → (x :: (Ψ ++ [ y ])) ⊩ (x' :: (Ψ' ++ [ y' ]))
  extend {Ψ} {x = x} {y} ρ = Cons {Ψ1 = []} {x} {Ψ ++ [ y ]} id (ConsR {Ψ1 = x :: Ψ} {y} {[]} id ρ)

  compose'' : ∀ {Ψ Ψ' Ψ''} 
           → Ψ ⊩ Ψ'
           → Ψ' ⊩ Ψ''
           → Ψ ⊩ Ψ''
  compose'' ρ Nil = Nil
  compose'' (Cons {Ψ1 = Ψ1} {x}{Ψ2} id ρ) (Cons {Ψ1 = []} id ρ') = 
    Cons {Ψ1 = Ψ1} {x} {Ψ2} id (compose'' (Cons {Ψ1 = []} {x} id ρ) ρ')    
  compose'' Nil (Cons {Ψ1 = []} () ρ') 
  compose'' (Cons s ρ) (Cons {Ψ1 = a1 :: Ψ1} id ρ') = 
    {!need a lemma!}
  compose'' Nil (Cons {Ψ1 = _ :: Ψ1} () ρ')

  compose' : ∀ {Ψ Ψ' Ψ'' x y x' y'} 
           → (x :: (Ψ ++ [ y ])) ⊩ Ψ'
           → (x' :: (Ψ' ++ [ y' ])) ⊩ Ψ''
           → (x :: (Ψ ++ [ y ])) ⊩ Ψ''
  compose' {Ψ} {Ψ'} {Ψ''} {x} {y} {x'} {y'} ρ ρ' =
    compose'' {Ψ = x :: (Ψ ++ [ y ])} {Ψ' = x' :: (Ψ' ++ [ y' ])} {Ψ'' = Ψ''} (extend {Ψ}{Ψ'}{x}{y}{x'}{y'} ρ) ρ'

  flip : ∀ {Ψ Ψ'} 
           → Ψ ⊩ Ψ'
           → rev Ψ ⊩ rev Ψ'
  flip Nil = Nil
  flip (Cons {Ψ1 = Ψ1} {x} {Ψ2} s ρ) = ConsR {Ψ1 = rev Ψ2} {x} {rev Ψ1} ({!!} ∘ ap rev s) (flip ρ)

  compose : ∀ {Ψ Ψ' Ψ''} → Ψ ⊢ Ψ' → Ψ' ⊢ Ψ'' → Ψ ⊢ Ψ''
  compose {Ψ , v} {Ψ' , v'} {Ψ'' , v''} (co ρ) (co ρ') = co (compose' {Ψ = Ψ} {Ψ' = Ψ'} {Ψ'' = Ψ''} ρ ρ')
  compose {Ψ , v} {Ψ' , v'} {Ψ'' , v''} (con ρ) (co ρ') = con (compose' {Ψ = rev Ψ} {Ψ' = Ψ'} {Ψ'' = Ψ''} ρ ρ')
  compose {Ψ , v} {Ψ' , v'} {Ψ'' , v''} (co ρ) (con ρ') = con (compose' {Ψ = rev Ψ} {Ψ' = rev Ψ'} {Ψ'' = Ψ''} {!flip ρ!} ρ')
  compose {Ψ , v} {Ψ' , v'} {Ψ'' , v''} (con ρ) (con ρ') = co (compose' {Ψ = Ψ} {Ψ' = rev Ψ'} {Ψ'' = Ψ''} {!flip ρ!} ρ')

  
