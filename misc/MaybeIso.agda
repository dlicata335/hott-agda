
{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 

module misc.MaybeIso where

  f : {A B : Type} → Equiv (Maybe A) (Maybe B) → A → B
  f e x with fst e (Some x)
  ... | Some y = y
  ... | None with fst e None
  ...           | Some y' = y'
  ...           | None = {!impossible, Some = None!}

  f-inv : {A B : Type} (e : Equiv (Maybe A) (Maybe B)) → (x : A) → f (!equiv e) (f e x) == x
  f-inv e x with fst e (Some x) 
  f-inv e x | Some x₁ with fst (!equiv e) (Some x₁) 
  f-inv e x₂ | Some x₁ | Some x = {!!}
  f-inv e x | Some x₁ | None = {!!}
  f-inv e x | None = {!!}

  eqv : {A B : Type} → Equiv (Maybe A) (Maybe B) → Equiv A B
  eqv e = {!!}

