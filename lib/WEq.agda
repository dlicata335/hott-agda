
{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths 
open import lib.Prods
open import lib.Truncations
open Paths

module lib.WEq where

  HFiber : {A B : Type} -> (A -> B) -> B -> Type
  HFiber f y = Σ \x -> Path (f x) y
  
  IsWEq : (A B : Type) -> (f : A -> B) -> Type
  IsWEq A B f = (y : _) -> Contractible (HFiber f y)
  
  WEq : (A B : Type) -> Type
  WEq A B = Σ \f -> IsWEq A B f

{-
  _☆_ : {A B : Set} -> WEq A B -> A -> B
  w ☆ x = (fst w) x
-}

  -- contrPathIfContr : (A : Set) -> Contractible A -> (a b : A) -> Contractible (Path a b)
  -- contrPathIfContr A (x , c) a b = trans ((c a)) (sym (c b)) , \ x' -> {!respd c x'!} 
    -- gives subst{\ x0 -> Path x0 x} x' (c a) ≃ c b
    -- by def subst is   (c a) o (sym x') ≃ c b
    -- rearrange to      (sym (c b)) o (c a) ≃ x'