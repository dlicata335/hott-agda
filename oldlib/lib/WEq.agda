
{-# OPTIONS --type-in-type --without-K #-}

open import lib.Paths 
open import lib.Prods
open Paths

module lib.WEq where

  Contractible : Set -> Set
  Contractible A = Σ \(t : A) -> (x : A) -> Id x t
  
  HFiber : {A B : Set} -> (A -> B) -> B -> Set
  HFiber f y = Σ \x -> Id (f x) y
  
  WEqBy : (A B : Set) -> (f : A -> B) -> Set
  WEqBy A B f = (y : _) -> Contractible (HFiber f y)
  
  WEq : (A B : Set) -> Set
  WEq A B = Σ \f -> WEqBy A B f

  _☆_ : {A B : Set} -> WEq A B -> A -> B
  w ☆ x = (fst w) x

  -- contrIdIfContr : (A : Set) -> Contractible A -> (a b : A) -> Contractible (Id a b)
  -- contrIdIfContr A (x , c) a b = trans ((c a)) (sym (c b)) , \ x' -> {!respd c x'!} 
    -- gives subst{\ x0 -> Id x0 x} x' (c a) ≃ c b
    -- by def subst is   (c a) o (sym x') ≃ c b
    -- rearrange to      (sym (c b)) o (c a) ≃ x'