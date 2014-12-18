{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open import lib.cubical.Cubical

module Misc.VecAssoc where

  data Vec (A : Type) : Nat → Type where
    [] : Vec A 0
    _::_ : ∀ {n} → A → Vec A n → Vec A (S n)

  open NatM

  _++_ : ∀ {A m n} → Vec A m → Vec A n → Vec A (m + n)
  [] ++ ys = ys
  (x :: xs) ++ ys = x :: (xs ++ ys)
  
  ++-assoc : ∀ {A m n p} 
           (xs : Vec A m) (ys : Vec A n) (zs : Vec A p)
           → PathOver (Vec A) (+-assoc m n p) 
                              (xs ++ (ys ++ zs))
                              ((xs ++ ys) ++ zs)
  ++-assoc [] ys zs = id
  ++-assoc {A} (x :: xs) ys zs = 
    over-o-ap (Vec A) {S} (ap-nt-over (_::_ x) (++-assoc xs ys zs))

