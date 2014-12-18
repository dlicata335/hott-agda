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

  vrev : ∀ {A m} → Vec A m → Vec A m
  vrev [] = []
  vrev {A} {S m} (x :: xs) = transport (Vec A) 
                                       (ap S (! (+-rh-Z m)) ∘ ! (+-rh-S m 0))
                                       (vrev xs ++ (x :: []))

  vfrev' : ∀ {A m n} → Vec A m → Vec A n → Vec A (m + n)
  vfrev' {A}{._}{n} [] ys = ys
  vfrev' {A} {S m}{n} (x :: xs) ys = transport (Vec A) (! (+-rh-S m n))
                                                       (vfrev' xs (x :: ys))

  correct : ∀ {A m n} (xs : Vec A m) (ys : Vec A n)
          → vrev xs ++ ys == vfrev' xs ys
  correct [] ys = id
  correct {A}{S m}{n} (x :: xs) ys = {!correct xs (x :: ys)!} where
    goal : PathOver (Vec A)
                    (id ∘ ! (+-assoc m (S 0) n)) 
                    ((vrev xs ++ (x :: [])) ++ ys)
                    (vfrev' xs (x :: ys))
    goal = hom-to-over (correct xs (x :: ys)) ∘o !o (++-assoc (vrev xs) (x :: []) ys)
      
    goal' : transport (Vec A) {!!}
                    ((vrev xs ++ (x :: [])) ++ ys)
            == (vfrev' xs (x :: ys))
    goal' = {!!}
                      

  ++-assoc' : ∀ {A m n p} 
           (xs : Vec A m) (ys : Vec A n) (zs : Vec A p)
           → transport (Vec A) (+-assoc m n p) (xs ++ (ys ++ zs))
              == ((xs ++ ys) ++ zs)
  ++-assoc' [] ys zs = id
  ++-assoc' {A} (x :: xs) ys zs = {!ap (Vec._::_ x) (++-assoc' {A} xs ys zs)!}

