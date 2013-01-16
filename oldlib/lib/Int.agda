{-# OPTIONS --type-in-type --without-K #-}

open import lib.Nat public
open import lib.Paths public
open Paths

module lib.Int where

  data Int : Set where
    Pos : Nat -> Int
    Zero : Int
    Neg : Nat -> Int

  succ : Int -> Int
  succ Zero = Pos Z
  succ (Pos n) = Pos (S n)
  succ (Neg Z) = Zero
  succ (Neg (S n)) = Neg n

  pred : Int -> Int
  pred Zero = Neg Z
  pred (Pos (S n)) = Pos n
  pred (Pos Z) = Zero
  pred (Neg n) = Neg (S n)

  succ-pred : ∀ n -> succ (pred n) ≃ n
  succ-pred (Pos Z) = Refl
  succ-pred (Pos (S y)) = Refl
  succ-pred (Zero) = Refl
  succ-pred (Neg y) = Refl

  pred-succ : ∀ n -> pred (succ n) ≃ n
  pred-succ (Pos y) = Refl
  pred-succ (Zero) = Refl
  pred-succ (Neg Z) = Refl
  pred-succ (Neg (S y)) = Refl

  succ-pred-triangle : (x : _) → Id (succ-pred (succ x)) (resp succ (pred-succ x))
  succ-pred-triangle (Pos y) = Refl
  succ-pred-triangle Zero = Refl
  succ-pred-triangle (Neg Z) = Refl
  succ-pred-triangle (Neg (S y)) = Refl

  pred-succ-triangle : (x : _) → Id (pred-succ (pred x)) (resp pred (succ-pred x))
  pred-succ-triangle (Pos Z) = Refl
  pred-succ-triangle (Pos (S _)) = Refl
  pred-succ-triangle Zero = Refl
  pred-succ-triangle (Neg y) = Refl

