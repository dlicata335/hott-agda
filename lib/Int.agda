{-# OPTIONS --type-in-type --without-K #-}

open import lib.First public
open import lib.Paths public
open import lib.AdjointEquiv public
open Paths
open import lib.Truncations public

module lib.Int where

module Int where
  data Positive : Type where
    One : Positive
    S   : (n : Positive) → Positive
 
  data Int : Type where
    Pos  : (n : Positive) → Int
    Zero : Int
    Neg  : (n : Positive) → Int
 
  succ : Int → Int
  succ Zero = Pos One
  succ (Pos n) = Pos (S n)
  succ (Neg One) = Zero
  succ (Neg (S n)) = Neg n
 
  pred : Int → Int
  pred Zero = Neg One
  pred (Pos (S n)) = Pos n
  pred (Pos One) = Zero
  pred (Neg n) = Neg (S n)
 
  _+_ : Int → Int → Int
  Zero + m        = m
  (Pos One) + m   = succ m
  (Pos (S n)) + m = succ (Pos n  +  m)
  (Neg One)   + m = pred m
  (Neg (S n)) + m = pred (Neg n  +  m)
 
  succ-pred : (n : Int) → Path (succ (pred n)) n
  succ-pred (Pos One) = id
  succ-pred (Pos (S y)) = id
  succ-pred (Zero) = id
  succ-pred (Neg y) = id
 
  pred-succ : (n : Int) → Path (pred (succ n)) n
  pred-succ (Pos y) = id
  pred-succ (Zero) = id
  pred-succ (Neg One) = id
  pred-succ (Neg (S y)) = id
 
  succ-pred-triangle : (x : _) → Id (succ-pred (succ x)) (ap succ (pred-succ x))
  succ-pred-triangle (Pos y) = id
  succ-pred-triangle Zero = id
  succ-pred-triangle (Neg One) = id
  succ-pred-triangle (Neg (S y)) = id
 
  pred-succ-triangle : (x : _) → Id (pred-succ (pred x)) (ap pred (succ-pred x))
  pred-succ-triangle (Pos One) = id
  pred-succ-triangle (Pos (S _)) = id
  pred-succ-triangle Zero = id
  pred-succ-triangle (Neg y) = id
 
  succEquiv : Equiv Int Int
  succEquiv = improve (hequiv succ pred pred-succ succ-pred)
  
  postulate
    HSet-Int : HSet Int
  