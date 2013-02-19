{-# OPTIONS --type-in-type --without-K #-}

open import lib.First public
open import lib.Paths public
open import lib.Prods public
open import lib.Sums public
open import lib.AdjointEquiv 
open import lib.NType
open import lib.Truncations
open Truncation
open import lib.Nat
open import lib.DecidablePath


module lib.Int where

module Int where
  data Positive : Type where
    One : Positive
    S   : (n : Positive) → Positive

  _+1 : Positive -> Positive
  _+1 = S

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


  -- decidable equality and sets

  tpred : Positive -> Positive
  tpred One = One
  tpred (S n) = n

  decidePath-Positive : DecPath Positive
  decidePath-Positive One One = Inl id
  decidePath-Positive One (S n) = Inr (λ ())
  decidePath-Positive (S n) One = Inr (λ ())
  decidePath-Positive (S n) (S n') with decidePath-Positive n n'
  ... | Inl x = Inl (ap S x)
  ... | Inr x = Inr (x o ap tpred)

  outject : Int -> Positive
  outject (Pos n) = n
  outject (Neg n) = n
  outject (Zero) = One

  decidePath-Int : DecPath Int
  decidePath-Int (Pos n) (Pos n') with decidePath-Positive n n' 
  ... | Inl x = Inl (ap Pos x)
  ... | Inr x = Inr (x o ap outject)
  decidePath-Int (Pos n) Zero = Inr (λ ())
  decidePath-Int (Pos n) (Neg n') = Inr (λ ())
  decidePath-Int Zero (Pos n) = Inr (λ ())
  decidePath-Int Zero Zero = Inl id
  decidePath-Int Zero (Neg n) = Inr (λ ())
  decidePath-Int (Neg n) (Pos n') = Inr (λ ())
  decidePath-Int (Neg n) Zero = Inr (λ ())
  decidePath-Int (Neg n) (Neg n') with decidePath-Positive n n' 
  ... | Inl x = Inl (ap Neg x)
  ... | Inr x = Inr (x o ap outject)

  abstract
    HSet-Int : HSet Int
    HSet-Int = UIP-HSet (λ x y p q → Hedberg.UIP decidePath-Int x {y} p q)
    
  τ₀Int-is-Int : τ₀ Int ≃ Int
  τ₀Int-is-Int = Trunc-reflective (S (S -2)) HSet-Int


  -- relating Int to other kinds of numbers
  
  tlp : Positive -> TLevel
  tlp One = tl 1
  tlp (S n) = S (tlp n)

  _+1np : Nat → Positive
  Z +1np = One
  (S n) +1np = S (n +1np)

  _+pn_ : Positive → Nat → Positive
  One +pn k = k +1np
  S n +pn k = S (n +pn k)

  +pn-rh-Z : ∀ n -> n +pn Z ≃ n
  +pn-rh-Z One = id
  +pn-rh-Z (S n) = ap S (+pn-rh-Z n)

  +pn-rh-S : ∀ n k -> n +pn (S k) ≃ S (n +pn k)
  +pn-rh-S One k = id
  +pn-rh-S (S n) k = ap S (+pn-rh-S n k)

  tlp+1 : (k : Nat) → tlp (k +1np) ≃ S (tl k)
  tlp+1 Z = id
  tlp+1 (S k) = ap S (tlp+1 k)

  pos2nat : Positive -> Nat
  pos2nat One = S Z
  pos2nat (S n) = S (pos2nat n)

  -2ptl : Positive -> TLevel
  -2ptl One = (S -2)
  -2ptl (S One) = (S (S -2))
  -2ptl (S (S n)) = tl (pos2nat n)

  pos2nat-+1np : ∀ n' -> (pos2nat n' +1np) ≃ S n'
  pos2nat-+1np One = id
  pos2nat-+1np (S n') = ap S (pos2nat-+1np n')

  -2<pos-2 : ∀ n → -2 <tl -2ptl n
  -2<pos-2 One = ltS
  -2<pos-2 (S One) = ltSR ltS
  -2<pos-2 (S (S n')) = -2<nat (pos2nat n')

