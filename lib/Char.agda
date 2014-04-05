
{-# OPTIONS --type-in-type --new-without-K #-}

open import lib.Nat
open import lib.Bool
open import lib.Sums
open import lib.First

module lib.Char where

 postulate {- Agda Primitive -}
   Char : Set
  
 {-# BUILTIN CHAR Char #-}
 {-# COMPILED_TYPE Char Char #-}
  
 ------------------------------------------------------------------------
 -- Operations
  
 module Char where

  private
   primitive
    primCharToNat    : Char → Nat
    primCharEquality : Char → Char → Bool
  
  toNat : Char → Nat
  toNat = primCharToNat
  
  equal : Char -> Char -> Bool
  equal = primCharEquality

  equals : (c d : Char) → Either (c == d) (c == d → Void)
  equals c d with equal c d
  ... | True = Inl FIXME where
    postulate FIXME : {A : Set} → A
  ... | False = Inr (\ _ -> FIXME) where
    postulate FIXME : {A : Set} → A
