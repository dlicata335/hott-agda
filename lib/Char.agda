
{-# OPTIONS --type-in-type --without-K #-}

open import lib.Nat
open import lib.Bool

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

