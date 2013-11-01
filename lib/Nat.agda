
{-# OPTIONS --type-in-type --without-K #-}

open import lib.First

module lib.Nat where

  data Nat : Type where
    Z : Nat
    S : Nat -> Nat

  {-# BUILTIN NATURAL Nat #-}
  {-# BUILTIN SUC S #-}
  {-# BUILTIN ZERO Z #-}

  module NatM where
  
    natrec : {p : Nat -> Type} -> 
              p Z -> 
              ((n : Nat) -> p n -> p (S n)) -> 
              (n : Nat) -> p n
    natrec zc sc Z = zc
    natrec zc sc (S n) = sc n (natrec zc sc n)
    
    _+_ : Nat -> Nat -> Nat
    _+_ Z n = n
    _+_ (S n) n' = S (n + n')

    +-rh-Z : (n : Nat) → n == (n + Z)
    +-rh-Z Z = id
    +-rh-Z (S n) = ap S (+-rh-Z n)
  
    +-assoc : (n m p : Nat) → n + (m + p) == (n + m) + p
    +-assoc Z m p = id
    +-assoc (S n) m p = ap S (+-assoc n m p)

    max : Nat -> Nat -> Nat
    max  Z    m      = m
    max (S n)  Z     = S n
    max (S n) (S m)  = S (max n m)

{-
    disjoint : {m : Nat} → Path{Nat} (S m) Z → {!!}
    disjoint ()

    injective : {m n : Nat} → Path{Nat} (S m) (S n) -> m ≃ n
    injective id = id
-}
