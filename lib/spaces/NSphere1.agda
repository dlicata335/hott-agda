
{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Int
open import lib.Paths
open Paths
open Int
open import lib.LoopSpace

module lib.spaces.NSphere1 where

  module NSphere1 where
    private
      data S' (n : Positive) : Set where
        Base : S' n
  
    S^ : Positive -> Set
    S^ n = S' n
  
    base : ∀ {n} → S^ n
    base = Base
  
    postulate
      loop : (n : Positive) → Loop (S^ n) base n
  
    S-rec : {n : Positive} {C : Set} 
           -> (c : C)
           -> (α : Loop C c n)
           -> S^ n -> C
    S-rec a _ Base = a

    postulate 
      βloop/rec : ∀ {n} {C : Set} 
           -> (c : C)
           -> (α : Loop C c n)
           -> Path (ap^ n (S-rec c α) (loop n)) α
  
    {-
    S¹-elim :  (C : S¹ -> Set)
            -> (c : C base) 
               (α : Path (transport C loop c) c)
            -> (x : S¹) -> C x
    S¹-elim _ x _ Base = x

      βloop/elim : {C : S¹ -> Set} 
                 -> (c : C base) (α : Path (transport C loop c) c)
                 -> Path (apd (S¹-induction C c α) loop) α
    -}
  