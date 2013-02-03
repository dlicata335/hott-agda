
{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Int
open import lib.Paths
open Paths
open Int

open import lib.loopspace.Basics

module lib.spaces.NSphere1 where

  module NSphere1 where
    private
      data S' (n : Positive) : Type where
        Base : S' n
  
    S^ : Positive -> Type
    S^ n = S' n
  
    base : ∀ {n} → S^ n
    base = Base
  
    postulate {- HoTT Axiom -}
      loop : (n : Positive) → Loop n (S^ n) base
  
    S-rec : {n : Positive} {C : Type} 
           -> (c : C)
           -> (α : Loop n C c)
           -> S^ n -> C
    S-rec a _ Base = a

    postulate {- HoTT Axiom -} 
      βloop/rec : (n : _) {C : Type} 
           -> (c : C)
           -> (α : Loop n C c)
           -> Path (ap^ n (S-rec c α) (loop n)) α
  
    S-elim :   ∀ {n} (C : S^ n -> Type)
            -> (c : C base) 
               (α : LoopOver n (loop n) C c)
            -> (x : S^ n) -> C x
    S-elim _ x _ Base = x

    -- FIXME: need to define apd^, but fortunately this
    -- doesn't come up very often (e.g. pi2(s2) doesn't use it)
    {-
      βloop/elim : {C : S¹ -> Set} 
                 -> (c : C base) (α : Path (transport C loop c) c)
                 -> Path (apd (S¹-induction C c α) loop) α
    -}
  