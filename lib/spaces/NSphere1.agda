
{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Int
open import lib.Paths
open import lib.AdjointEquiv
open import lib.Univalence
open Paths
open Int
open import lib.spaces.Circle

open import lib.loopspace.Basics

module lib.spaces.NSphere1 where

 module NSphere1 where
   module S where
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
   module S¹-is-S^One where
      eqv : Equiv (S¹.S¹) (S.S^ One)
      eqv = improve (hequiv (S¹.S¹-rec S.base (S.loop One))
                            (S.S-rec S¹.base S¹.loop)
                            (S¹.S¹-elim _ id ((!-inv-r S¹.loop ∘ ap∘ (ap-id S¹.loop) (ap ! ((S.βloop/rec One S¹.base S¹.loop ∘ ap (ap (S.S-rec S¹.base S¹.loop)) (S¹.βloop/rec S.base (S.loop One))) ∘ ap-o (S.S-rec S¹.base S¹.loop) (S¹.S¹-rec S.base (S.loop One)) S¹.loop) ∘ ∘-unit-l (! (ap (S.S-rec S¹.base S¹.loop o S¹.S¹-rec S.base (S.loop One)) S¹.loop)))) ∘ transport-Path ((S.S-rec S¹.base S¹.loop) o (S¹.S¹-rec S.base (S.loop One))) (\ x -> x) S¹.loop id ))
                            (S.S-elim _ id ((!-inv-r (S.loop One) ∘ ap∘ (ap-id (S.loop One)) (ap ! ((S¹.βloop/rec S.base (S.loop One) ∘ ap (ap (S¹.S¹-rec S.base (S.loop One))) (S.βloop/rec One S¹.base (S¹.loop))) ∘ ap-o (S¹.S¹-rec S.base (S.loop One)) (S.S-rec S¹.base (S¹.loop)) (S.loop One)) ∘ ∘-unit-l (! (ap (S¹.S¹-rec S.base (S.loop One) o S.S-rec S¹.base (S¹.loop)) (S.loop One))))) ∘ transport-Path ((S¹.S¹-rec S.base (S.loop One)) o (S.S-rec S¹.base (S¹.loop))) (\ x -> x) (S.loop One) id )))
   
      path : S¹.S¹ ≃ S.S^ One
      path = ua eqv

   open S public  
   

