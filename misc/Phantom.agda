
{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude

module misc.Phantom where

module S where
      private
        data S¹' : Type where
          Base : S¹'
    
      S¹ : Type
      S¹ = S¹'
    
      base : S¹
      base = Base

      postulate {- HoTT Axiom -}
        loop : Path base base
    
      S¹-rec' : {C : Type} 
             -> (c : C)
             -> (p : c ≃ c) (_ : Phantom p)
             -> S¹ -> C
      S¹-rec' c p (Phantom.phantom <>⁺) Base = c

      S¹-rec : {C : Type} 
             -> (c : C)
             -> (p : c ≃ c) 
             -> S¹ -> C
      S¹-rec c p = S¹-rec' c p (Phantom.phantom <>⁺)

{-
test : {C : Type} 
     -> (c : C)
     -> (p q : c ≃ c)
     → S.S¹-rec c p ≃ S.S¹-rec c q 
test c p q = id
-}

test' : {C : Type} 
     -> (c : C)
     -> (p : c ≃ c)
     → S.S¹-rec c p S.base ≃ c
test' c p = id
