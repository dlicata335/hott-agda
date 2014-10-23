{-# OPTIONS --type-in-type --without-K #-}

open import lib.BasicTypes 
open import lib.cubical.Cubical

module lib.spaces.1Sphere2 where

  module S¹2 where
    private
      data S¹' : Set where
        W : S¹'
        E : S¹'

    S¹ : Set
    S¹ = S¹'

    w : S¹
    w = W

    e : S¹
    e = E

    postulate {- HoTT Axiom -}
      n : w ≃ e
      s : w ≃ e

    S¹-rec : {C : Set} 
           -> (w' : C)(e' : C)
           -> (n' : w' ≃ e') (s' : w' ≃ e')
           -> S¹ -> C
    S¹-rec a' _ _ _ W = a'
    S¹-rec _ b' _ _ E = b'

    S¹-elim : (C : S¹ -> Set)
            -> (a' : C w)(b' : C e)
            -> (_ : PathOver C n a' b') (_ : PathOver C s a' b')
            -> (x : S¹) -> C x
    S¹-elim _ a' _ _ _ W = a'
    S¹-elim _ _ b' _ _ E = b'

    postulate {- HoTT Axiom -} 
      βn/rec :  {C : Set} 
             -> (w' : C)(e' : C)
             -> (n' : w' ≃ e') (s' : w' ≃ e')
             -> ap (S¹-rec w' e' n' s') n ≃ n' 
      βs/rec :  {C : Set} 
             -> (w' : C)(e' : C)
             -> (n' : w' ≃ e') (s' : w' ≃ e')
             -> ap (S¹-rec w' e' n' s') s ≃ s' 

{-
      βloop/elim : {C : S¹ -> Set} 
                 -> (a : C base) (p : transport C loop a ≃ a)
                 -> apd (S¹-elim{C} a p) loop ≃ p
-} 

