{-# OPTIONS --type-in-type --without-K #-}

open import lib.BasicTypes 

module lib.spaces.2Sphere2 where

  open Paths

  module S²2 where
    private
      data S2 : Set where
        A : S2
        B : S2

    S² : Set
    S² = S2

    a : S²
    a = A

    b : S²
    b = B

    postulate
      n : a ≃ b
      s : a ≃ b
      fr : n ≃ s
      ba : n ≃ s

    S²-rec : {C : Set} 
           -> (a' : C)(b' : C)
           -> (n' : a' ≃ b') (s' : a' ≃ b')
           -> (fr' : n' ≃ s') (ba' : n' ≃ s')
           -> S² -> C
    S²-rec a' _ _ _ _ _ A = a'
    S²-rec _ b' _ _ _ _ B = b'

    S²-elim : (C : S² -> Set)
            -> (a' : C a)(b' : C b)
            -> (n' : subst C n a' ≃ b') (s' : subst C s a' ≃ b')
            -> (fr' : subst (\ y -> Id (subst C y a') b') fr n' ≃ s') 
            -> (ba' : subst (\ y -> Id (subst C y a') b') ba n' ≃ s') 
            -> (x : S²) -> C x
    S²-elim C a' _ _ _ _ _ A = a'
    S²-elim C _ b' _ _ _ _ B = b'

    module Rec where 
     postulate
      βn :  {C : Set} 
             -> (a' : C)(b' : C)
             -> (n' : a' ≃ b') (s' : a' ≃ b')
             -> (fr' : n' ≃ s') (ba' : n' ≃ s')
             -> resp (S²-rec a' b' n' s' fr' ba') n ≃ n' 
      βs :  {C : Set} 
             -> (a' : C)(b' : C)
             -> (n' : a' ≃ b') (s' : a' ≃ b')
             -> (fr' : n' ≃ s') (ba' : n' ≃ s')
             -> resp (S²-rec a' b' n' s' fr' ba') s ≃ s' 
      βfr :  {C : Set} 
             -> (a' : C)(b' : C)
             -> (n' : a' ≃ b') (s' : a' ≃ b')
             -> (fr' : n' ≃ s') (ba' : n' ≃ s')
             -> resp (resp (S²-rec a' b' n' s' fr' ba')) fr ≃ (! (βs _ _ _ _ _ _) ∘ fr' ∘ βn _ _ _ _ _ _)
      βba :  {C : Set} 
             -> (a' : C)(b' : C)
             -> (n' : a' ≃ b') (s' : a' ≃ b')
             -> (fr' : n' ≃ s') (ba' : n' ≃ s')
             -> resp (resp (S²-rec a' b' n' s' fr' ba')) ba ≃ (! (βs _ _ _ _ _ _) ∘ ba' ∘ βn _ _ _ _ _ _)

    module Elim where
      -- FIXME

{-
      βloop/elim : {C : S² -> Set} 
                 -> (a : C base) (p : subst C loop a ≃ a)
                 -> respd (S²-elim{C} a p) loop ≃ p
-} 