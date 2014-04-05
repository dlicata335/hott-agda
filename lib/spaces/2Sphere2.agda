{-# OPTIONS --type-in-type --new-without-K #-}

open import lib.BasicTypes 

module lib.spaces.2Sphere2 where

  

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

    postulate {- HoTT Axiom -}
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
            -> (n' : transport C n a' ≃ b') (s' : transport C s a' ≃ b')
            -> (fr' : transport (\ y -> Id (transport C y a') b') fr n' ≃ s') 
            -> (ba' : transport (\ y -> Id (transport C y a') b') ba n' ≃ s') 
            -> (x : S²) -> C x
    S²-elim C a' _ _ _ _ _ A = a'
    S²-elim C _ b' _ _ _ _ B = b'

    module Rec where 
     postulate {- HoTT Axiom -}
      βn :  {C : Set} 
             -> (a' : C)(b' : C)
             -> (n' : a' ≃ b') (s' : a' ≃ b')
             -> (fr' : n' ≃ s') (ba' : n' ≃ s')
             -> ap (S²-rec a' b' n' s' fr' ba') n ≃ n' 
      βs :  {C : Set} 
             -> (a' : C)(b' : C)
             -> (n' : a' ≃ b') (s' : a' ≃ b')
             -> (fr' : n' ≃ s') (ba' : n' ≃ s')
             -> ap (S²-rec a' b' n' s' fr' ba') s ≃ s' 
      βfr :  {C : Set} 
             -> (a' : C)(b' : C)
             -> (n' : a' ≃ b') (s' : a' ≃ b')
             -> (fr' : n' ≃ s') (ba' : n' ≃ s')
             -> ap (ap (S²-rec a' b' n' s' fr' ba')) fr ≃ (! (βs _ _ _ _ _ _) ∘ fr' ∘ βn _ _ _ _ _ _)
      βba :  {C : Set} 
             -> (a' : C)(b' : C)
             -> (n' : a' ≃ b') (s' : a' ≃ b')
             -> (fr' : n' ≃ s') (ba' : n' ≃ s')
             -> ap (ap (S²-rec a' b' n' s' fr' ba')) ba ≃ (! (βs _ _ _ _ _ _) ∘ ba' ∘ βn _ _ _ _ _ _)

    module Elim where
      -- FIXME

{-
      βloop/elim : {C : S² -> Set} 
                 -> (a : C base) (p : transport C loop a ≃ a)
                 -> apd (S²-elim{C} a p) loop ≃ p
-} 
