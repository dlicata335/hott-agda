{-# OPTIONS --type-in-type --without-K #-}

open import lib.BasicTypes 

module lib.spaces.1Sphere2 where

  

  module S¹2 where
    private
      data S¹' : Set where
        A : S¹'
        B : S¹'

    S¹ : Set
    S¹ = S¹'

    a : S¹
    a = A

    b : S¹
    b = B

    postulate {- HoTT Axiom -}
      n : a ≃ b
      s : a ≃ b

    S¹-rec : {C : Set} 
           -> (a' : C)(b' : C)
           -> (n' : a' ≃ b') (s' : a' ≃ b')
           -> S¹ -> C
    S¹-rec a' _ _ _ A = a'
    S¹-rec _ b' _ _ B = b'

    S¹-elim : {C : S¹ -> Set} 
            -> (a' : C a)(b' : C b)
            -> (_ : transport C n a' ≃ b') (_ : transport C s a' ≃ b')
            -> (x : S¹) -> C x
    S¹-elim a' _ _ _ A = a'
    S¹-elim _ b' _ _ B = b'

    postulate {- HoTT Axiom -} 
      βn/rec :  {C : Set} 
             -> (a' : C)(b' : C)
             -> (n' : a' ≃ b') (s' : a' ≃ b')
             -> ap (S¹-rec a' b' n' s') n ≃ n' 
      βs/rec :  {C : Set} 
             -> (a' : C)(b' : C)
             -> (n' : a' ≃ b') (s' : a' ≃ b')
             -> ap (S¹-rec a' b' n' s') s ≃ s' 

{-
      βloop/elim : {C : S¹ -> Set} 
                 -> (a : C base) (p : transport C loop a ≃ a)
                 -> apd (S¹-elim{C} a p) loop ≃ p
-} 
