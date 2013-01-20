{-# OPTIONS --type-in-type --without-K #-}

open import lib.BasicTypes 

module lib.spaces.2Sphere1 where

  open Paths

  module S²1 where

   module S where
    private
      data S2 : Set where
        Base : S2

    S² : Set
    S² = S2

    base : S²
    base = Base

    postulate
      loop : id{_}{base} ≃ id{_}{base}

    S²-rec : {C : Set} 
           -> (base' : C)
           -> (loop' : id{_}{base'} ≃ id{_}{base'})
           -> S² -> C
    S²-rec base' _ Base = base'

    S²-elim :  (C : S² -> Set)
            -> (base' : C base)
            -> (loop' : transport (\ y -> Path (transport C y base') base')
                                  loop 
                                  (id{_}{base'})
                        ≃ id {_} {base'})
            -> (x : S²) -> C x
    S²-elim C base' _ Base = base'

    postulate
      βloop/rec : {C : Set} 
                -> (base' : C)
                -> (loop' : id{_}{base'} ≃ id{_}{base'})
                -> ap (ap (S²-rec base' loop')) loop ≃ loop'

   open S public

   S²-fibration : (A : Type) 
                  → ((x : A) → Path x x)
                  → S² → Type
   S²-fibration A α = S²-rec A (loop-family->id-loop α)
 
   S²-fibration/βloop : {A : Type}
                        (α : (x : A) → Path x x)
                      → ap (ap (S²-fibration A α)) loop ≃ 
                        (loop-family->id-loop α)
   S²-fibration/βloop α = βloop/rec _ _


{-
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
-}

