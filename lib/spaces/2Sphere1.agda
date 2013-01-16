{-# OPTIONS --type-in-type --without-K #-}

open import lib.BasicTypes 

module lib.spaces.2Sphere1 where

  open Paths

  module S²1 where
    private
      data S2 : Set where
        Base : S2

    S² : Set
    S² = S2

    base : S²
    base = Base

    postulate
      loop : Refl{_}{base} ≃ Refl{_}{base}

    S²-rec : {C : Set} 
           -> (base' : C)
           -> (loop' : Refl{_}{base'} ≃ Refl{_}{base'})
           -> S² -> C
    S²-rec base' _ Base = base'

    S²-elim : (C : S² -> Set)
            -> (base' : C base)
            -> (loop' : subst (\ y -> Id (subst C y base') base') loop (Refl{_}{base'}) ≃ {! (Refl{_}{base'}) !})
            -> (x : S²) -> C x
    S²-elim C base' _ Base = base'

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

    module Elim where
      -- FIXME

{-
      βloop/elim : {C : S² -> Set} 
                 -> (a : C base) (p : subst C loop a ≃ a)
                 -> respd (S²-elim{C} a p) loop ≃ p
-} 