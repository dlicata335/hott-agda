{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 

module programming.PartialBijection2 where

  module B (A B : Type) (D : A → Type) (decD : (x : A) → Either (D x) (D x → Void)) where

    run : Equiv (Σ D) B → A → Maybe B
    run (f , _) x with decD x 
    ... | Inl indom = Some (f (x , indom))
    ... | Inr _ = None

    
    
