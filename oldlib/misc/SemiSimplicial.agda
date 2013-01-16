{-# OPTIONS --type-in-type --no-positivity-check #-}

open import lib.Prelude

module misc.SemiSimplicial where

  sZero = Set

  sOne = Σ \ (X : sZero) -> (X -> X -> Set)

  sTwo = Σ {sOne} \ {(X , R) -> (x y z : X) → R x y → R y z → R x z → Set}

  sThree = Σ {sTwo} \ {((X , R1) , R2) -> {!(x y z w : X) -> !}}

  mutual 

    SSSet : Nat -> Set
    SSSet 0 = Set
    SSSet (S n) = Σ \ (p : SSSet n) -> ((Tetra n p) -> Set)

    data Tetra : (n : Nat) -> SSSet n -> Set where
      t0 : ∀ {X} -> X -> X -> Tetra 0 X
      t1 : ∀ {X R} -> ∀ {x y z} -> R (t0 x y) -> R (t0 y z) -> R (t0 x z) -> Tetra 1 (X , R) 
--      Tetra 3 ((X , R1) , R2) = {!!}
--      Tetra 4 (((X , R1) , R2) , R3) = {!!}
--    Tetra n _ = {!!}

    x : SSSet 1
    x = Nat , (λ {(t0 x y) → Id x y})

    x2 : SSSet 2
    x2 = x , λ {(t1 a b c) → {!!}}