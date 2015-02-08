{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open import lib.cubical.PathOver

module computational-interp.GCube2 where

  module Cube (A : Type) where

    Cube : Nat → Type 
    Boundary : Nat → Type
    d : (n : Nat) → Cube n → Boundary n
    Inside : (n : Nat) → Boundary n → Type
    CubePath : (n : Nat) → Cube n → Cube n → Type

    BCube : (l : Nat) (b : Nat) -> Type
    BBoundary : (l : Nat) (b : Nat) → Type
    BInside : (l : Nat) (b : Nat) → BBoundary l b → Type

    BCube l b = Σ \ (B : BBoundary l b) → BInside l b B

    BBoundary Z b = Unit
    BBoundary (S l) b = Σ (λ (c1 : BCube l b) → Σ (λ (c2 : BCube l b) → {!!}))

    BInside Z b B = Boundary b
    BInside (S l) b (c1 , c2 , p) = {!!}

    BoundaryPath : (n : Nat) -> Boundary n -> Boundary n -> Type
    BoundaryPath = {!!}

    Boundary 0 = Unit
    Boundary (S n) = Σ λ (c1 : Cube n) → Σ \ (c2 : Cube n) → BoundaryPath n (d n c1) (d n c2) -- d n c1 == d n c2

    Cube n = Σ \ (B : Boundary n) → Inside n B

    d n (B , _) = B

    InsideS : (n : Nat) → (c1 : Cube n) → (c2 : Cube n) → BoundaryPath n (d n c1) (d n c2) → Type
    InsideS = {!!}

    Inside Z <> = A
    Inside (S n) (c1 , c2 , p) = InsideS n c1 c2 p

    BoundaryCube = {!!}
    -- BoundaryPath Z B1 B2 = Unit
    -- BoundaryPath (S n) (c1 , c1' , p11') (c2 , c2' , p22') = 
    --   Σ (λ (p12 : CubePath n c1 c2) → 
    --   Σ (λ (p1'2' : CubePath n c1' c2') → 
    --     {!"p11' = p22' over p12 , p1'2'" !}))

    CubePath n c1 c2 = 
      Σ (λ (p : BoundaryPath n (d n c1) (d n c2)) → Inside (S n) (c1 , c2 , p))
