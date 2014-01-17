{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open import lib.PathOver

module computational-interp.GCube where

  module Cube (A : Type) where

    Cube : Nat → Type 
    Boundary : Nat → Type
    d : (n : Nat) → Cube n → Boundary n
    Inside : (n : Nat) → Boundary n → Type
    CubePath : (n : Nat) → Cube n → Cube n → Type
    BoundaryPath : (n : Nat) -> Boundary n -> Boundary n -> Type

    Boundary 0 = Unit
    Boundary (S n) = Σ λ (c1 : Cube n) → Σ \ (c2 : Cube n) → BoundaryPath n (d n c1) (d n c2) -- d n c1 == d n c2

    Cube n = Σ \ (B : Boundary n) → Inside n B

    d n (B , _) = B

    postulate 
      InsideS : (n : Nat) → (c1 : Cube n) → (c2 : Cube n) → BoundaryPath n (d n c1) (d n c2) → Type

    Inside Z <> = A
    Inside (S n) (c1 , c2 , p) = InsideS n c1 c2 p

    BoundaryPath Z B1 B2 = Unit
    BoundaryPath (S n) (c1 , c1' , p11') (c2 , c2' , p22') = 
      Σ (λ (p12 : CubePath n c1 c2) → 
      Σ (λ (p1'2' : CubePath n c1' c2') → 
        {!"p11' = p22' over p12 , p1'2'"? !}))

    CubePath n c1 c2 = 
      Σ (λ (p : BoundaryPath n (d n c1) (d n c2)) → Inside (S n) (c1 , c2 , p))

    test1 : Cube 1 → _
    test1 (((<> , a) , (<> , b) , <>) , pab) = {!!}

    test2 : Cube 2 → _
    test2 (((((<> , a) , (<> , b) , <>) , pab) , (((<> , c) , (<> , d) , <>) , pcd) , (<> , pac) , (<> , pbd) , XXX) , sq) 
      = {!snd₁!} -- XXX should be unit

    test3 : Cube 3 → _
    test3 (((((((<> , a) , (<> , b) , <>) , pab) , 
              (((<> , c) , (<> , d) , <>) , pcd) , 
              (<> , pac) , (<> , pbd) , trivabcd) , sqabcd) , 
           (((((<> , a') , (<> , b') , <>) , pab') , 
             (((<> , c') , (<> , d') , <>) , pcd') , 
              (<> , pac') , (<> , pbd') , triva'b'c'd') , sqa'b'c'd') , 
           (((<> , paa') , (<> , pbb') , trivaba'b') , sqaba'b') , 
           (((<> , pcc') , (<> , pdd') , trivcdc'd') , sqcdc'd') , 
           x) , 
          cub) = {!x!}
