{-# OPTIONS --type-in-type --without-K #-}

open import lib.BasicTypes 
open import lib.cubical.Cubical

module lib.spaces.3SphereCube where

  module S³Cube where

   module S where
    private
      data S3 : Set where
        Base : S3

      data S3' : Set where
        mkS3' : S3 -> (Unit -> Unit) -> S3' 

    S³ : Set
    S³ = S3'

    base : S³
    base = mkS3' Base _

    postulate {- HoTT Axiom -}
      loop : Cube {_}{base} id id id id id id 

    S³-rec : {C : Set} 
           -> (base' : C)
           -> (loop' : Cube {_}{base'} id id id id id id )
           -> S³ -> C
    S³-rec base' _ (mkS3' Base _) = base'

    S³-elim :  (C : S³ -> Set)
            -> (base' : C base)
            -> (loop' : CubeOver C {base'} loop id id id id id id )
            -> (x : S³) -> C x
    S³-elim C base' _ (mkS3' Base _) = base'

    postulate {- HoTT Axiom -}
      βloop/rec : {C : Set} 
                -> (base' : C)
                -> (loop' : Cube {_}{base'} id id id id id id)
                -> ap-cube (S³-rec base' loop') loop == loop' 

{-
      βloop/elim : (C : S² -> Set)
                 -> (base' : C base)
                 -> (loop' : SquareOver C loop (id{_}{_}{_}{base'}) id id id)
                 -> apdo-square (S²-elim C base' loop') loop == loop'
-}

   open S public

