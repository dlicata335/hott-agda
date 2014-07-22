{-# OPTIONS --type-in-type --without-K #-}

open import lib.BasicTypes 
open import lib.cubical.Cubical

module lib.spaces.2SphereCube where

  module S²Cube where

   module S where
    private
      data S2 : Set where
        Base : S2

      data S2' : Set where
        mkS2' : S2 -> (Unit -> Unit) -> S2' 

    S² : Set
    S² = S2'

    base : S²
    base = mkS2' Base _

    postulate {- HoTT Axiom -}
      loop : Square (id{_}{base}) (id{_}{base}) (id{_}{base}) (id{_}{base})

    S²-rec : {C : Set} 
           -> (base' : C)
           -> (loop' : Square (id{_}{base'}) (id{_}{base'}) (id{_}{base'}) (id{_}{base'}))
           -> S² -> C
    S²-rec base' _ (mkS2' Base _) = base'

    S²-elim :  (C : S² -> Set)
            -> (base' : C base)
            -> (loop' : SquareOver C loop (id{_}{_}{_}{base'}) id id id)
            -> (x : S²) -> C x
    S²-elim C base' _ (mkS2' Base _) = base'

    postulate {- HoTT Axiom -}
      βloop/rec : {C : Set} 
                -> (base' : C)
                -> (loop' : Square (id{_}{base'}) (id{_}{base'}) (id{_}{base'}) (id{_}{base'}))
                -> ap-square (S²-rec base' loop') loop == loop' 

      βloop/elim : (C : S² -> Set)
                 -> (base' : C base)
                 -> (loop' : SquareOver C loop (id{_}{_}{_}{base'}) id id id)
                 -> apdo-square (S²-elim C base' loop') loop == loop'

   open S public

