{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open import homotopy.Hopf
import homotopy.Pi1S1
import homotopy.pi2s2.Retract
open import homotopy.pi2s2.EncDec

open Int

module homotopy.pi2s2.Inverses where

  open Truncation

  private 
    module S² = S²1

  abstract
    encode-decode' : (x : S¹.S¹) -> encode (decode' x) ≃ x
    encode-decode' = R.encode-decode' --the truncations cancel by just β-reduction
   
    decode-encode : {x : S².S²} (α : τ₁(Path S².base x)) → decode{x} (encode{x} α) ≃ α
    decode-encode{x} tα = Trunc-elim (\ α → decode{x} (encode{x} α) ≃ α)
                                     (λ α → OK _ _)
                                     case-for-[]
                                     tα 
     where
      case-for-[] : {x : S².S²} (α : (Path S².base x)) → decode{x} (encode{x} [ α ]) ≃ [ α ]
      case-for-[] id = id

      OK : (α β : τ₁(Path S².base x)) → HGpd (Path{τ₁ _} α β)
      OK α β = increment-level {S (S -2)} {_} OK1 where
        OK1 : HSet (Path{τ₁ _} α β)
        OK1 = use-level (Trunc-level {S (S (S -2))}) α β

