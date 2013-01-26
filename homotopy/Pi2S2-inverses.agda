{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open import homotopy.Hopf
import homotopy.Pi1S1
import homotopy.Pi2S2-retract
open import homotopy.Pi2S2-encdec
open Paths
open Int

module homotopy.Pi2S2-inverses where

  open Truncation

  private 
    module S² = S²1
  open S² using (S² ; S²-rec ; S²-elim)
  open S¹ using (S¹ ; S¹-rec ; S¹-elim)

  abstract
    encode-decode' : (x : S¹) -> encode (decode' x) ≃ x
    encode-decode' = R.encode-decode' --the truncations cancel by just β-reduction
   
    decode-encode : {x : S²} (α : τ₁(Path S².base x)) → decode{x} (encode{x} α) ≃ α
    decode-encode{x} tα = Trunc-elim (\ α → decode{x} (encode{x} α) ≃ α)
                                     OK 
                                     case-for-[]
                                     tα 
     where
      case-for-[] : {x : S²} (α : (Path S².base x)) → decode{x} (encode{x} [ α ]) ≃ [ α ]
      case-for-[] id = id

      OK : (α : τ₁(Path S².base x)) → HGpd (Path{τ₁ _} (decode{x} (encode{x} α)) α)
      OK α = increment-IsTrunc {S (S -2)} {_} OK1 where
        OK1 : HSet (Path{τ₁ _} (decode{x} (encode{x} α)) α)
        OK1 = use-trunc (Trunc-is {S (S (S -2))}) (decode {x} (encode {x} α)) α

