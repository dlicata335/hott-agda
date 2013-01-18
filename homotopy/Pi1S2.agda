{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open Paths
open Int
open Truncation

module homotopy.Pi1S2 where

  private 
    module S² = S²1
  open S² using (S² ; S²-rec ; S²-elim ; S²-fibration)

  Codes = S²-fibration Unit (λ _ → id)

  Codes-Contractible : {x : S²} -> IsTrunc -2 (Codes x)
  Codes-Contractible {x} = (S²-elim (\ x -> IsTrunc -2 (Codes x))
                                    (istrunc (<> , (λ _ → id)))
                                    (HSet-UIP (increment-IsTrunc (IsTrunc-is-HProp _)) _ _ _ _) -- (fst (use-trunc (use-trunc (IsTrunc-Path { -1} ((Contractible o Codes) S².base) (istrunc {!\ x y → !}) _ _) _ _)))
                                    x)
  
  Codes-HSet : (x : S²) -> HSet (Codes x)
  Codes-HSet x = increment-IsTrunc (increment-IsTrunc (Codes-Contractible{x}))

  P = τ₀ o Path{S²} S².base

  encode : {x : S²} → P x → Codes x
  encode {x} tα = Trunc-rec (Codes-HSet x) 
                            (λ α → transport Codes α <>)
                            tα

  decode' : Codes S².base → τ₀ (Path {S²} S².base S².base)
  decode' _ = [ id ]

  encode-decode' : (x : Codes S².base) → encode (decode' x) ≃ x
  encode-decode' _ = id -- η

  decode : {x : S²} → Codes x → P x
  decode {x} = S²-elim (λ x' → Codes x' → P x') 
                       decode'
                       (HSet-UIP hset _ _ _ _)
                       x
     where 
       hset : ∀ {A} → HSet (Unit → τ₀ A)
       hset = ΠIsTrunc (λ _ → Trunc-is)
       
  decode-encode : {x : S²} (α : P x) → decode (encode α) ≃ α
  decode-encode{x} α = Trunc-elim (λ α' → decode {x} (encode {x} α') ≃ α')
                                  (λ x' → IsTrunc-Path _ Trunc-is _ _)
                                  case-for-[]
                                  α
    where 
      case-for-[] : {x : S²} (α : Path S².base x) → decode (encode [ α ]) ≃ [ α ]
      case-for-[] id = id

  π₁[S²]-is-1 : HEquiv (τ₀ (Path S².base S².base)) Unit
  π₁[S²]-is-1 = hequiv encode decode decode-encode encode-decode'
  