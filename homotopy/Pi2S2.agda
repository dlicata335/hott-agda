{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open import homotopy.Hopf
import homotopy.Pi1S1
import homotopy.HigherHomotopyAbelian
import homotopy.Pi2S2-retract
open Paths
open Int

module homotopy.Pi2S2 where

  open Truncation
  module R = homotopy.Pi2S2-retract

  private 
    module S² = S²1
  open S² using (S² ; S²-rec ; S²-elim)
  open S¹ using (S¹ ; S¹-rec ; S¹-elim)

  encode : {x : S²} -> τ₁ (Path{S²} S².base x) -> H x
  encode {x} α = Trunc-rec (H-is-1-truncated x) R.encode α

  encode' : τ₁ (Path{S²} S².base S².base) -> S¹
  encode' = encode{S².base}

  decode' : S¹ → τ₁ (Path S².base S².base)
  decode' = [_] o R.decode'

  encode-decode' : (x : S¹) -> encode (decode' x) ≃ x
  encode-decode' = R.encode-decode' --the truncations cancel by just β-reduction

  decode : {x : S²} -> H x → τ₁ (Path{S²} S².base x)
  decode{x} = S²-elim (λ x' → H x' → τ₁ (Path {S²} S².base x')) 
                      decode' 
                      ?
                      x
{-
                      where

   abstract
     respects-loop : transport (λ y → Path (transport (λ x' → H x' → τ₁(Path S².base x')) y decode') decode') S².loop id ≃ id
     respects-loop = (transport (λ y → Path (transport (λ x' → H x' → τ₁(Path S².base x')) y decode') decode') S².loop id ≃〈 transport-Path (λ y → transport (λ x' → H x' → τ₁(Path S².base x')) y decode') (λ y → decode') S².loop id 〉 
                      (ap (\ _ -> decode') S².loop)
                      ∘ id
                      ∘ ! (ap (\ y -> (transport (λ x' → H x' → τ₁(Path S².base x')) y decode')) S².loop) ≃〈 ap (λ x' → ap (λ _ → decode') S².loop ∘ x') (∘-unit-l (! (ap (λ y → transport (λ x' → H x' → τ₁(Path S².base x')) y decode') S².loop))) 〉 
                      (ap (\ _ -> decode') S².loop)
                      ∘ ! (ap (\ y -> (transport (λ x' → H x' → τ₁(Path S².base x')) y decode')) S².loop) ≃〈 ap (λ x' → x' ∘ ! (ap (λ y → transport (λ x0 → H x0 → τ₁(Path S².base x0)) y decode') S².loop)) (ap-constant decode' S².loop) 〉 
                      id
                      ∘ ! (ap (\ y -> (transport (λ x' → H x' → τ₁(Path S².base x')) y decode')) S².loop) ≃〈 ∘-unit-l (! (ap (λ y → transport (λ x' → H x' → τ₁(Path S².base x')) y decode') S².loop)) 〉 
                      ! (ap (\ y -> (transport (λ x' → H x' → τ₁(Path S².base x')) y decode')) S².loop) ≃〈 ap ! STS 〉 
                      id ∎) where
            
            STS : (ap (\ y -> (transport (λ x' → H x' → τ₁(Path S².base x')) y decode')) S².loop) ≃ id {_} {decode'}
            STS = ap (λ y → transport (λ x' → H x' → τ₁(Path S².base x')) y decode') S².loop ≃〈 ap-by-equals (λ α → transport-→ H (τ₁ o Path S².base) α decode') S².loop 〉 
                  id ∘ ap (λ α → transport (τ₁ o Path S².base) α o decode' o transport H (! α)) S².loop ≃〈 ∘-unit-l (ap (λ α → transport (τ₁ o Path S².base) α o decode' o transport H (! α)) S².loop) 〉 
                  ap (λ α → transport (τ₁ o Path S².base) α o decode' o transport H (! α)) S².loop ≃〈 ap-of-o (λ α → transport (τ₁ o Path S².base) α o decode') (λ α → transport H (! α)) S².loop 〉 
                  λ≃ (\ (x : S¹) → ap≃₁→ (ap (\ α' -> transport (τ₁ o Path S².base) α' o decode') S².loop)
                                         (ap (\ β -> transport H (! β) x) S².loop)) ≃〈 ap λ≃ (λ≃ STS2) 〉 
                  λ≃ (\ x -> id) ≃〈 ! (Π≃η id) 〉 
                  id ∎ 
             where
              STS2 : (x : S¹) → ap≃₁→ (ap (\ α' -> transport (τ₁ o Path S².base) α' o decode') S².loop)
                                      (ap (\ β -> transport H (! β) x) S².loop)
                               ≃ id
              STS2 = 
                     S¹-elim (\ x -> ap≃₁→ (ap (\ α' -> transport (τ₁ o Path S².base) α' o decode') S².loop)
                                           (ap (\ β -> transport H (! β) x) S².loop) ≃ id)
                             (ap≃₁→
                                (ap (λ α' → transport (τ₁ o Path S².base) α' o decode') S².loop)
                                (ap (λ β → transport H (! β) S¹.base) S².loop) ≃〈 ap (λ x' → ap≃₁→ (ap (λ α' → transport (τ₁ o Path S².base) α' o decode') S².loop) x') STS3 〉 
                             (ap≃₁→
                                  (ap (λ α' → transport (τ₁ o Path S².base) α' o decode') S².loop)
                                  (! S¹.loop))                                 ≃〈 ap (λ x' → ap≃₁→ x' (! S¹.loop)) STS4 〉 
                             (ap≃₁→
                                  (λ≃ (λ y → ap (λ α' → transport (τ₁ o Path S².base) α' (decode' y)) S².loop))
                                  (! S¹.loop)) ≃〈 →≃β1 (λ y → ap (λ α' → transport (τ₁ o Path S².base) α' (decode' y)) S².loop) (! S¹.loop) 〉
                             (ap decode' (! S¹.loop)
                              ∘ ap (λ α' → transport (τ₁ o Path S².base) α' (decode' S¹.base)) S².loop) ≃〈 ap (λ x' → x' ∘ ap (λ α' → transport (τ₁ o Path S².base) α' (decode' S¹.base)) S².loop) (ap-! decode' S¹.loop) 〉 
                             (! (ap decode' S¹.loop)
                              ∘ ap (λ α' → transport (τ₁ o Path S².base) α' (decode' S¹.base)) S².loop) ≃〈 ap (λ x' → ! x' ∘ ap (λ α' → transport (τ₁ o Path S².base) α' (decode' S¹.base)) S².loop) (ap-o [_] R.decode' S¹.loop) 〉 
                             (! (ap [_] (ap R.decode' S¹.loop))
                              ∘ ap (λ α' → transport (τ₁ o Path S².base) α' [ id ]) S².loop) ≃〈 ap (λ x' → ! (ap [_] x') ∘ ap (λ α' → transport (τ₁ o Path S².base) α' (decode' S¹.base)) S².loop) (S¹.βloop/rec id S².loop) 〉 
                             (! (ap [_] S².loop)
                              ∘ ap (λ α' → transport (τ₁ o Path S².base) α' [ id ]) S².loop) ≃〈 ap (λ x' → ! (ap [_] S².loop) ∘ x') STS5 〉 
                             (! (ap [_] S².loop)
                              ∘ ap [_] S².loop) ≃〈 !-inv-l (ap [_] S².loop) 〉 
                             id ∎)
                             (fst (Trunc-is {S (S (S -2))} {Path S².base S².base} _ _ _ _ _ _))
               where 
                STS3 : (ap (λ β → transport H (! β) S¹.base) S².loop) ≃ ! S¹.loop
                STS3 = (ap (λ β → transport H (! β) S¹.base) S².loop)    ≃〈 ap-o (λ z → transport H z S¹.base) ! S².loop 〉 
                       (ap (λ β → transport H β S¹.base) (ap ! S².loop)) ≃〈 ap (λ y → ap (λ β → transport H β S¹.base) y) (! (homotopy.HigherHomotopyAbelian.inverse-same S² S².base S².loop)) 〉 
                       (ap (λ β → transport H β S¹.base) (! S².loop))    ≃〈 R.transport-H-!loop2 〉 
                       ! S¹.loop ∎

                STS4 :   (ap (λ α' → transport (τ₁ o Path S².base) α' o decode') S².loop)
                       ≃ λ≃ (λ y → ap (λ α' → transport (τ₁ o Path S².base) α' (decode' y)) S².loop)
                STS4 = (ap (λ α' → transport (τ₁ o Path S².base) α' o decode') S².loop) ≃〈 id 〉
                       (ap (λ α' → (\ (y : S¹) → transport (τ₁ o Path S².base) α' (decode' y))) S².loop)  ≃〈 ap-λ-range-nd (λ α' → λ (y : S¹) → transport (τ₁ o Path S².base) α' (decode' y)) S².loop 〉
                       (λ≃ (\ y -> (ap (\α' → transport (τ₁ o Path S².base) α' (decode' y))) S².loop))    ≃〈 ap λ≃ (λ≃ (λ y → ap-app-1-nd (λ α' → transport (τ₁ o Path S².base) α') S².loop (decode' y))) 〉
                       (λ≃ (\ y -> (ap≃ (ap (\α' → transport (τ₁ o Path S².base) α') S².loop)
                                        {(decode' y)})))                                                 ≃〈 ap λ≃ (λ≃ (λ y → ap (λ x' → ap≃ x') (ap-λ-range-nd (λ α' → transport (τ₁ o Path S².base) α') S².loop))) 〉
                       (λ≃ (\ y -> (ap≃ (λ≃ (\β → ap (\ α' → transport (τ₁ o Path S².base) α' β) S².loop))
                                        {(decode' y)})))                                                 ≃〈 ap λ≃ (λ≃ (λ y → Π≃β (\β → ap (\ α' → transport (τ₁ o Path S².base) α' β) S².loop))) 〉
                       (λ≃ (\ y -> (ap (\ α' → transport (τ₁ o Path S².base) α' (decode' y)) S².loop))) ∎

                STS5 : ap (λ α' → transport (τ₁ o Path S².base) α' [ id ]) S².loop ≃ ap [_] S².loop
                STS5 = ap (λ α' → transport (τ₁ o Path S².base) α' [ id ]) S².loop ≃〈 ap-by-equals (λ α' → transport-Trunc' (Path S².base) α' [ id ]) S².loop 〉 
                       id ∘ ap (λ α' → [ transport (Path S².base) α' id ]) S².loop ≃〈 ∘-unit-l _ 〉 
                       ap ([_] o (λ α' → transport (Path S².base) α' id)) S².loop ≃〈 ap-o [_] (λ α' → transport (Path S².base) α' id) S².loop 〉 
                       ap [_] (ap (λ α' → transport (Path S².base) α' id) S².loop) ≃〈 ap (λ x' → ap [_] x') (ap-by-id (\ α' -> ! (transport-Path-right α' id)) S².loop) 〉 
                       ap [_] (id ∘ S².loop)                                       ≃〈 ap (ap [_]) (∘-unit-l S².loop) 〉 
                       ap [_] S².loop ∎ 
-}

  decode-encode : {x : S²} (α : τ₁(Path S².base x)) → decode{x} (encode{x} α) ≃ α
  decode-encode{x} tα = Trunc-elim (\ α → decode{x} (encode{x} α) ≃ α)
                                   istrunc 
                                   (untrunc {x}) 
                                   tα where
    untrunc : {x : S²} (α : (Path S².base x)) → decode{x} (encode{x} [ α ]) ≃ [ α ]
    untrunc id = id

    istrunc : (α : τ₁(Path S².base x)) → HGpd (Path{τ₁ _} (decode{x} (encode{x} α)) α)
    istrunc α = increment-IsTrunc {S (S -2)}{_} istrunc1 where
      istrunc1 : HSet (Path{τ₁ _} (decode{x} (encode{x} α)) α)
      istrunc1 = Trunc-is {S (S (S -2))} (decode {x} (encode {x} α)) α

  τ₁Ω[S²]-is-S¹ : Path (τ₁ (Path{S²} S².base S².base)) S¹
  τ₁Ω[S²]-is-S¹ = ua (improve (hequiv encode decode' decode-encode encode-decode'))

  π2S²-is-Z : Path (τ₀ (Path{Path{S²} S².base S².base} id id)) Int
  π2S²-is-Z = (τ₀ (Path{Path{S²} S².base S².base} id id)) ≃〈 ua (improve (hequiv TruncPath.decode' TruncPath.encode' (λ _ → ap≃ TruncPath.encode-decode') (λ _ → ap≃ TruncPath.decode-encode'))) 〉 
              Path{τ₁ (Path{S²} S².base S².base)} [ id ] [ id ] ≃〈 {!encode' [ id ]!} 〉
              Path{S¹} S¹.base S¹.base ≃〈 ua (improve homotopy.Pi1S1.Ω₁[S¹]-is-Int) 〉 
              Int ∎