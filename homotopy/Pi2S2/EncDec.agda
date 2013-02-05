{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open import homotopy.Hopf
import homotopy.Pi1S1
import homotopy.Pi2S2.Retract

open Int

module homotopy.Pi2S2.EncDec where

  open Truncation
  module R = homotopy.Pi2S2.Retract

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
  
  decode : {x : S²} -> H x → τ₁ (Path{S²} S².base x)
  decode{x} = S²-elim (λ x' → H x' → τ₁ (Path {S²} S².base x')) 
                      decode' 
                      respects-loop
                      x
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
                               ≃ id{_}{decode' x}
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
                             (fst (use-level (use-level (use-level (use-level (Trunc-level {S (S (S -2))} {Path S².base S².base}) _ _) _ _) _ _)))
               where 
                STS3 : (ap (λ β → transport H (! β) S¹.base) S².loop) ≃ ! S¹.loop
                STS3 = (ap (λ β → transport H (! β) S¹.base) S².loop)    ≃〈 ap-o (λ z → transport H z S¹.base) ! S².loop 〉 
                       (ap (λ β → transport H β S¹.base) (ap ! S².loop)) ≃〈 ap (λ y → ap (λ β → transport H β S¹.base) y) (! (HigherHomotopyAbelian.inverse-same S² S².base S².loop)) 〉 
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

  
