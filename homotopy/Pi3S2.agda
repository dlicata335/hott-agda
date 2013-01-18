{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open import homotopy.Hopf
open Paths
open Truncation

module homotopy.Pi3S2 where

  private 
    module S² = S²1
  open S² using (S² ; S²-rec ; S²-elim)
  open S¹ using (S¹ ; S¹-rec ; S¹-elim)

  [_]2 : {A : _} → (x : A) -> Trunc (S (S (S (S -2)))) A
  [ x ]2 = [ x ]

  B : S² → Type
  B = S²-fibration (τ₂ S²) 
                   (Trunc-elim (λ x → x ≃ x) 
                              (λ x → IsTrunc-Path (Trunc (S (S (S (S -2)))) S²) Trunc-is x x)
                              (S²-elim (λ x → [ x ] ≃ [ x ]) 
                                       (ap [_] (id{_}{S².base})) 
                                       foo))
    where
     foo : Path{Path {Path {τ₂ S²} [ S².base ] [ S².base ]} id id}
           (transport (λ y → Path{Path {τ₂ S²} [ S².base ] [ S².base ]} (transport{S²} (λ x → [ x ]2 ≃ [ x ]2) y (ap [_]2 id)) (ap [_] (id{_}{S².base})))
                      S².loop 
                      id) 
           id
     foo = transport
             (λ y →
                Path {Path {τ₂ S²} [ S².base ] [ S².base ]}
                (transport {S²} (λ x → [ x ]2 ≃ [ x ]2) y (ap [_]2 id))
                (ap [_] (id {_} {S².base})))
             S².loop id   ≃〈 {!!} 〉 

           ap (\ _ -> ap [_] (id {_} {S².base})) S².loop 
           ∘ id 
           ∘ ! (ap (\ y -> (transport {S²} (λ x → [ x ]2 ≃ [ x ]2) y (ap [_]2 id))) S².loop) ≃〈 {!!} 〉 

           id {_}{ap [_] (id {_} {S².base})}
           ∘ id 
           ∘ ! (ap (\ y -> (transport {S²} (λ x → [ x ]2 ≃ [ x ]2) y (ap [_]2 id))) S².loop) ≃〈 {!!} 〉 

           id {_}{ap [_] (id {_} {S².base})}
           ∘ ! (ap (\ y -> (transport {S²} (λ x → [ x ]2 ≃ [ x ]2) y (ap [_]2 id))) S².loop) ≃〈 {!!} 〉 

           ! (ap (\ y -> (transport {S²} (λ x → [ x ]2 ≃ [ x ]2) y (ap [_]2 id))) S².loop) ≃〈 {!!} 〉 

           ! (ap (\ y -> (ap [_]2 y ∘ ap [_]2 id ∘ (! (ap [_]2 y)))) S².loop) ≃〈 {!!} 〉 

           ! (ap (\ y -> (ap [_]2 (y ∘ id ∘ ! y))) S².loop) ≃〈 {!!} 〉 

           ! (ap (\ y -> id) S².loop) ≃〈 {!!} 〉 

           id ≃〈 ap (ap (ap [_]2)) Encode.nontriv 〉 

           id ∎

  P = τ₂ o Path S².base

  encode1 : {x : S²} -> Path{S²} S².base x -> B x
  encode1 {x} α = transport B α [ S².base ]

  encode1' : Path{S²} S².base S².base -> τ₂ S²
  encode1' = encode1{S².base}

  B-is-2-truncated : (x : S²) -> IsTrunc (S (S (S (S -2)))) (B x)
  B-is-2-truncated = S²-elim (λ x → IsTrunc (S (S (S (S -2)))) (B x)) Trunc-is (fst (use-trunc (use-trunc (use-trunc (increment-IsTrunc (IsTrunc-is-HProp _)) _ _) _ _))) 

  encode : {x : S²} -> P x -> B x
  encode {x} = Trunc-rec (B-is-2-truncated x) encode1 

  encode' = encode{S².base}

  decode' : τ₂ S² → P S².base
  decode' = Trunc-func (S²-rec id Encode.nontriv)

  