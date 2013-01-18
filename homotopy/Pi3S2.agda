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
                                       ((ap (ap (ap [_]2)) hopf-cell) ∘ βred)))
    where
     postulate
       βred : Path{Path {Path {τ₂ S²} [ S².base ] [ S².base ]} id id}
            (transport (λ y → Path{Path {τ₂ S²} [ S².base ] [ S².base ]} (transport{S²} (λ x → [ x ]2 ≃ [ x ]2) y (ap [_]2 id)) (ap [_] (id{_}{S².base})))
                       S².loop 
                       id) 
            id
{-
     βred = transport
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

           id ∎
-}

  P = τ₂ o Path S².base

  encode1 : {x : S²} -> Path{S²} S².base x -> B x
  encode1 {x} α = transport B α [ S².base ]

  encode1' : Path{S²} S².base S².base -> τ₂ S²
  encode1' = encode1{S².base}

  B-is-2-truncated : (x : S²) -> IsTrunc (tl 2) (B x)
  B-is-2-truncated = S²-elim (λ x → IsTrunc (tl 2) (B x)) Trunc-is (fst (use-trunc (use-trunc (use-trunc (increment-IsTrunc (IsTrunc-is-HProp _)) _ _) _ _))) 

  encode : {x : S²} -> P x -> B x
  encode {x} = Trunc-rec (B-is-2-truncated x) encode1 

  encode' = encode{S².base}

  decode1' : S² → Path S².base S².base
  decode1' = (S²-rec id hopf-cell)

  decode' : τ₂ S² → P S².base
  decode' = Trunc-func decode1'

  id-idequiv : ∀ {A} → id{Equiv A A}{id-equiv} ≃ loop-family->id-equiv-loop (λ x → id)
  id-idequiv = {!!}


  loop2-as-fn-path : Path {Path {τ₂ S² → τ₂ S²} (Trunc-func (λ x → x)) (Trunc-func (λ x → x))}
                          (λ≃ (λ x → id))
                          (λ≃ (λ x → id))
  loop2-as-fn-path = ap λ≃ (λ≃ (Trunc-elim (λ x → id ≃ id) 
                               (λ x → IsTrunc-Path _ (IsTrunc-Path _ Trunc-is _ _) _ _)
                               (S²-elim (λ _ → id ≃ id) 
                                        (ap (ap [_]2) S².loop)
                                        (fst (use-trunc (use-trunc (use-trunc (use-trunc (use-trunc (Trunc-is {tl 2} {S²}) _ _) _ _) _ _) _ _))))))


  loop2-as-equiv : Path{Path {Path{Type} (τ₂ S²) (τ₂ S²)} id id} id id
  loop2-as-equiv = wrap loop2-as-fn-path where
   postulate 
    wrap : Path {Path {τ₂ S² → τ₂ S²} (Trunc-func (λ x → x)) (Trunc-func (λ x → x))}
               (λ≃ (λ x → id))
               (λ≃ (λ x → id))
           -> Path{Path {Path{Type} (τ₂ S²) (τ₂ S²)} id id} id id
    
  {-
    step1 : Equiv (Path{Type} (τ₂ S²) (τ₂ S²)) (Equiv (τ₂ S²) (τ₂ S²))
    step1 = (_ , univalence)

    step2 : Equiv (Path {Path{Type} (τ₂ S²) (τ₂ S²)} id id)
                  (Path {(Equiv (τ₂ S²) (τ₂ S²))} id-equiv id-equiv)
    step2 = {!!}

    step2a : Equiv (Path {Path{Type} (τ₂ S²) (τ₂ S²)} id id)
                   (Path {(τ₂ S²) → (τ₂ S²)} (\ x -> x) (\ x -> x))
    step2a = {!!}

    step3 : Equiv (Path {Path {Path{Type} (τ₂ S²) (τ₂ S²)} id id} id id)
                  (Path {(Path {(τ₂ S²) → (τ₂ S²)} (\ x -> x) (\ x -> x))} id id)
    step3 = {!!}

    step4 : Equiv (Path {Path {Path{Type} (τ₂ S²) (τ₂ S²)} id id} id id)
                  (Path {Path {τ₂ S² → τ₂ S²} (λ x → x) (λ x → x)} (λ≃ (λ _ → id)) (λ≃ (λ _ → id)))
    step4 = {!!}
  -}


  transport-B-hopf : (ap (ap encode1') hopf-cell) ≃ (ap (ap [_]2) S².loop)
  transport-B-hopf = 
    (ap (ap encode1') hopf-cell) ≃〈 id 〉 
    (ap (ap (\ α → transport B α [ S².base ])) hopf-cell) ≃〈 {!!} 〉 
    (ap (ap ((\ α → coe α [ S².base ]) o ap B)) hopf-cell) ≃〈 {!!} 〉 
    (ap (  ap (\ α → coe α [ S².base ]) 
         o ap (ap B)) hopf-cell) ≃〈 ap-o (ap (λ α → coe α [ S².base ])) (ap (ap B)) hopf-cell 〉 
    ap (ap (λ α → coe α [ S².base ])) (ap (ap (ap B)) hopf-cell) ≃〈 {!!} 〉 
    ap (ap (λ α → coe α [ S².base ])) loop2-as-equiv ≃〈 {!!} 〉 
    -- some sort of beta-reduction, like that in pi2(s2) but one level up
    ap (ap [_]2) S².loop ∎
    where 
      STS : Path{Path{Path {Path{Type} (τ₂ S²) (τ₂ S²)} id id} id id}
                (ap (ap (ap B)) hopf-cell)
                loop2-as-equiv
      STS = (ap (ap (ap B)) hopf-cell) ≃〈 {!!} 〉 
            {!!} ∎

{-  
  encode-decode' : (x : τ₂ S²) -> encode' (decode' x) ≃ x
  encode-decode' = Trunc-elim (λ z → Path (encode' (decode' z)) z)
                              (λ x → IsTrunc-Path (Trunc (tl 2) S²) Trunc-is (encode' (decode' x)) x) 
                              (S²-elim (λ z → Path (encode' (decode' [ z ])) [ z ]) 
                                       id 
                                       (transport
                                          (λ y →
                                             Path (transport (λ z → Path (encode' (decode' [ z ])) [ z ]) y id)
                                             id)
                                          S².loop id ≃〈 {!!} 〉 

                                          ap (\ _ -> id) S².loop
                                        ∘ id 
                                        ∘ (! (ap (\ y -> (transport (λ z → Path (encode' (decode' [ z ])) [ z ]) y id)) S².loop)) ≃〈 {!!} 〉 

                                        (! (ap (\ y -> (transport (λ z → Path (encode' (decode' [ z ])) [ z ]) y id)) S².loop)) ≃〈 {!!} 〉 
                                          
                                        id ∎)) where

    STS : (ap (\ y -> (transport (λ z → Path (encode' (decode' [ z ])) [ z ]) y id)) S².loop) ≃ id
    STS = (ap (\ y -> (transport (λ z → Path (encode' (decode' [ z ])) [ z ]) y id)) S².loop) ≃〈 {!!} 〉
          (ap (\ y -> (ap [_]2 y ∘ ! (ap (\ z -> encode' (decode' [ z ])) y))) S².loop) ≃〈 id 〉
          (ap (\ y -> (ap [_]2 y ∘ ! (ap (\ z -> encode1' (decode1'  z)) y))) S².loop) ≃〈 {!!} 〉
          (ap∘ (ap (ap [_]2) S².loop)
               (ap (\ y -> ! (ap (\ z -> encode1' (decode1'  z)) y)) S².loop)) ≃〈 {!!} 〉
          (ap∘ (ap (ap [_]2) S².loop)
               (ap ! (ap (\ y -> (ap (\ z -> encode1' (decode1'  z)) y)) S².loop))) ≃〈 {!!} 〉
          id where
        STS2 : (ap (ap (encode1' o decode1')) S².loop) ≃ (ap (ap [_]2) S².loop)
        STS2 = (ap (ap (encode1' o decode1')) S².loop) ≃〈 {!!} 〉 
               (ap (ap (\ z -> encode1' (decode1' z))) S².loop) ≃〈 {!!} 〉 
               (ap (\ y -> ap≃₁→ (ap (\ _ -> encode1') y)
                                 (ap decode1' y)) S².loop) ≃〈 {!!} 〉 
               (ap (\ y -> ap≃₁→ (id{_}{encode1'})
                                 (ap decode1' y)) S².loop) ≃〈 {!!} 〉 
               (ap (\ y -> ap≃₁→ (id{_}{encode1'})
                                 (ap decode1' y)) S².loop) ≃〈 {!!} 〉 
               (ap (ap≃₁→ (id{_}{encode1'}) o (ap decode1')) S².loop)    ≃〈 {!!} 〉 
               (ap (ap≃₁→ (id{_}{encode1'})) (ap (ap decode1') S².loop)) ≃〈 {!!} 〉 
               (ap (ap≃₁→ (id{_}{encode1'})) hopf-cell) ≃〈 {!!} 〉 
               (ap (\ y -> ap2 (\ f x -> f x) (id{_}{encode1'}) y) hopf-cell) ≃〈 {!!} 〉 
               (ap (ap encode1') hopf-cell) ≃〈 {!!} 〉 
               (ap (ap [_]2) S².loop) ∎

-}