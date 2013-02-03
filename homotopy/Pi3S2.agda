{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open import homotopy.Hopf
open Paths
open Truncation
open Int
open LoopSpace

module homotopy.Pi3S2 where

  module S = NSphere1
  open S using (S^ ; S-rec; S-elim)

  Two : Positive
  Two = S One

  Three : Positive
  Three = S Two

  TTwo : TLevel
  TTwo = S (S (S (S -2)))

  S² = S^ Two
  S²-elim = S-elim {Two}
  S²-rec  = \ {A} -> S-rec{Two}{A}
  base = S.base{Two}
  loop = S.loop Two

  [_]2 : {A : _} → (x : A) -> Trunc (S (S (S (S -2)))) A
  [ x ]2 = [ x ]

  module A = HigherHomotopyAbelian S² base

  {-
  ap∘-!-inv-l : {A : Type} {x : A} 
              -> (α : Path (id{_}{x}) id)
              → ap∘ (! α) α ≃ id
  ap∘-!-inv-l α = !-inv-l α ∘ ! (HigherHomotopyAbelian.same _ _ (! α) α)
  -}

  ap∘-! : {A : Type} {x y z : A} {p q : Path x y} {p' q' : Path y z} 
       -> (α : Path p' q') -> (β : Path p q)
       → ap∘ (! α) (! β) ≃ ! (ap∘ α β)
  ap∘-! id id = id

  hopf-cell-a1 : ∀ {A} {a} -> (α : Loop Two A a) → id ≃ ap∘ (α ∘ ! α) (α ∘ ! α)
  hopf-cell-a1 α = ! (ap2 ap∘ (!-inv-r α) (!-inv-r α))

  hopf-cell-a2 : ∀ {A} {a} -> (α : Loop Two A a) → ap∘ α α ∘ ap∘ (! α) (! α) ≃ id
  hopf-cell-a2 α = !-inv-r (ap∘ α α) ∘ ap (λ x → ap∘ α α ∘ x) (ap∘-! α α)

  hopf-cell : ∀ {A} {a} -> Loop Two A a → Loop Three A a 
  hopf-cell α = hopf-cell-a2 α ∘ 
                ichange-type (! α) α (! α) α ∘ -- could also do ichange-type id α (! α) id ∘ 
                hopf-cell-a1 α

  Bloop : Loop Two Type (τ₂ S²)
  Bloop = λt One (λ a → 
        Trunc-elim (λ x → x ≃ x) (λ x → path-preserves-IsTrunc Trunc-is)
          (S²-elim (λ x → [ x ] ≃ [ x ]) 
                   (ap [_] (id {_} {base}))
                   -- what follows is an hprop, so this doesn't matter...
                   (coe  (! (LoopOverS≃ One loop (λ x → [ x ]2 ≃ [ x ]2) (ap [_] (id {_} {base})))) 
                     (apt One (ap^ (S One) (λ x → [ x ]2 ≃ [ x ]2) loop) (ap [_] id) ≃〈 apt-apS One (λ x → [ x ]2 ≃ [ x ]2) loop (ap [_] id) 〉 
                     (ap (\ y -> transport (\ x -> [ x ]2 ≃ [ x ]2) y id) loop) ≃〈 ap-by-equals {f = λ y → transport (λ x → [ x ]2 ≃ [ x ]2) y id} {g = λ y → id} (λ y → !-inv-with-middle-r (ap [_]2 y) id ∘ transport-Path [_]2 [_]2 y id) loop 〉 
                     (id ∘ ap (\ y -> id) loop) ≃〈 ∘-unit-l (ap (\ y -> id) loop) 〉 
                     (ap (\ y -> id) loop)     ≃〈 ap-constant id loop 〉 
                     id ∎)))
                   a)  where

  {-
        cell1 = 

        cell2 = apt One (ap^ (S One) (λ x → [ x ]2 ≃ [ x ]2) loop) (ap [_] id) ≃〈
                apt-apS One (λ x → [ x ]2 ≃ [ x ]2) loop (ap [_] id) 〉
                ap (λ y → transport (λ x → [ x ]2 ≃ [ x ]2) y id) loop ≃〈
                ap-by-equals {f = λ y → transport (λ x → [ x ]2 ≃ [ x ]2) y id}
                {g = λ y → id}
                (λ y →
                   !-inv-with-middle-r (ap [_]2 y) id ∘ transport-Path [_]2 [_]2 y id)
                loop
                〉
                id ∘ ap (λ y → id) loop ≃〈 ∘-unit-l (ap (λ y → id) loop) 〉
                ap (λ y → id) loop ≃〈 ap-constant id loop 〉 (id ∎)

        l : foo ≃ bar
        l = fst
              (use-trunc
               (use-trunc
                (use-trunc (use-trunc (use-trunc (Trunc-is {TTwo}) _ _) _ _) _ _) _
                _))
  -}

  B : S² → Type
  B = S²-rec (τ₂ S²) Bloop

  P = τ₂ o Path{S²} base

  encode1 : {x : S²} -> Path{S²} base x -> B x
  encode1 {x} α = transport B α [ base ]

  encode1' : Path{S²} base base -> τ₂ S²
  encode1' = encode1{base}

  B-is-2-truncated : (x : S²) -> IsTrunc (tl 2) (B x)
  B-is-2-truncated = S²-elim (λ x → IsTrunc (tl 2) (B x)) Trunc-is (fst (use-trunc (use-trunc (use-trunc (increment-IsTrunc (IsTrunc-is-HProp _)) _ _) _ _))) 

  encode : {x : S²} -> P x -> B x
  encode {x} = Trunc-rec (B-is-2-truncated x) encode1 

  encode' = encode{base}

  decode1' : S² → Path base base
  decode1' = (S²-rec id (hopf-cell loop))

  decode' : τ₂ S² → P base
  decode' = Trunc-func decode1'

  red : (ap (ap encode1') (hopf-cell loop)) ≃ (ap (ap [_]) loop)
  red = ap (ap encode1') (hopf-cell loop) ≃〈 {!!} 〉 
        ap^ Two encode1' (hopf-cell loop) ≃〈 {!!} 〉 
        apt Two (ap^ Three B (hopf-cell loop)) [ base ] ≃〈 {!apt Two !} 〉 
        apt Two (hopf-cell (ap^ Two B loop)) [ base ] ≃〈 {!apt Two !} 〉 
        apt Two (hopf-cell Bloop) [ base ] ≃〈 {!apt Two !} 〉 
        ap (ap [_]) loop ∎ where
      lemma : ap (ap (ap B)) (hopf-cell loop) ≃ hopf-cell (ap (ap B) loop)
      lemma = {!hopf-cell-a1 loop!}

      commute :  {A : Type} {x y z : A} {B : Type} {f : A → B}
                 {p q r : Path x y} {p' q' r' : Path y z}
               -> (a : Path p q) (b : Path q r) (c : Path p' q') (d : Path q' r') 
               -> ap (ap (ap f)) (ichange-type a b c d) ≃ {! ichange-type (ap (ap f) a) (ap (ap f) b) (ap (ap f) c) (ap (ap f) d)!}
      commute id id id id = {!!}

      lemma' : {A : Type} {pa : A}
                 {p q r : Path A A} {p' q' r' : Path A A}
               -> (a : Path p q) (b : Path q r) 
                  (c : Path p' q') (d : Path q' r') 
               ->
               ap (ap (\ x -> coe x pa)) 
                  (ichange-type a b c d) 
             ≃ {!!}
      lemma' = {!!}
      -- ap (\ x -> coe x pa) (ap∘ c a) is morally
      -- ap2 (\ x y -> coe x (coe y pa)) c a

      -- so
      -- (ap (λ x → coe x pa) (ap∘ (d ∘ c) (b ∘ a)))

      -- (ap2 (λ x y → coe x (coe y pa)) (d ∘ c) (b ∘ a)  [ should distribute over two compositions ]

      -- (ap2 (λ x y → coe x (coe y pa)) d b ∘ 
      --  ap2 (λ x y → coe x (coe y pa)) c a)

      -- (ap (λ x → coe x pa) (ap∘ d b) ∘ 
      --  ap (λ x → coe x pa) (ap∘ c a))

      -- (ap (λ x → coe x pa) (ap∘ d b ∘ ap∘ c a))


  {-
  encode-decode' : (x : τ₂ S²) -> encode' (decode' x) ≃ x
  encode-decode' = 
    Trunc-elim (λ z → Path (encode' (decode' z)) z) (λ x → path-preserves-IsTrunc Trunc-is) 
     (S²-elim (λ z → Path (encode' (decode' [ z ])) [ z ]) 
              id 
              (coe (! (LoopOverS≃ One loop (λ z → Path (encode' (decode' [ z ])) [ z ]) id))
              (apt One (ap^ (S One) (λ z → Path (encode' (decode' [ z ])) [ z ]) loop) id  ≃〈 apt-apS One (λ z → Path (encode' (decode' [ z ])) [ z ]) loop id 〉 
               ap (\y -> transport (λ z → Path (encode' (decode' [ z ])) [ z ]) y id) loop ≃〈 {!!} 〉
               id ∘ ap (\y -> ap [_] y ∘ ! (ap (λ z → (encode' (decode' [ z ]))) y)) loop   ≃〈 {!!} 〉
               ap∘ (ap (ap [_]) loop) (! (ap (ap (encode' o decode' o [_]2)) loop))             ≃〈 {!ap^ Two!} 〉
               (ap (ap [_]) loop) ∘ (! (ap (ap (encode' o decode' o [_]2)) loop))               ≃〈 id 〉
               (ap (ap [_]) loop) ∘ (! (ap (ap (encode1' o decode1')) loop))                    ≃〈 {!!} 〉
               (ap (ap [_]) loop) ∘ (! (ap (ap encode1') (ap (ap decode1') loop)))              ≃〈 {!!} 〉
               (ap (ap [_]) loop) ∘ (! (ap (ap encode1') hopf-cell))                            ≃〈 {!!} 〉
               id ∎)))
  -}




















{-
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
  {-
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
  -}    
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

{-
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
-}

