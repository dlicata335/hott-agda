{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open import lib.cubical.Cubical

module homotopy.scraps.TS1S1-universal where

  module _ {A B : Type}
           (f : B → A)
           (e : (X : Type) → (A → X) == (B → X))
           (pc : {X : Type} (g : A → X) → coe (e _) g == g o f)
           where

    finv : A → B
    finv = coe (! (e B)) (λ x → x)

    f-as-coe : f == (coe (e A) (\ x -> x))
    f-as-coe = ! (pc (λ x → x))

    comp2 : finv o f == (\ x -> x)
    comp2 = ! (pc finv) · IsEquiv.β (snd (coe-equiv (e B))) (λ x → x)

    pc' : {X : Type} (g : B → X) → coe (! (e _)) g == g o finv
    pc' g = ap (coe (! (e _))) STS · IsEquiv.α (snd (coe-equiv (e _))) _ where
      STS : g == coe (e _) (g o finv)
      STS = λ≃ (λ x → ! (ap g (ap≃ comp2))) · ! (pc (g o finv))

    comp1 : f o finv == (\ x -> x)
    comp1 = ! (pc' f) · ap (coe (! (e A))) f-as-coe · IsEquiv.α (snd (coe-equiv (e _))) (λ x → x)

    iseq : IsEquiv f
    iseq = snd (improve (hequiv f finv (λ x → ap≃ comp2) (λ _ → ap≃ comp1)))

{-
  open S¹ using (S¹ ; S¹-rec ; S¹-elim)
  module T = Torus
  open T using (T ; T-rec ; T-elim)

  rearrange : ∀ {A : Type} (x : A) (p : Path x x) (q : Path x x)
           → (Path (transport (λ x → Path x x) q p) p) ≃ Path (p ∘ q) (q ∘ p)
  rearrange x p q = transport (λ x' → Path x' x') q p ≃ p ≃〈 ap (BackPath _) (transport-Path (λ x' → x') (λ x' → x') q p) 〉 
                    ap (\ x -> x) q ∘ p ∘ ! (ap (\ x -> x) q) ≃ p ≃〈 ap (BackPath _) (ap (λ x' → x' ∘ p ∘ ! x') (ap-id q)) 〉 
                    q ∘ p ∘ ! q ≃ p ≃〈 ap (BackPath _) (∘-assoc q p (! q)) 〉 
                    (q ∘ p) ∘ ! q ≃ p ≃〈 move-right-right-!≃ (q ∘ p) q p 〉 
                    q ∘ p ≃ p ∘ q ≃〈 flip≃ 〉 
                    p ∘ q ≃ q ∘ p ∎

  map-out : {X : Type} -> (S¹ × S¹ -> X) ≃ (T -> X)
  map-out {X} = 
    ((S¹ × S¹ → X)                                         ≃〈 (uncurry≃ S¹ (\ _ -> S¹) (\ _ -> X)) 〉 
    (S¹ -> (S¹ -> X))                                      ≃〈 ap (λ t → S¹ → t) S¹.ump 〉
    (S¹ -> Σ[ x ∶ X ] (Path x x))                           ≃〈 S¹.ump 〉
    (Σ[ p ∶ (Σ[ x ∶ X ] (Path x x)) ] (Path p p))           ≃〈 Σassoc.path 〉
    (Σ[ x ∶ X ] (Σ[ p ∶ Path x x ] (Path (x , p) (x , p)))) ≃〈 apΣ' id-equiv (λ x → apΣ' id-equiv (λ p → ! ΣPath.path)) 〉
    (Σ[ x ∶ X ] (Σ[ p ∶ Path x x ] (Σ[ q ∶ Path x x ] (Path (transport (λ x → Path x x) q p) p)))) ≃〈 apΣ' id-equiv (λ x → apΣ' id-equiv (λ p → apΣ' id-equiv (λ q → rearrange x p q))) 〉 
    (Σ[ x ∶ X ] (Σ[ p ∶ Path x x ] (Σ[ q ∶ Path x x ] Path (p ∘ q) (q ∘ p)))) ≃〈 ua (_ , T.ump) 〉
    (T → X) ∎)   

  t2c : T -> S¹ × S¹
  t2c = T-rec (S¹.base , S¹.base) (pair×≃ id S¹.loop) (pair×≃ S¹.loop id) {!!}

  map-out-posto : ∀ {X} (f : S¹ × S¹ -> X) -> coe map-out f ≃ f o t2c
  map-out-posto {X} f = {!!} where
    fact1 : coe (uncurry≃ S¹ (\ _ -> S¹) (\ _ -> X)) f ≃ (λ x y → f (x , y))
    fact1 = ap≃ (type≃β _)

    term2 = (λ x → f (x , S¹.base) , ap (λ y → f (x , y)) S¹.loop)
    fact2 : coe (ap (λ t → S¹ → t) S¹.ump) (λ x y → f (x , y)) ≃ term2
    fact2 = coe (ap (λ t → S¹ → t) S¹.ump) (λ x y → f (x , y)) ≃〈 ! (ap≃ (transport-ap-assoc (λ t → S¹ → t) S¹.ump)) 〉
            transport (\ x -> S¹ -> x) S¹.ump (λ x y → f (x , y)) ≃〈 transport-→-post S¹.ump (λ x y → f (x , y)) 〉
            (\ x -> coe S¹.ump (λ y → f (x , y))) ≃〈 λ≃ (λ x → ap≃ (type≃β S¹.ump-eqv)) 〉
            (λ x → f (x , S¹.base) , ap (λ y → f (x , y)) S¹.loop) ∎

    term3 = (f (S¹.base , S¹.base) , ap (λ y → f (S¹.base , y)) S¹.loop) ,
            ap term2 S¹.loop
    fact3 : (coe S¹.ump term2) ≃ term3
    fact3 = ap≃ (type≃β S¹.ump-eqv)

    term4 = f (S¹.base , S¹.base) , (ap (λ y → f (S¹.base , y)) S¹.loop) , ap term2 S¹.loop
    fact4 : coe Σassoc.path term3 ≃ term4
    fact4 = ap≃ (type≃β Σassoc.eqv){term3}

    term5 = f (S¹.base , S¹.base) , (ap (λ y → f (S¹.base , y)) S¹.loop) , fst≃ (ap term2 S¹.loop) , snd≃ (ap term2 S¹.loop)
    fact5 : coe (apΣ' id-equiv (λ x → apΣ' id-equiv (λ p → ! ΣPath.path))) term4 ≃ term5
    fact5 = {!!}

    term6 = f (S¹.base , S¹.base) , 
            (ap (λ y → f (S¹.base , y)) S¹.loop) , 
            fst≃ (ap term2 S¹.loop) ,
            coe (rearrange _ (ap (λ y → f (S¹.base , y)) S¹.loop) (fst≃ (ap term2 S¹.loop))) (snd≃ (ap term2 S¹.loop))
    fact6 : coe (apΣ' id-equiv (λ x → apΣ' id-equiv (λ p → apΣ' id-equiv (λ q → rearrange x p q)))) term5 ≃ term6
    fact6 = {!!}

    LHS-reduced = T-rec (f (S¹.base , S¹.base))
                        (ap (λ y → f (S¹.base , y)) S¹.loop)
                        (ap (λ x → f (x , S¹.base)) S¹.loop)
                        {!coe (rearrange _ (ap (λ y → f (S¹.base , y)) S¹.loop) (fst≃ (ap term2 S¹.loop))) (snd≃ (ap term2 S¹.loop))!}
    fact7 : coe (ua (_ , T.ump)) term6 ≃ LHS-reduced
    fact7 = {!!} ∘ ap≃ (type≃β (_ , T.ump)) {term6}

    RHS-reduced : f o t2c ≃ T-rec (f (S¹.base , S¹.base)) (ap f (pair×≃ id S¹.loop))
                              (ap f (pair×≃ S¹.loop id)) {!!}
    RHS-reduced = {!T.Tη {_}{f} !}

  theorem : IsEquiv{T} {(S¹ × S¹)} t2c
  theorem = {!transport IsEquiv ? (coe-is-equiv (map-out{S¹ × S¹}))!} 
          fact1 : (S¹ × S¹ -> S¹ × S¹) ≃ (T -> S¹ × S¹)
          fact1 = 

          fact2 : IsEquiv{S¹ × S¹}{S¹ × S¹} (\ x -> x)
          fact2 = snd id-equiv
-}
