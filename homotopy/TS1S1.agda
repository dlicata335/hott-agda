{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open import lib.cubical.Cubical

module homotopy.TS1S1 where

  open S¹ using (S¹ ; S¹-rec ; S¹-elimo)
  module T = Torus
  open T using (T ; T-rec ; T-elim)

  -- FIXME bug with unification? look at the constraints
  -- NAMETHATDOESNTOCCURANYWHEREELSE : {!Nat!}
  -- NAMETHATDOESNTOCCURANYWHEREELSE = {!Z!}

  -- FIXME: bug with unification on the following ?
  -- too many things are solved to id
  -- BUG2 = S¹-rec (S¹-rec T.a T.p) (λ≃ (S¹-elimo _ T.q 
  --               (PathOver=.in-PathOver-= ((∘-square-vertical (vertical-degen-square (S¹.βloop/rec T.a T.p)) {!!})))))

  -- define the square as the filler of this?
  wrap-around :
    {A : Type}
    {a b c d : A}
    {l : a == b} 
    {t : a == c} 
    {bt : a == c} 
    {r : c == d} 
    {b' : b == d}  
    {b'' : b == d} 
    → (p : t == bt)
    → (f : Square l bt b' r)
    → (q : b'' == b')
    → Cube
      (∘-square-vertical/degen-top
       (vertical-degen-square p)
       (∘-square-vertical/degen-bot f
        (vertical-degen-square (! q))))
      f hrefl-square (horiz-degen-square p) (horiz-degen-square q) hrefl-square 
  wrap-around id id id = id

  t2c : T -> S¹ × S¹
  t2c = T-rec (S¹.base , S¹.base) (pair×≃ id S¹.loop) (pair×≃ S¹.loop id) (pair-square vrefl-square hrefl-square)

  c2t-loop-homotopy = (S¹-elimo _ T.q 
                (PathOver=.in-PathOver-= 
                  ((∘-square-vertical/degen-top
                    (vertical-degen-square (S¹.βloop/rec T.a T.p)) 
                    (∘-square-vertical/degen-bot (square-symmetry T.f)
                                                (vertical-degen-square (! (S¹.βloop/rec T.a T.p))))))))

  c2t' : S¹ → S¹ → T
  c2t' x y = S¹-rec (S¹-rec T.a T.p) (λ≃ c2t-loop-homotopy) x y 

  c2t : S¹ × S¹ → T
  c2t (x , y) = c2t' x y

  reduce-c2t-2'' : (y : S¹) → ap (λ x → c2t' x y) S¹.loop == c2t-loop-homotopy y
  reduce-c2t-2'' y = {!!}

  cube5 : Σ \ square1'' → Σ \ square2'' → Cube (bifunctor-square1 c2t' S¹.loop S¹.loop) (square-symmetry T.f) square2'' square1'' square1'' square2''
  cube5 = _ , _ , (
          SquareOver=ND.out-SquareOver-= (apdo-by-equals _ _ S¹.loop (λ≃ reduce-c2t-2'')) ∘-cube-h
          degen-cube-h (ap PathOver=.out-PathOver-= (S¹.βloop/elimo _ T.q (PathOver=.in-PathOver-= (∘-square-vertical/degen-top (vertical-degen-square (S¹.βloop/rec T.a T.p)) (∘-square-vertical/degen-bot (square-symmetry T.f) (vertical-degen-square (! (S¹.βloop/rec T.a T.p)))))))) ∘-cube-h
          degen-cube-h (IsEquiv.β (snd PathOver=.out-PathOver-=-eqv) _)
            ∘-cube-h (wrap-around (S¹.βloop/rec T.a T.p) (square-symmetry T.f) (S¹.βloop/rec T.a T.p)))

  t2c2t : (x : T) → c2t (t2c x) == x
  t2c2t = T-elim (\ x -> c2t (t2c x) == x) 
                 id 
                 (PathOver=.in-PathOver-= (square-symmetry square1))
                 (PathOver=.in-PathOver-= (square-symmetry square2))
                 (SquareOver=ND.in-SquareOver-= 
                   {!cube-symmetry-left-to-top goal1!}) where

        square1 = _
        square2 = _
        goal1 : Cube (ap-square (λ z → c2t (t2c z)) T.f)
                     (ap-square (λ z → z) T.f)
                     square1
                     square2
                     square2
                     square1
        goal1 = (ap-square-o c2t t2c T.f) ∘-cube-h
                ap-cube c2t
                  (T.βf/rec (S¹.base , S¹.base) (pair×≃ id S¹.loop)
                   (pair×≃ S¹.loop id) (pair-square vrefl-square hrefl-square)) ∘-cube-h
                bifunctor-cube1 c2t' S¹.loop S¹.loop ∘-cube-h 
                cube-square-symmetry-left (snd (snd cube5)) ∘-cube-h
                degen-cube-h (square-symmetry-symmetry T.f)  ∘-cube-h 
                ap-square-id! T.f

  c2t2c : (x y : S¹) → t2c (c2t' x y) == (x , y)
  c2t2c = S¹-elimo _ (S¹-elimo _ id (PathOver=.in-PathOver-= square1)) 
                     (coe (! PathOverΠ-NDdomain) (\ x -> PathOver=.in-PathOver-= 
                                                         (S¹-elimo
                                                            (λ x₁ → Square (S¹-elimo (λ x₂ → t2c (c2t' S¹.base x₂) == (S¹.base , x₂)) id (PathOver=.in-PathOver-= square1) x₁) (ap (λ z → t2c (c2t' z x₁)) S¹.loop) (ap (λ z → z , x₁) S¹.loop) (S¹-elimo (λ x₂ → t2c (c2t' S¹.base x₂) == (S¹.base , x₂)) id (PathOver=.in-PathOver-= square1) x₁))
                                                            square2
                                                            (coe (! (PathOver-square/= S¹.loop square2 square2)) 
                                                              (transport (λ x₁ → Cube square2 square2 x₁ (PathOver=.out-PathOver-= (apdo (λ x₂ → ap (λ z → t2c (c2t' z x₂)) S¹.loop) S¹.loop)) (PathOver=.out-PathOver-= (apdo (λ x₂ → ap (λ z → z , x₂) S¹.loop) S¹.loop)) x₁)
                                                                 (! (IsEquiv.β (snd PathOver=.out-PathOver-=-eqv) square1 ∘ ap PathOver=.out-PathOver-= (S¹.βloop/elimo _ id (PathOver=.in-PathOver-= square1))))
                                                                 cube3))
                                                          x))) where
    square1' = _
    square2' = _
    cube4 : Cube
            (PathOver=.out-PathOver-=
              (apdo (λ x₁ → ap (λ z → t2c (c2t' z x₁)) S¹.loop) S¹.loop))
            (PathOver=.out-PathOver-=
              (apdo (λ x₁ → ap (λ z → z , x₁) S¹.loop) S¹.loop))
            square1'
            square2'
            square2'
            square1'
    cube4 = !-cube-h (bifunctor-cube1' (λ x y → t2c (c2t' x y)) S¹.loop S¹.loop) ∘-cube-h
            ap-square-o t2c c2t (pair-square hrefl-square vrefl-square) ∘-cube-h
            ap-cube t2c (bifunctor-cube1' c2t' S¹.loop S¹.loop ∘-cube-h (snd (snd cube5))) ∘-cube-h
            degen-cube-h (ap-square-symmetry t2c T.f) ∘-cube-h
            cube-square-symmetry-left (T.βf/rec (S¹.base , S¹.base) (pair×≃ id S¹.loop) (pair×≃ S¹.loop id) (pair-square vrefl-square hrefl-square)) ∘-cube-h 
            degen-cube-h (pair-vrefl-hrefl-symmetry S¹.loop S¹.loop) ∘-cube-h
            (ap-square-id! (pair-square hrefl-square vrefl-square)) ∘-cube-h
            (bifunctor-cube1' _,_ S¹.loop S¹.loop)

    square1 : Square id (ap (λ z → t2c (c2t' S¹.base z)) S¹.loop) (ap (λ z → S¹.base , z) S¹.loop) id
    square1 = _

    square2 : Square id (ap (λ z → t2c (c2t' z S¹.base)) S¹.loop) (ap (λ z → z , S¹.base) S¹.loop) id
    square2 = _

    cube3 : Cube square2 square2 square1
                 (PathOver=.out-PathOver-= (apdo (λ x₁ → ap (λ z → t2c (c2t' z x₁)) S¹.loop) S¹.loop))
                 (PathOver=.out-PathOver-= (apdo (λ x₁ → ap (λ z → z , x₁) S¹.loop) S¹.loop))
                 square1 
    cube3 = (cube-symmetry-left-to-top cube4)
