{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open import lib.cubical.Cubical

module homotopy.TS1S1 where

  open S¹ using (S¹ ; S¹-rec ; S¹-elimo)
  module T = Torus
  open T using (T ; T-rec ; T-elim)

  -- FIXME move to lib

{-
  ap-uncurry' : {A B C : Type} → (f : A → B → C) {a1 a2 : A} (p1 : a1 == a2) {b1 b2 : B} (p2 : b1 == b2)
             → ap (\ {(x , y) → (f x) y}) (pair×≃ p1 p2) == ap≃₁→ (ap f p1) p2
  ap-uncurry' f id id = id

  ap≃₁→-id-fn : {A B : Type} (f : A → B) {x y : A} → (p : x ≃ y) → (ap≃₁→ id p) == ap f p
  ap≃₁→-id-fn f id = id

  ap≃₁→-id-arg : {A B : Type} {f g : A → B} {x : A} → (p : f ≃ g) → (ap≃₁→ p (id{_}{x})) == ap≃ p
  ap≃₁→-id-arg id = id
-}

  -- FIXME bug with unification? look at the constraints
  -- NAMETHATDOESNTOCCURANYWHEREELSE : {!Nat!}
  -- NAMETHATDOESNTOCCURANYWHEREELSE = {!Z!}

  -- FIXME: bug with unification on the following ?
  -- too many things are solved to id
  -- BUG2 = S¹-rec (S¹-rec T.a T.p) (λ≃ (S¹-elimo _ T.q 
  --               (PathOver=.in-PathOver-= ((∘-square-vertical (vertical-degen-square (S¹.βloop/rec T.a T.p)) {!!})))))

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

  reduce-c2t-1 : ap c2t (pair×≃ (id{_}{S¹.base}) S¹.loop) == T.p
  reduce-c2t-1 = S¹.βloop/rec T.a T.p ∘ ap-bifunctor-id-1 c2t' S¹.loop 

  reduce-c2t-2'' : (y : S¹) → ap (λ x → c2t' x y) S¹.loop == c2t-loop-homotopy y
  reduce-c2t-2'' y = {!!}

  reduce-c2t-2' : ap (λ x → c2t' x S¹.base) S¹.loop == T.q
  reduce-c2t-2' = reduce-c2t-2'' S¹.base

  reduce-c2t-2 : ap c2t (pair×≃ S¹.loop (id{_}{S¹.base})) == T.q
  reduce-c2t-2 = reduce-c2t-2' ∘ ap-bifunctor-id-2 c2t' S¹.loop 

  reduction1 : ap (λ z → c2t (t2c z)) T.p == ap (λ z → z) T.p
  reduction1 = ! (ap-id T.p) ∘ 
               (reduce-c2t-1 ∘ 
                (ap (ap c2t) (T.βp/rec (S¹.base , S¹.base) (pair×≃ id S¹.loop) (pair×≃ S¹.loop id) (pair-square vrefl-square hrefl-square)) ∘ 
                 ap-o c2t t2c T.p))

  reduction2 : ap (λ z → c2t (t2c z)) T.q == ap (λ z → z) T.q
  reduction2 = ! (ap-id T.q) ∘ 
               reduce-c2t-2 ∘ 
               ap (ap c2t) (T.βq/rec (S¹.base , S¹.base) (pair×≃ id S¹.loop) (pair×≃ S¹.loop id) (pair-square vrefl-square hrefl-square)) ∘ 
               ap-o c2t t2c T.q

  t2c2t : (x : T) → c2t (t2c x) == x
  t2c2t = T-elim (\ x -> c2t (t2c x) == x) 
                 id 
                 (PathOver=.in-PathOver-= (vertical-degen-square reduction1))
                 (PathOver=.in-PathOver-= (vertical-degen-square reduction2))
                 (SquareOver=ND.in-SquareOver-= 
                   {!cube-symmetry-left-to-top goal1!}) where
        goal1 : Cube (ap-square (λ z → c2t (t2c z)) T.f)
                     (ap-square (λ z → z) T.f)
                     (horiz-degen-square reduction1)
                     (horiz-degen-square reduction2)
                     (horiz-degen-square reduction2)
                     (horiz-degen-square reduction1)
        goal1 = ∘-cube-horiz/degen (∘-cube-horiz/degen
                                      (∘-cube-horiz/degen (ap-square-o c2t t2c T.f)
                                                          goal2)
                                      {!!})
                                   (ap-square-id! T.f) where 

              goal2 : let a' = (S¹.base , S¹.base)
                          p' = (pair×≃ id S¹.loop)
                          q' = (pair×≃ S¹.loop id)
                          f' = (pair-square vrefl-square hrefl-square)
                      in 
                      Cube (ap-square c2t (ap-square (T-rec a' p' q' f') T.f))
                           (ap-square c2t f')
                           (horiz-degen-square (ap (ap c2t) (T.βp/rec a' p' q' f')))
                           (horiz-degen-square (ap (ap c2t) (T.βq/rec a' p' q' f')))
                           (horiz-degen-square (ap (ap c2t) (T.βq/rec a' p' q' f')))
                           (horiz-degen-square (ap (ap c2t) (T.βp/rec a' p' q' f')))
              goal2 = let a' = (S¹.base , S¹.base)
                          p' = (pair×≃ id S¹.loop)
                          q' = (pair×≃ S¹.loop id)
                          f' = (pair-square vrefl-square hrefl-square)
                      in 
                      coe (ap (λ x → Cube (ap-square c2t (ap-square (T-rec a' p' q' f') T.f)) (ap-square c2t f') 
                                          (horiz-degen-square (ap (ap c2t) (T.βp/rec a' p' q' f'))) x x (horiz-degen-square (ap (ap c2t) (T.βp/rec a' p' q' f'))))
                              (ap-square-horiz-degen c2t (T.βq/rec a' p' q' f')))
                          (coe (ap (λ x → Cube
                                          (ap-square c2t (ap-square (T-rec a' p' q' f') T.f))
                                          (ap-square c2t f')
                                          x
                                          (ap-square c2t (horiz-degen-square (T.βq/rec a' p' q' f')))
                                          (ap-square c2t (horiz-degen-square (T.βq/rec a' p' q' f')))
                                          x)
                                       (ap-square-horiz-degen c2t (T.βp/rec a' p' q' f')))
                        (ap-cube c2t
                         (T.βf/rec (S¹.base , S¹.base) (pair×≃ id S¹.loop)
                          (pair×≃ S¹.loop id) (pair-square vrefl-square hrefl-square))))

              goal3 : Cube (ap-square c2t (pair-square vrefl-square hrefl-square))
                           T.f
                           (horiz-degen-square reduce-c2t-1)
                           (horiz-degen-square reduce-c2t-2)
                           (horiz-degen-square reduce-c2t-2)
                           (horiz-degen-square reduce-c2t-1)
              goal3 = ∘-cube-horiz/degen (bifunctor-cube1 c2t' S¹.loop S¹.loop)
                                        {! SquareOver=ND.out-SquareOver-= (apdo-by-equals (λ y → ap (λ x → c2t' x y) S¹.loop) _ S¹.loop (λ≃ reduce-c2t-2''))  !} 


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
    square1'' = _
    square2'' = _

    cube5 : Cube (ap-square c2t (pair-square hrefl-square vrefl-square)) (square-symmetry T.f) square2'' square1'' square1'' square2''
    cube5 = bifunctor-cube1' c2t' S¹.loop S¹.loop ∘-cube-h 
            SquareOver=ND.out-SquareOver-= (apdo-by-equals _ _ S¹.loop (λ≃ reduce-c2t-2'')) ∘-cube-h
            degen-cube-h (ap PathOver=.out-PathOver-= (S¹.βloop/elimo _ T.q (PathOver=.in-PathOver-= (∘-square-vertical/degen-top (vertical-degen-square (S¹.βloop/rec T.a T.p)) (∘-square-vertical/degen-bot (square-symmetry T.f) (vertical-degen-square (! (S¹.βloop/rec T.a T.p)))))))) ∘-cube-h
            degen-cube-h (IsEquiv.β (snd PathOver=.out-PathOver-=-eqv) _)
              ∘-cube-h (wrap-around (S¹.βloop/rec T.a T.p) (square-symmetry T.f) (S¹.βloop/rec T.a T.p))

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
            ap-cube t2c cube5 ∘-cube-h
            degen-cube-h (ap-square-symmetry t2c T.f) ∘-cube-h
            cube-square-symmetry-left (T.βf/rec (S¹.base , S¹.base) (pair×≃ id S¹.loop) (pair×≃ S¹.loop id) (pair-square vrefl-square hrefl-square)) ∘-cube-h 
            degen-cube-h (pair-vrefl-hrefl-symmetry S¹.loop S¹.loop) ∘-cube-h
            (ap-square-id! (pair-square hrefl-square vrefl-square)) ∘-cube-h
            (bifunctor-cube1' _,_ S¹.loop S¹.loop)

    square1 : Square id (ap (λ z → t2c (c2t' S¹.base z)) S¹.loop) (ap (λ z → S¹.base , z) S¹.loop) id
    square1 = _

    square2 : Square id (ap (λ z → t2c (c2t' z S¹.base)) S¹.loop) (ap (λ z → z , S¹.base) S¹.loop) id
    square2 = _

    cube3 : Cube
            square2
            square2
            square1 
            (PathOver=.out-PathOver-=
             (apdo (λ x₁ → ap (λ z → t2c (c2t' z x₁)) S¹.loop) S¹.loop))
            (PathOver=.out-PathOver-=
              (apdo (λ x₁ → ap (λ z → z , x₁) S¹.loop) S¹.loop))
            square1 
    cube3 = cube-symmetry-left-to-top cube4

