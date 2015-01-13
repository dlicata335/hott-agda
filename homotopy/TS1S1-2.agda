{-# OPTIONS --type-in-type --without-K #-}
open import lib.Prelude
open import lib.cubical.Cubical

module homotopy.TS1S1-2 where

  open S¹ using (S¹ ; S¹-rec ; S¹-elimo)
  module T = Torus
  open T using (T ; T-rec ; T-elim)

  t2c : T -> S¹ × S¹
  t2c = T-rec (S¹.base , S¹.base) (pair×≃ S¹.loop id) (pair×≃ id S¹.loop) (pair-square hrefl-square vrefl-square)

  abstract
    c2t-square-and-cube : Σ \ s -> Cube s T.f 
                                        hrefl-square
                                        (horiz-degen-square (S¹.βloop/rec T.a T.q))
                                        (horiz-degen-square (S¹.βloop/rec T.a T.q))
                                        hrefl-square
    c2t-square-and-cube = (fill-cube-left T.f 
                                          hrefl-square
                                          (horiz-degen-square (S¹.βloop/rec T.a T.q)) 
                                          (horiz-degen-square (S¹.βloop/rec T.a T.q))
                                          hrefl-square)

  c2t-square : Square T.p (ap (λ z → S¹-rec T.a T.q z) S¹.loop) (ap (λ z → S¹-rec T.a T.q z) S¹.loop) T.p
  c2t-square = fst c2t-square-and-cube

  c2t-loop-homotopy = (S¹-elimo (\ x -> (S¹-rec T.a T.q) x == (S¹-rec T.a T.q) x) T.p (PathOver=.in-PathOver-= c2t-square))

  c2t' : S¹ → S¹ → T
  c2t' x y = S¹-rec (S¹-rec T.a T.q) (λ≃ c2t-loop-homotopy) x y 

  c2t : S¹ × S¹ → T
  c2t (x , y) = c2t' x y

  reduce-c2t' : (y : S¹) → ap (λ x → c2t' x y) S¹.loop == c2t-loop-homotopy y
  reduce-c2t' y = (Π≃β c2t-loop-homotopy ∘ ap (ap (λ f → f y)) (S¹.βloop/rec (S¹-rec T.a T.q) (λ≃ c2t-loop-homotopy))) ∘ ap-o (λ f → f y) c2t' S¹.loop

  c2t'-loop-loop-cube : Σ \ square1'' → Σ \ square2'' → 
        Cube (bifunctor-square1 c2t' S¹.loop S¹.loop) T.f square2'' square1'' square1'' square2''
  c2t'-loop-loop-cube = _ , _ , (
          SquareOver=ND.out-SquareOver-= (apdo-by-equals _ _ S¹.loop (λ≃ reduce-c2t')) ·-cube-h
          degen-cube-h (ap PathOver=.out-PathOver-= (S¹.βloop/elimo _ T.p (PathOver=.in-PathOver-= c2t-square))) ·-cube-h
          degen-cube-h (IsEquiv.β (snd PathOver=.out-PathOver-=-eqv) _) ·-cube-h 
          (snd c2t-square-and-cube))

  t2c2t : (x : T) → c2t (t2c x) == x
  t2c2t = T-elim (\ x -> c2t (t2c x) == x) 
                 id 
                 (PathOver=.in-PathOver-= (square-symmetry p-case))
                 (PathOver=.in-PathOver-= (square-symmetry q-case))
                 (SquareOver=ND.in-SquareOver-= 
                   (whisker-cube (! (IsEquiv.β (snd PathOver=.out-PathOver-=-eqv) _))
                                 (! (IsEquiv.β (snd PathOver=.out-PathOver-=-eqv) _))
                                 (! (IsEquiv.β (snd PathOver=.out-PathOver-=-eqv) _))
                                 id id 
                                 (! (IsEquiv.β (snd PathOver=.out-PathOver-=-eqv) _))
                                 (cube-symmetry-left-to-top f-case))) where
        p-case = _
        q-case = _
        f-case : Cube (ap-square (λ z → c2t (t2c z)) T.f)
                     (ap-square (λ z → z) T.f)
                     p-case q-case q-case p-case
        f-case = (ap-square-o c2t t2c T.f) ·-cube-h
                 ap-cube c2t (T.βf/rec (S¹.base , S¹.base) (pair×≃ S¹.loop id) (pair×≃ id S¹.loop) (pair-square hrefl-square vrefl-square)) ·-cube-h
                 bifunctor-cube1' c2t' S¹.loop S¹.loop ·-cube-h 
                 snd (snd c2t'-loop-loop-cube) ·-cube-h 
                 ap-square-id! T.f

  c2t2c : (x y : S¹) → t2c (c2t' x y) == (x , y)
  c2t2c = S¹-elimo _ (S¹-elimo _ id (PathOver=.in-PathOver-= (square-symmetry loop2-case))) 
           (coe (! PathOverΠ-NDdomain) 
                (λ x → PathOver=.in-PathOver-= 
                  (S¹-elimo
                    (λ x₁ → Square (S¹-elimo (λ x₂ → t2c (c2t' S¹.base x₂) == (S¹.base , x₂)) id (PathOver=.in-PathOver-= (square-symmetry loop2-case)) x₁) (ap (λ z → t2c (c2t' z x₁)) S¹.loop) (ap (λ z → z , x₁) S¹.loop) (S¹-elimo (λ x₂ → t2c (c2t' S¹.base x₂) == (S¹.base , x₂)) id (PathOver=.in-PathOver-= (square-symmetry loop2-case)) x₁))
                    (square-symmetry loop1-case)
                    (PathOver-Square.in-PathOver-Square _ (whisker-cube id id red id id red (cube-symmetry-left-to-top looploop-case)))
                    x))) where
    loop1-case = _
    loop2-case = _
    looploop-case : Cube
              (PathOver=.out-PathOver-=
               (apdo (λ x → ap (λ z → t2c (c2t' z x)) S¹.loop) S¹.loop))
              (PathOver=.out-PathOver-=
               (apdo (λ x → ap (λ z → z , x) S¹.loop) S¹.loop))
              loop1-case loop2-case loop2-case loop1-case
    looploop-case = !-cube-h (bifunctor-cube1' (λ x y → t2c (c2t' x y)) S¹.loop S¹.loop) ·-cube-h
                    ap-square-o t2c c2t (pair-square hrefl-square vrefl-square) ·-cube-h
                    ap-cube t2c (bifunctor-cube1' c2t' S¹.loop S¹.loop ·-cube-h (snd (snd c2t'-loop-loop-cube))) ·-cube-h
                    T.βf/rec (S¹.base , S¹.base) (pair×≃ S¹.loop id) (pair×≃ id S¹.loop) (pair-square hrefl-square vrefl-square) 
                    ·-cube-h ap-square-id! (pair-square hrefl-square vrefl-square) 
                    ·-cube-h bifunctor-cube1' _,_ S¹.loop S¹.loop

    red = (! (IsEquiv.β (snd PathOver=.out-PathOver-=-eqv) (square-symmetry loop2-case) ∘ 
          ap PathOver=.out-PathOver-= (S¹.βloop/elimo _ id (PathOver=.in-PathOver-= (square-symmetry loop2-case)))))
