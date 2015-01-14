{-# OPTIONS --type-in-type --without-K #-}
open import lib.Prelude
open import lib.cubical.Cubical

module homotopy.TS1S1-2 where

  open S¹ using (S¹ ; S¹-rec ; S¹-elimo)
  module T = Torus
  open T using (T ; T-rec ; T-elim)

  βsquare = horiz-degen-square (S¹.βloop/rec T.a T.q)

  t2c : T -> S¹ × S¹
  t2c = T-rec (S¹.base , S¹.base) (pair×≃ S¹.loop id) (pair×≃ id S¹.loop) (pair-square hrefl-square vrefl-square)

  βfcube = T.βf/rec (S¹.base , S¹.base) (pair×≃ S¹.loop id) (pair×≃ id S¹.loop) (pair-square hrefl-square vrefl-square)

  abstract
    c2t-square-and-cube : Σ \ (s : Square T.p (ap (S¹-rec T.a T.q) S¹.loop) (ap (S¹-rec T.a T.q) S¹.loop) T.p)
                             -> Cube s T.f hrefl-square βsquare βsquare hrefl-square
    c2t-square-and-cube = (fill-cube-left _ _ _ _ _)

  c2t-loop-homotopy = S¹-elimo _ T.p (PathOver=.in-PathOver-= (fst c2t-square-and-cube))

  c2t' : S¹ → S¹ → T
  c2t' = S¹-rec (S¹-rec T.a T.q) (λ≃ c2t-loop-homotopy) 

  c2t : S¹ × S¹ → T
  c2t (x , y) = c2t' x y

  c2t'-β : Σ \ (c2t'-loop-2 : Square (ap (c2t' S¹.base) S¹.loop) id id T.q) → 
           Σ \ (c2t'-loop-1 : Square (ap (λ x → c2t' x S¹.base) S¹.loop) id id T.p)  → 
                Cube (apdo-ap c2t' S¹.loop S¹.loop) T.f c2t'-loop-1 c2t'-loop-2 c2t'-loop-2 c2t'-loop-1
  c2t'-β = _ , _ , 
          SquareOver=ND.out-SquareOver-= (apdo-by-equals _ _ S¹.loop (λ≃ (\ y -> ap-o (λ f → f y) c2t' S¹.loop))) ·-cube-h
          SquareOver=ND.out-SquareOver-= (apdo-by-equals _ _ S¹.loop (λ≃ (\ y -> ap (ap (λ f → f y)) (S¹.βloop/rec (S¹-rec T.a T.q) (λ≃ c2t-loop-homotopy))))) ·-cube-h
          SquareOver=ND.out-SquareOver-= (apdo-by-equals _ _ S¹.loop (λ≃ (λ y → Π≃β c2t-loop-homotopy))) ·-cube-h
          degen-cube-h (ap PathOver=.out-PathOver-= (S¹.βloop/elimo _ T.p (PathOver=.in-PathOver-= (fst c2t-square-and-cube)))) ·-cube-h
          degen-cube-h (IsEquiv.β (snd PathOver=.out-PathOver-=-eqv) _) ·-cube-h 
          (snd c2t-square-and-cube)

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
                 ap-cube c2t βfcube ·-cube-h
                 apdo-ap-cube-hv c2t' S¹.loop S¹.loop ·-cube-h 
                 snd (snd c2t'-β) ·-cube-h 
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
    looploop-case : Cube (apdo-ap (\ x y → t2c (c2t' x y)) S¹.loop S¹.loop)
                         (apdo-ap _,_ S¹.loop S¹.loop)
                    loop1-case loop2-case loop2-case loop1-case
    looploop-case = apdo-ap-o t2c c2t' S¹.loop S¹.loop ·-cube-h
                    ap-cube t2c (snd (snd c2t'-β)) ·-cube-h
                    βfcube ·-cube-h 
                    ap-square-id! (pair-square hrefl-square vrefl-square) ·-cube-h
                    apdo-ap-cube-hv _,_ S¹.loop S¹.loop

    red = (! (IsEquiv.β (snd PathOver=.out-PathOver-=-eqv) (square-symmetry loop2-case) ∘ 
          ap PathOver=.out-PathOver-= (S¹.βloop/elimo _ id (PathOver=.in-PathOver-= (square-symmetry loop2-case)))))
