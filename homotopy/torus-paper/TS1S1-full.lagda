
%include agda.fmt

\begin{figure*}[h]

\ignore{ 
\begin{code}
{-# OPTIONS --type-in-type --without-K #-}
open import lib.Prelude
open import lib.cubical.Cubical

module homotopy.torus-paper.TS1S1-full where

  open S¹ using (S¹ ; S¹-rec ; S¹-elimo; base; loop)
  module T = Torus
  open T using (T ; T-rec ; T-elim; a; p; q; f)
  open PathOver=
  open SquareOver=ND
  open PathOver-Square

  pair-line = pair×≃
\end{code}
}

\begin{code}  
  t2c : T → S¹ × S¹
  t2c = T-rec (base , base) (pair-line loop id) (pair-line id loop) (pair-square hrefl-square vrefl-square)
\end{code}

\ignore{
\begin{code}
  βfcube = T.βf/rec (base , base) (pair-line loop id) (pair-line id loop) (pair-square hrefl-square vrefl-square)

  βsquare = horiz-degen-square (S¹.βloop/rec a q)
\end{code}
}

\begin{code}
  c2t-square-and-cube : Σ \  (s : Square p (ap (S¹-rec a q) loop) (ap (S¹-rec a q) loop) p) → 
                             Cube s f hrefl-square βsquare βsquare hrefl-square
  c2t-square-and-cube = (fill-cube-left _ _ _ _ _)

  c2t-loop-homotopy = S¹-elimo _ p (in-PathOver-= (fst c2t-square-and-cube))

  c2t' : S¹ → S¹ → T
  c2t' = S¹-rec (S¹-rec a q) (λ≃ c2t-loop-homotopy) 

  c2t : S¹ × S¹ → T
  c2t (x , y) = c2t' x y
\end{code}


\begin{code}
  c2t'-β :  Σ \ (  c2t'-loop-2 : Square (ap (c2t' base) loop) id id q) → 
            Σ \ (  c2t'-loop-1 : Square (ap (λ x → c2t' x base) loop) id id p)  → 
                   Cube (apdo-ap c2t' loop loop) f c2t'-loop-1 c2t'-loop-2 c2t'-loop-2 c2t'-loop-1
  c2t'-β = _ , _ , 
          out-SquareOver-= (apdo-by-equals _ _ _ (λ≃ (\ y → ap-o (λ f → f y) c2t' loop))) ·-cube-h
          out-SquareOver-= (apdo-by-equals _ _ _ (λ≃ (\ y → ap (ap (λ f → f y)) 
            (S¹.βloop/rec (S¹-rec a q) (λ≃ c2t-loop-homotopy))))) ·-cube-h
          out-SquareOver-= (apdo-by-equals _ _ _ (λ≃ (λ y → Π≃β c2t-loop-homotopy))) ·-cube-h
          degen-cube-h (ap out-PathOver-= (S¹.βloop/elimo _ p (in-PathOver-= (fst c2t-square-and-cube)))) ·-cube-h
          degen-cube-h (IsEquiv.β (snd out-PathOver-=-eqv) _) ·-cube-h 
          (snd c2t-square-and-cube)
\end{code}


\begin{code}
  t2c2t : (x : T) → Path (c2t (t2c x)) x
  t2c2t = T-elim  _ id (in-PathOver-= (square-symmetry p-case)) (in-PathOver-= (square-symmetry q-case))
                  (in-SquareOver-= 
                    (whisker-cube  (! (IsEquiv.β (snd out-PathOver-=-eqv) _)) (! (IsEquiv.β (snd out-PathOver-=-eqv) _))
                                   (! (IsEquiv.β (snd out-PathOver-=-eqv) _)) id id (! (IsEquiv.β (snd out-PathOver-=-eqv) _))
                                   (cube-symmetry-left-to-top f-case))) where
        p-case = _
        q-case = _
        f-case : Cube (ap-square (λ z → c2t (t2c z)) f) (ap-square (λ z → z) f) p-case q-case q-case p-case
        f-case =   ap-square-o c2t t2c f ·-cube-h
                   ap-cube c2t βfcube ·-cube-h
                   apdo-ap-cube-hv c2t' loop loop ·-cube-h 
                   snd (snd c2t'-β) ·-cube-h 
                   ap-square-id! f

  c2t2c : (x y :  S¹) → Path (t2c (c2t' x y)) (x , y)
  c2t2c = S¹-elimo  _ (S¹-elimo _ id (in-PathOver-= (square-symmetry loop2-case))) 
                    (coe (! PathOverΠ-NDdomain) 
                      (in-PathOver-= od1 (S¹-elimo  _ (square-symmetry loop1-case)
                                                    (in-PathOver-Square _ 
                                                      (whisker-cube id id red id id red 
                                                         (cube-symmetry-left-to-top looploop-case)))))) where
    loop1-case = _
    loop2-case = _
    looploop-case : Cube  (apdo-ap (\ x y → t2c (c2t' x y)) loop loop) (apdo-ap _,_ loop loop)
                          loop1-case loop2-case loop2-case loop1-case
    looploop-case =  apdo-ap-o t2c c2t' loop loop ·-cube-h
                     ap-cube t2c (snd (snd c2t'-β)) ·-cube-h
                     βfcube ·-cube-h 
                     ap-square-id! _ ·-cube-h
                     apdo-ap-cube-hv _,_ loop loop

    red =  ! (ap out-PathOver-= (S¹.βloop/elimo _ id (in-PathOver-= (square-symmetry loop2-case))) ·
              IsEquiv.β (snd out-PathOver-=-eqv) (square-symmetry loop2-case))
\end{code}

\caption{Appendix: |T ≃ S¹ × S¹| proof}
\label{fig:ts1s1-full}

\end{figure*}
