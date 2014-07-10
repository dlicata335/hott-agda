{-# OPTIONS --type-in-type --without-K #-}

open import lib.BasicTypes
open import lib.cubical.PathOver
open import lib.cubical.Square

module lib.cubical.Cube where


  data Cube {A : Type} {a000 : A} : 
    {a010 a100 a110 a001 a011 a101 a111 : A}
    {p0-0 : a000 == a010}
    {p-00 : a000 == a100}
    {p-10 : a010 == a110}
    {p1-0 : a100 == a110}
    (f--0 : Square p0-0 p-00 p-10 p1-0)

    {p0-1 : a001 == a011}
    {p-01 : a001 == a101}
    {p-11 : a011 == a111}
    {p1-1 : a101 == a111}
    (f--1 : Square p0-1 p-01 p-11 p1-1)

    {p00- : a000 == a001}
    {p01- : a010 == a011}
    {p10- : a100 == a101}
    {p11- : a110 == a111}
    (f0-- : Square p0-0 p00- p01- p0-1)
    (f-0- : Square p-00 p00- p10- p-01)
    (f-1- : Square p-10 p01- p11- p-11)
    (f1-- : Square p1-0 p10- p11- p1-1)
    → Type where
    id : Cube id id id id id id

  SquareOver-='' : {A : Type} 
    {a000 a010 a100 a110 a001 a011 a101 a111 : A}
    {p0-0 : a000 == a010}
    {p-00 : a000 == a100}
    {p-10 : a010 == a110}
    {p1-0 : a100 == a110}
    {f--0 : Square p0-0 p-00 p-10 p1-0}

    {p0-1 : a001 == a011}
    {p-01 : a001 == a101}
    {p-11 : a011 == a111}
    {p1-1 : a101 == a111}
    {f--1 : Square p0-1 p-01 p-11 p1-1}

    {p00- : a000 == a001}
    {p01- : a010 == a011}
    {p10- : a100 == a101}
    {p11- : a110 == a111}
    {f0-- : Square p0-0 p00- p01- p0-1}
    {f-0- : Square p-00 p00- p10- p-01}
    {f-1- : Square p-10 p01- p11- p-11}
    {f1-- : Square p1-0 p10- p11- p1-1}
    → Cube f--0 f--1 f0-- f-0- f-1- f1--
    → SquareOver (\ x -> a000 == x) f-1-
                 (in-PathOver-=' f--0)
                 (in-PathOver-=' f0--)
                 (in-PathOver-=' (∘-square-vertical f-0- f1--))
                 (in-PathOver-=' {p0- = p0-1 ∘ p00- } {p-0 = p00- } {p-1 = p-11} {p1- = p1-1 ∘ p-01}
                                 (∘-square-vertical {p-00 = p00- } {p1-0 = p0-1} {p-01 = p-01}
                                    {p1-1 = p1-1} {p00- = p00- } {p10- = p-01} {p11- = p-11} connection2 f--1))
    
  SquareOver-='' id = id


  SquareOver-=' : {A : Type} {a' : A} 
                 {a00 : A} {a01 a10 a11 : A} 
                 {p0- : a00 == a01}
                 {p-0 : a00 == a10}
                 {p-1 : a01 == a11}
                 {p1- : a10 == a11}
                 (f   : Square p0- p-0 p-1 p1-)
                 {b00 : a' == a00} (b01 : a' == a01)
                 (q0- : PathOver (_==_ a') p0- b00 b01)
                 (b10 : a' == a10)
                 (q-0 : PathOver (_==_ a') p-0 b00 b10)
                 (b11 : a' == a11)
                 (q-1 : PathOver (_==_ a') p-1 b01 b11)
                 (q1- : PathOver (_==_ a') p1- b10 b11)
                 → Cube (out-PathOver-= q0-) (out-PathOver-= q1-) (out-PathOver-= q-0) id f (out-PathOver-= q-1)
                 → SquareOver (\ x -> a' == x) f 
                              q0-
                              q-0
                              q-1
                              q1-
  SquareOver-=' id {b00 = id} = path-induction-homo-e _ (path-induction-homo-e _ (path-induction-homo-e _ (λ q1- → \ c -> transport (\ x -> SquareOver (Path _) id id id id x) (PathOver-=-inout q1-) (SquareOver-='' c)))) 

  SquareOver-= : {A : Type} {a' : A} 
                 {a00 : A} {a01 a10 a11 : A} 
                 {p0- : a00 == a01}
                 {p-0 : a00 == a10}
                 {p-1 : a01 == a11}
                 {p1- : a10 == a11}
                 (f   : Square p0- p-0 p-1 p1-)
                 {b00 : a' == a00} {b01 : a' == a01} {b10 : a' == a10} {b11 : a' == a11}
                 (q0- : PathOver (_==_ a') p0- b00 b01)
                 (q-0 : PathOver (_==_ a') p-0 b00 b10)
                 (q-1 : PathOver (_==_ a') p-1 b01 b11)
                 (q1- : PathOver (_==_ a') p1- b10 b11)
                 → Cube (out-PathOver-= q0-) (out-PathOver-= q1-) (out-PathOver-= q-0) id f (out-PathOver-= q-1)
                 → SquareOver (\ x -> a' == x) f 
                              q0-
                              q-0
                              q-1
                              q1-
  SquareOver-= f q1 q2 q3 q4 c = SquareOver-=' f _ q1 _ q2 _ q3 q4 c


