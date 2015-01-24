{-# OPTIONS --type-in-type --without-K #-}

open import lib.BasicTypes
open import lib.cubical.PathOver
open import lib.cubical.Square

module lib.cubical.Cube where

  -- coordinates are yzx because we think of the principle sides as the left and the right
  -- 000 is top-back-left
  -- then faces in order are
  data Cube {A : Type} {a000 : A} : 
    {a010 a100 a110 a001 a011 a101 a111 : A}
    {p0-0 : a000 == a010}
    {p-00 : a000 == a100}
    {p-10 : a010 == a110}
    {p1-0 : a100 == a110}
    (f--0 : Square p0-0 p-00 p-10 p1-0) -- left

    {p0-1 : a001 == a011}
    {p-01 : a001 == a101}
    {p-11 : a011 == a111}
    {p1-1 : a101 == a111}
    (f--1 : Square p0-1 p-01 p-11 p1-1) -- right

    {p00- : a000 == a001}
    {p01- : a010 == a011}
    {p10- : a100 == a101}
    {p11- : a110 == a111}
    (f0-- : Square p0-0 p00- p01- p0-1) -- back
    (f-0- : Square p-00 p00- p10- p-01) -- top
    (f-1- : Square p-10 p01- p11- p-11) -- bot
    (f1-- : Square p1-0 p10- p11- p1-1) -- front
    → Type where
    id : Cube id id id id id id

  data CubeOver {A : Type} {a000 : A} (B : A → Type) {b000 : B a000}: 
    {a010 a100 a110 a001 a011 a101 a111 : A}
    {b010 : B a010} {b100 : B a100} {b110 : B a110} {b001 : B a001} {b011 : B a011} {b101 : B a101} {b111 : B a111}
    {p0-0 : a000 == a010} {q0-0 : PathOver B p0-0 b000 b010}
    {p-00 : a000 == a100}     {q-00 : PathOver B p-00 b000 b100}
    {p-10 : a010 == a110}     {q-10 : PathOver B p-10 b010 b110}
    {p1-0 : a100 == a110}     {q1-0 : PathOver B p1-0 b100 b110}
    {f--0 : Square p0-0 p-00 p-10 p1-0} -- left

    {p0-1 : a001 == a011}     {q0-1 : PathOver B p0-1 b001 b011}
    {p-01 : a001 == a101}     {q-01 : PathOver B p-01 b001 b101}
    {p-11 : a011 == a111}     {q-11 : PathOver B p-11 b011 b111}
    {p1-1 : a101 == a111}     {q1-1 : PathOver B p1-1 b101 b111}
    {f--1 : Square p0-1 p-01 p-11 p1-1} -- right

    {p00- : a000 == a001}     {q00- : PathOver B p00- b000 b001}
    {p01- : a010 == a011}     {q01- : PathOver B p01- b010 b011}
    {p10- : a100 == a101}     {q10- : PathOver B p10- b100 b101}
    {p11- : a110 == a111}     {q11- : PathOver B p11- b110 b111}
    {f0-- : Square p0-0 p00- p01- p0-1} -- back
    {f-0- : Square p-00 p00- p10- p-01} -- top
    {f-1- : Square p-10 p01- p11- p-11} -- bot
    {f1-- : Square p1-0 p10- p11- p1-1} -- front

    → Cube f--0 f--1 f0-- f-0- f-1- f1-- 
    → 
    (g--0 : SquareOver B f--0 q0-0 q-00 q-10 q1-0) -- left
    (g--1 : SquareOver B f--1 q0-1 q-01 q-11 q1-1) -- right
    (g0-- : SquareOver B f0-- q0-0 q00- q01- q0-1) -- back
    (g-0- : SquareOver B f-0- q-00 q00- q10- q-01) -- top
    (g-1- : SquareOver B f-1- q-10 q01- q11- q-11) -- bot
    (g1-- : SquareOver B f1-- q1-0 q10- q11- q1-1) -- front 
   
    → Type where
    id : CubeOver B id id id id id id id

  whisker-cube :  {A : Type} {a000 : A}  
    {a010 a100 a110 a001 a011 a101 a111 : A}
    {p0-0 : a000 == a010}
    {p-00 : a000 == a100}
    {p-10 : a010 == a110}
    {p1-0 : a100 == a110}
    {f--0 f--0' : Square p0-0 p-00 p-10 p1-0} -- left
    → f--0 == f--0'
    → 
    {p0-1 : a001 == a011}
    {p-01 : a001 == a101}
    {p-11 : a011 == a111}
    {p1-1 : a101 == a111}
    {f--1 f--1' : Square p0-1 p-01 p-11 p1-1} -- right
    → f--1 == f--1'
    → 
    {p00- : a000 == a001}
    {p01- : a010 == a011}
    {p10- : a100 == a101}
    {p11- : a110 == a111}
    {f0-- f0--' : Square p0-0 p00- p01- p0-1} -- back
    → f0-- == f0--'
    →
    {f-0- f-0-' : Square p-00 p00- p10- p-01} -- top
    → f-0- == f-0-'
    → {f-1- f-1-' : Square p-10 p01- p11- p-11} -- bot
    → f-1- == f-1-'
    → {f1-- f1--' : Square p1-0 p10- p11- p1-1} -- front
    → f1-- == f1--'
    -> Cube f--0 f--1 f0-- f-0- f-1- f1--
    -> Cube f--0' f--1' f0--' f-0-' f-1-' f1--'
  whisker-cube id id id id id id c = c

  -- old left and right are new top and bottom
  -- old top and bottom are new front and back
  -- old back and front are new left and right
  cube-symmetry-left-to-top :
    {A : Type}
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
    → Cube (square-symmetry f0--) (square-symmetry f1--) (square-symmetry f-0-) f--0 f--1 (square-symmetry f-1-)
  cube-symmetry-left-to-top id = id

  -- apply square symmetry to the left
  cube-square-symmetry-left :
    {A : Type}
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
    → Cube (square-symmetry f--0) (square-symmetry f--1) f-0- f0-- f1-- f-1-
  cube-square-symmetry-left id = id

  ap-cube :
    {A B : Type} (f : A → B)
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
    → Cube (ap-square f f--0) (ap-square f f--1) (ap-square f f0--) (ap-square f f-0-) (ap-square f f-1-) (ap-square f f1--)
  ap-cube f id = id

  _·-cube-h_ :  {A : Type} {a000 : A}  
    {a010 a100 a110 a001 a011 a101 a111 : A}
    {p0-0 : a000 == a010}
    {p-00 : a000 == a100}
    {p-10 : a010 == a110}
    {p1-0 : a100 == a110}
    {f--0 : Square p0-0 p-00 p-10 p1-0} -- left

    {p0-1 : a001 == a011}
    {p-01 : a001 == a101}
    {p-11 : a011 == a111}
    {p1-1 : a101 == a111}
    {f--1 : Square p0-1 p-01 p-11 p1-1} -- right

    {p00- : a000 == a001}
    {p01- : a010 == a011}
    {p10- : a100 == a101}
    {p11- : a110 == a111}
    {f0-- : Square p0-0 p00- p01- p0-1} -- back
    {f-0- : Square p-00 p00- p10- p-01} -- top
    {f-1- : Square p-10 p01- p11- p-11} -- bot
    {f1-- : Square p1-0 p10- p11- p1-1} -- front

    {a002 a012 a102 a112 : A}
    {p0-2 : a002 == a012}
    {p-02 : a002 == a102}
    {p-12 : a012 == a112}
    {p1-2 : a102 == a112}
    {f--2 : Square p0-2 p-02 p-12 p1-2} -- right'

    {p00-' : a001 == a002}
    {p01-' : a011 == a012}
    {p10-' : a101 == a102}
    {p11-' : a111 == a112}
    {f0--' : Square p0-1 p00-' p01-' p0-2} -- back'
    {f-0-' : Square p-01 p00-' p10-' p-02} -- top'
    {f-1-' : Square p-11 p01-' p11-' p-12} -- bot'
    {f1--' : Square p1-1 p10-' p11-' p1-2} -- front'
    -> Cube f--0 f--1 f0-- f-0- f-1- f1--
    → Cube f--1 f--2 f0--' f-0-' f-1-' f1--'
    -> Cube f--0 f--2 (f0-- ·-square-h f0--') (f-0- ·-square-h f-0-') (f-1- ·-square-h f-1-') (f1-- ·-square-h f1--')
  id ·-cube-h c = c

  infixr 10 _·-cube-h_

  !-cube-h : {A : Type} {a000 : A}  
    {a010 a100 a110 a001 a011 a101 a111 : A}
    {p0-0 : a000 == a010}
    {p-00 : a000 == a100}
    {p-10 : a010 == a110}
    {p1-0 : a100 == a110}
    {f--0 : Square p0-0 p-00 p-10 p1-0} -- left

    {p0-1 : a001 == a011}
    {p-01 : a001 == a101}
    {p-11 : a011 == a111}
    {p1-1 : a101 == a111}
    {f--1 : Square p0-1 p-01 p-11 p1-1} -- right

    {p00- : a000 == a001}
    {p01- : a010 == a011}
    {p10- : a100 == a101}
    {p11- : a110 == a111}
    {f0-- : Square p0-0 p00- p01- p0-1} -- back
    {f-0- : Square p-00 p00- p10- p-01} -- top
    {f-1- : Square p-10 p01- p11- p-11} -- bot
    {f1-- : Square p1-0 p10- p11- p1-1} -- front
    → Cube f--0 f--1 f0-- f-0- f-1- f1--
    → Cube f--1 f--0 (!-square-h f0--) (!-square-h f-0-) (!-square-h f-1-) (!-square-h f1--)
  !-cube-h id = id

  module SquareOverPathFrom where
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
                   (PathOverPathFrom.in-PathOver-=' f--0)
                   (PathOverPathFrom.in-PathOver-=' f0--)
                   (PathOverPathFrom.in-PathOver-=' (·-square-vertical f-0- f1--))
                   (PathOverPathFrom.in-PathOver-=' {p0- = p0-1 ∘ p00- } {p-0 = p00- } {p-1 = p-11} {p1- = p1-1 ∘ p-01}
                                   (·-square-vertical connection2 f--1))
      
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
                   → Cube (PathOverPathFrom.out-PathOver-= q0-) (PathOverPathFrom.out-PathOver-= q1-) (PathOverPathFrom.out-PathOver-= q-0) id f (PathOverPathFrom.out-PathOver-= q-1)
                   → SquareOver (\ x -> a' == x) f 
                                q0-
                                q-0
                                q-1
                                q1-
    SquareOver-=' id {b00 = id} = path-induction-homo-e _ (path-induction-homo-e _ (path-induction-homo-e _ (λ q1- → \ c -> transport (\ x -> SquareOver (Path _) id id id id x) (PathOverPathFrom.PathOver-=-inout q1-) (SquareOver-='' c)))) 
  
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
                   → Cube (PathOverPathFrom.out-PathOver-= q0-) (PathOverPathFrom.out-PathOver-= q1-) (PathOverPathFrom.out-PathOver-= q-0) id f (PathOverPathFrom.out-PathOver-= q-1)
                   → SquareOver (\ x -> a' == x) f 
                                q0-
                                q-0
                                q-1
                                q1-
    SquareOver-= f q1 q2 q3 q4 c = SquareOver-=' f _ q1 _ q2 _ q3 q4 c

  module CubePath where
    cube-to-path :
      {A : Type}
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
      → Path (whisker-square id (square-to-disc' f-0-) (square-to-disc' f-1-) id
                ((!-square-h f0-- ·-square-h f--0) ·-square-h f1--)) f--1
    cube-to-path id = id

    cube-to-path/degen-tube : {A : Type} {a000 : A} {a010 a100 a110 : A}
                    {p0-0 : a000 == a010}
                    {p-00 : a000 == a100}
                    {p-10 : a010 == a110}
                    {p1-0 : a100 == a110}
                    {f--0 f--1 : Square p0-0 p-00 p-10 p1-0}
                  → Cube f--0 f--1 hrefl-square hrefl-square hrefl-square hrefl-square 
                  → f--0 == f--1
    cube-to-path/degen-tube {p0-0 = id} {p-00 = id} {p-10 = id} {p1-0} c = ! (·-square-h-unit-r _) · cube-to-path c

{-
  module CubeSquare where
    cube-to-square : {A : Type} {a000 : A}  
      {a010 X : A}
      {p0-0 : a000 == a010}
      {p1-0 : a000 == a010}
      (f--0 : Square p0-0 id id p1-0) -- left
      {p0-1 : a000 == a010}
      {p1-1 : a000 == a010}
      (f--1 : Square p0-1 id id p1-1) -- right
      (f0-- : Square p0-0 id id p0-1) -- back
      (f1-- : Square p1-0 id id p1-1) -- front
      → Cube f--0 f--1 f0-- id id f1--
      → Square (horiz-degen-square-to-path f--0) (horiz-degen-square-to-path f0--) (horiz-degen-square-to-path f1--) (horiz-degen-square-to-path f--1)
    cube-to-square {a000 = a000} {p0-0 = id} = horiz-degen-square-induction1 
      (\ {p1-0} f--0 → 
       {p0-1 : a000 == a000}
       {p1-1 : a000 == a000}
       (f--1 : Square p0-1 id id p1-1) -- right
       (f0-- : Square id id id p0-1) -- back
       (f1-- : Square p1-0 id id p1-1) -- front
       → Cube f--0 f--1 f0-- id id f1--
       → Square (horiz-degen-square-to-path f--0) (horiz-degen-square-to-path f0--) (horiz-degen-square-to-path f1--) (horiz-degen-square-to-path f--1))
      {!!}
-}
  
  module SquareOver=ND where

    open PathOver=

    in-SquareOver-= : {A B : Type} {f g : A → B} 
                       {a00 : A} {a01 a10 a11 : A} 
                       {p0- : a00 == a01}
                       {p-0 : a00 == a10}
                       {p-1 : a01 == a11}
                       {p1- : a10 == a11}
                       {fa   : Square p0- p-0 p-1 p1- }
                       {b00 : f a00 == g a00} {b01 : f a01 == g a01} {b10 : f a10 == g a10} {b11 : f a11 == g a11}
                       {q0- : PathOver (\ x -> f x == g x) p0- b00 b01}
                       {q-0 : PathOver (\ x -> f x == g x) p-0 b00 b10}
                       {q-1 : PathOver (\ x -> f x == g x) p-1 b01 b11}
                       {q1- : PathOver (\ x -> f x == g x) p1- b10 b11}
                       → Cube (out-PathOver-= q0-) (out-PathOver-= q1-) (out-PathOver-= q-0) (ap-square f fa) (ap-square g fa) (out-PathOver-= q-1)
                       → SquareOver (\ x -> f x == g x) fa
                                    q0-
                                    q-0
                                    q-1
                                    q1-
    in-SquareOver-= {f = f} {g} {fa = fa} {b00 = b00} {q0- = id} {q-0 = id} {q-1 = id} c = 
      horiz-degen-square-induction1
        (λ {p1- } fa →
           {q1- : PathOver (λ x → f x == g x) p1- b00 b00}
           (c₁
            : Cube hrefl-square (out-PathOver-= q1-) hrefl-square
              (ap-square f fa) (ap-square g fa) hrefl-square) →
           SquareOver (λ x → f x == g x) fa id id id q1-)
        (λ {q1- } c → transport
         (λ x → SquareOver (λ x₁ → Id (f x₁) (g x₁)) id id id id x) (IsEquiv.β (snd hom-to-over/left-eqv) q1-)
                        (square-to-over-id
                         (coh {q1- = over-to-hom q1- }
                          (whisker-cube id (! (coh2 _ q1-)) id id id id c))) ) fa c where -- need square over id is a square
      coh : ∀ {A} {a b : A} {b00 : a == b} {q1- : b00 == b00} →
         Cube hrefl-square (horiz-degen-square q1-) hrefl-square id id hrefl-square → Square id id id q1-
      coh {b00 = id} {q1- } c = transport (λ x → Square id id id x) (IsEquiv.β (snd horiz-degen-square-eqv) q1- ∘ ap horiz-degen-square-to-path (CubePath.cube-to-path c)) id

      coh2 : (b00' : _) (q1- : PathOver (λ x → f x == g x) id b00 b00') → (horiz-degen-square (over-to-hom q1-)) == (out-PathOver-= q1-) 
      coh2 = path-induction-homo-e _ (coh2a b00) where
        coh2a : ∀ {A} {a b : A} (p : a == b) → horiz-degen-square id == hrefl-square {p = p}
        coh2a id = id

    out-SquareOver-= : {A B : Type} {f g : A → B} 
                     {a00 : A} {a01 a10 a11 : A} 
                     {p0- : a00 == a01}
                     {p-0 : a00 == a10}
                     {p-1 : a01 == a11}
                     {p1- : a10 == a11}
                     {fa   : Square p0- p-0 p-1 p1- }
                     {b00 : f a00 == g a00} {b01 : f a01 == g a01} {b10 : f a10 == g a10} {b11 : f a11 == g a11}
                     {q0- : PathOver (\ x -> f x == g x) p0- b00 b01}
                     {q-0 : PathOver (\ x -> f x == g x) p-0 b00 b10}
                     {q-1 : PathOver (\ x -> f x == g x) p-1 b01 b11}
                     {q1- : PathOver (\ x -> f x == g x) p1- b10 b11}
                     → SquareOver (\ x -> f x == g x) fa
                                  q0-
                                  q-0
                                  q-1
                                  q1-
                     → Cube (out-PathOver-= q0-) (out-PathOver-= q1-) (out-PathOver-= q-0) (ap-square f fa) (ap-square g fa) (out-PathOver-= q-1)
    out-SquareOver-= {b00 = b00} id = coh b00 where 
      coh : ∀ {a b} (p : a == b) → Cube (hrefl-square {p = p}) (hrefl-square {p = p}) (hrefl-square {p = p}) id id (hrefl-square {p = p})
      coh id = id

  module PathOver-Square where

    in-PathOver-Square : {Γ A : Type} {x1 x2 : Γ} (δ : x1 == x2) {a00 a01 a10 a11 : Γ → A} 
                          {p0- : (x : Γ) → a00 x == a01 x}
                          {p-0 : (x : Γ) → a00 x == a10 x }
                          {p-1 : (x : Γ) → a01 x == a11 x }
                          {p1- : (x : Γ) → a10 x == a11 x }
                          {f1 : Square (p0- x1) (p-0 x1) (p-1 x1) (p1- x1)}
                          {f2 : Square (p0- x2) (p-0 x2) (p-1 x2) (p1- x2)}
                       → (Cube f1 f2 (PathOver=.out-PathOver-= (apdo p0- δ)) (PathOver=.out-PathOver-= (apdo p-0 δ)) (PathOver=.out-PathOver-= (apdo p-1 δ)) (PathOver=.out-PathOver-= (apdo p1- δ)))
                       → (PathOver (\ x -> Square (p0- x) (p-0 x) (p-1 x) (p1- x)) δ f1 f2)
    in-PathOver-Square id {f1 = f1} {f2} c = hom-to-over (coh _ _ c) where
      coh : {A : Type}
            {a00 a01 a10 a11 : A} 
            {p0- : a00 == a01}
            {p-0 : a00 == a10}
            {p-1 : a01 == a11}
            {p1- : a10 == a11}
          → (f1 f2 : (Square p0- p-0 p-1 p1-))
          → Cube f1 f2 hrefl-square hrefl-square hrefl-square hrefl-square
          → f1 == f2
      coh id f2 c = CubePath.cube-to-path c

  degen-cube-h :{A : Type} {a000 : A} 
    {a010 a100 a110 : A}
    {p0-0 : a000 == a010}
    {p-00 : a000 == a100}
    {p-10 : a010 == a110}
    {p1-0 : a100 == a110}
    {f--0 f--1 : Square p0-0 p-00 p-10 p1-0} -- left and right
    -> f--0 == f--1
    → Cube f--0 f--1 hrefl-square hrefl-square hrefl-square hrefl-square
  degen-cube-h {f--0 = id} id = id

  -- ap to inner argument first
  -- could do it in the other order, too
  apdo-ap : {A B C : Type} (f : A → B → C) {a a' : A} {b b' : B}
                     (p : a == a') (q : b == b') 
                   → Square (ap (λ x → f x b) p)
                             (ap (λ z → f a z) q)
                             (ap (λ z → f a' z) q)
                             (ap (λ x → f x b') p)
  apdo-ap f p q = PathOver=.out-PathOver-= (apdo (λ y → ap (λ x → f x y) p) q)

  apdo-ap' : {A B C : Type} (f : A → B → C) {a a' : A} {b b' : B}
                     (p : a == a') (q : b == b') 
                   → Square (ap (λ y → f a y) q) (ap (λ z → f z b) p) (ap (λ z → f z b') p) (ap (λ y → f a' y) q) 
  apdo-ap' f p q = PathOver=.out-PathOver-= (apdo (λ x → ap (λ y → f x y) q) p)

  ap-id-fst : {A B C : Type} (f : A → B → C) {a : A} {b b' : B}
                      (q : b == b') 
                    → ap (uncurry f) (pair×≃ id q) == ap (f a) q
  ap-id-fst f id = id

  ap-id-snd : {A B C : Type} (f : A → B → C) {a a' : A} {b : B}
                      (p : a == a') 
                    → ap (uncurry f) (pair×≃ p id) == ap (\ x -> f x b) p
  ap-id-snd f id = id

  apdo-ap-o : {A B C D : Type} (g : C → D) (f : A → B → C) {a a' : A} {b b' : B}
              (p : a == a') (q : b == b') 
            → Cube (apdo-ap (\ x y → g (f x y)) p q)
                   (ap-square g (apdo-ap f p q))
                   (horiz-degen-square (ap-o _ _ p)) (horiz-degen-square (ap-o _ _ q)) (horiz-degen-square (ap-o _ _ q)) (horiz-degen-square (ap-o _ _ p))
  apdo-ap-o f g id id = id

  apdo-ap-cube-hv : {A B C : Type} (f : A → B → C) {a a' : A} {b b' : B}
                   (p : a == a') (q : b == b') 
                   → Cube (ap-square (uncurry f) (pair-square (hrefl-square {p = p}) (vrefl-square {p = q})))
                           (apdo-ap f p q) 
                           (horiz-degen-square (ap-id-snd f p)) 
                           (horiz-degen-square (ap-id-fst f q)) 
                           (horiz-degen-square (ap-id-fst f q))
                           (horiz-degen-square (ap-id-snd f p)) 
  apdo-ap-cube-hv f id id = id

  -- should be a symmetry of the above
  apdo-ap-cube-vh : {A B C : Type} (f : A → B → C) {a a' : A} {b b' : B}
                   (p : a == a') (q : b == b') 
                   → Cube (ap-square (\ {(x , y) → f x y}) (pair-square (vrefl-square {p = p}) (hrefl-square {p = q})))
                           (square-symmetry (apdo-ap f p q))
                           (horiz-degen-square (ap-id-fst f q))
                           (horiz-degen-square (ap-id-snd f p))
                           (horiz-degen-square (ap-id-snd f p))
                           (horiz-degen-square (ap-id-fst f q))
  apdo-ap-cube-vh f id id = id

  apdo-ap'd : {A C : Type} {B : A → Type} (f : (x : A) → B x → C) {a a' : A} {b1 : (x : A) → B x} {b2 : (x : A) → B x}
                     (p : a == a') (q : b1 == b2) 
                   → Square (ap (λ y → f a (y a)) q)
                             (ap (λ z → f z (b1 z)) p)
                             (ap (λ z → f z (b2 z)) p)
                             (ap (λ y → f a' (y a')) q)
  apdo-ap'd f p q = PathOver=.out-PathOver-= (apdo (λ x → ap (λ y → f x (y x)) q) p)

{-
  bifunctor-on-cube : {A : Type} {B : A → Type} {C : Type}
                      (f : (x : A) → B x → C)
                      {a00 a01 a10 a11 : A} 
                      {p0- : a00 == a01}
                      {p-0 : a00 == a10}
                      {p-1 : a01 == a11}
                      {p1- : a10 == a11}
                      (s   : Square p0- p-0 p-1 p1-)
                      {b0 : (x : A) → B x}
                      {b1 : (x : A) → B x}
                      (pb : b0 == b1)
                    → Cube (apdo-ap'd f p0- pb)
                            (apdo-ap'd f p1- pb)
                            (apdo-ap'd f p-0 pb)
                            (ap-square (λ z → f z (b0 z)) s)
                            (ap-square (λ z → f z (b1 z)) s)
                            (apdo-ap'd f p-1 pb) 
  bifunctor-on-cube f s pb = SquareOver=ND.out-SquareOver-= (apdo-square (λ x → ap (λ y → f x (y x)) pb) s)
-}

  fill-cube-left : 
      {A : Type} 
      {a000 a010 a100 a110 a001 a011 a101 a111 : A}
      {p0-0 : a000 == a010}
      {p-00 : a000 == a100}
      {p-10 : a010 == a110}
      {p1-0 : a100 == a110}
  
      {p0-1 : a001 == a011}
      {p-01 : a001 == a101}
      {p-11 : a011 == a111}
      {p1-1 : a101 == a111}
      (f--1 : Square p0-1 p-01 p-11 p1-1) -- right
  
      {p00- : a000 == a001}
      {p01- : a010 == a011}
      {p10- : a100 == a101}
      {p11- : a110 == a111}
      (f0-- : Square p0-0 p00- p01- p0-1) -- back
      (f-0- : Square p-00 p00- p10- p-01) -- top
      (f-1- : Square p-10 p01- p11- p-11) -- bot
      (f1-- : Square p1-0 p10- p11- p1-1) -- front
      → Σ \ (f--0 : Square p0-0 p-00 p-10 p1-0) → 
            Cube f--0 f--1 f0-- f-0- f-1- f1--
  fill-cube-left {p-00 = id}  {p-10 = p-10} {p-01 = p-01} f--1 id f-0- f-1- id = 
    horiz-degen-square-induction1
      (λ {p-11} f-1- →
         (f-0-₁ : Square id id id p-01) (f--2 : Square id p-01 p-11 id) →
         Σ (λ f--0 → Cube f--0 f--2 id f-0-₁ f-1- id))
      (λ f-0- f--1 → horiz-degen-square-induction1
                       (λ {p-1} f-0- →
                          (f--1 : Square id p-1 p-10 id) →
                          Σ (λ f--0 → Cube f--0 f--1 id f-0- hrefl-square id))
                       (λ f--1 → f--1 , (degen-cube-h id)) f-0- f--1) f-1- f-0- f--1 


  ap-square-id! : {A : Type} {a00 a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
              (f   : Square p0- p-0 p-1 p1-)
              → Cube f (ap-square (\ x -> x) f)
                        (horiz-degen-square (! (ap-id p0-)))
                        (horiz-degen-square (! (ap-id p-0)))
                        (horiz-degen-square (! (ap-id p-1)))
                        (horiz-degen-square (! (ap-id p1-))) 
  ap-square-id! id = id

  ap-square-o : {A B C : Type} (g : B → C) (f : A → B) 
              {a00 a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
              (s   : Square p0- p-0 p-1 p1-)
              → Cube (ap-square (g o f) s) (ap-square g (ap-square f s)) (horiz-degen-square (ap-o g f p0-)) (horiz-degen-square (ap-o g f p-0)) (horiz-degen-square (ap-o g f p-1)) (horiz-degen-square (ap-o g f p1-))
  ap-square-o g f id = id

{- annoying to prove and not used
   ·-cube-horiz/degen : 
    {A : Type}
    {a000 a010 a100 a110 : A}

    {p0-0 : a000 == a010}
    {p-00 : a000 == a100}
    {p-10 : a010 == a110}
    {p1-0 : a100 == a110}
    {f--0 : Square p0-0 p-00 p-10 p1-0}

    {p0-1 : a000 == a010}
    {p-01 : a000 == a100}
    {p-11 : a010 == a110}
    {p1-1 : a100 == a110}
    {f--1 : Square p0-1 p-01 p-11 p1-1}

    {f0-- : p0-0 == p0-1}
    {f-0- : p-00 == p-01}
    {f-1- : p-10 == p-11}
    {f1-- : p1-0 == p1-1}

    {p0-2 : a000 == a010}
    {p-02 : a000 == a100}
    {p-12 : a010 == a110}
    {p1-2 : a100 == a110}
    {f--2 : Square p0-2 p-02 p-12 p1-2}

    {f0--' : p0-1 == p0-2}
    {f-0-' : p-01 == p-02}
    {f-1-' : p-11 == p-12}
    {f1--' : p1-1 == p1-2}

    → Cube f--0 f--1 (horiz-degen-square f0--) (horiz-degen-square f-0-) (horiz-degen-square f-1-) (horiz-degen-square f1--)
    → Cube f--1 f--2 (horiz-degen-square f0--') (horiz-degen-square f-0-') (horiz-degen-square f-1-') (horiz-degen-square f1--')
    → Cube f--0 f--2 (horiz-degen-square (f0--' ∘ f0--)) (horiz-degen-square (f-0-' ∘ f-0-)) (horiz-degen-square (f-1-' ∘ f-1-)) (horiz-degen-square (f1--' ∘ f1--))
--  ·-cube-horiz/degen = {!!} 

  _·-cube-h/degen_ = ·-cube-horiz/degen
  infixr 10 _·-cube-h/degen_

  cross-square-path-Σ : {A : Type} {B : A → Type} 
              {a00 a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
              (s   : Square p0- p-0 p-1 p1-)
              {b0 : (x : A) → B x}
              {b1 : (x : A) → B x}
              (pb : b0 == b1)
            → Cube {Σ B} {a00 , b0 a00} {a01 , b0 a01} {a10 , b0 a10} {a11 , b0 a11} 
                          {a00 , b1 a00} {a01 , b1 a01} {a10 , b1 a10} {a11 , b1 a11} 
                          {pair= p0- (apdo b0 p0-)} {pair= p-0 (apdo b0 p-0)}{pair= p-1 (apdo b0 p-1)}{pair= p1- (apdo b0 p1-)}
                          (ine SquareΣ-eqv-intro (s , apdo-square b0 s))
                          (ine SquareΣ-eqv-intro (s , apdo-square b1 s))
                          (PathOver=.out-PathOver-= (apdo (λ b → pair= p0- (apdo b p0-)) pb))
                          (PathOver=.out-PathOver-= (apdo (λ b → pair= p-0 (apdo b p-0)) pb))
                          (PathOver=.out-PathOver-= (apdo (λ b → pair= p-1 (apdo b p-1)) pb))
                          (PathOver=.out-PathOver-= (apdo (λ b → pair= p1- (apdo b p1-)) pb))
  cross-square-path-Σ id id = ?

  cross-square-path-Σ-compute : {A : Type} {B : A → Type} {C : Type}
            (f : (x : A) → B x → C)
            {a00 a01 a10 a11 : A} 
            {p0- : a00 == a01}
            {p-0 : a00 == a10}
            {p-1 : a01 == a11}
            {p1- : a10 == a11}
            (s   : Square p0- p-0 p-1 p1-)
            {b0 : (x : A) → B x}
            {b1 : (x : A) → B x}
            (pb : b0 == b1)
          → cube-symmetry-left-to-top (ap-cube (\ {(x , y) → f x y}) (operation s pb)) == 
             coe {!(square-symmetry
        (ap-square (λ xy → f (fst xy) (snd xy))
         (PathOver=.out-PathOver-=
          (apdo (λ b → pair= p0- (apdo b p0-)) pb)))) !} (bifunctor-on-cube f s pb)
  cross-square-path-Σ-compute = {!!}

-- Square (ap (λ y → f a00 (y a00)) pb)
--       (ap (λ z → f z (b0 z)) p0-) (ap (λ z → f z (b1 z)) p0-)
--       (ap (λ y → f a01 (y a01)) pb)

-- Square
--    (ap (λ xy → f (fst xy) (snd xy)) (ap (λ z → a00 , z a00) pb))
--    (ap (λ xy → f (fst xy) (snd xy)) (pair= p0- (apdo b0 p0-)))
--    (ap (λ xy → f (fst xy) (snd xy)) (pair= p0- (apdo b1 p0-)))
--    (ap (λ xy → f (fst xy) (snd xy)) (ap (λ z → a01 , z a01) pb))

  -- FIXME how do you get this from composition?

  fill-cube-top : 
      {A : Type} 
      {a000 a010 a100 a110 a001 a011 a101 a111 : A}
      {p0-0 : a000 == a010}
      {p-00 : a000 == a100}
      {p-10 : a010 == a110}
      {p1-0 : a100 == a110}
  
      {p0-1 : a001 == a011}
      {p-01 : a001 == a101}
      {p-11 : a011 == a111}
      {p1-1 : a101 == a111}
  
      {p00- : a000 == a001}
      {p01- : a010 == a011}
      {p10- : a100 == a101}
      {p11- : a110 == a111}
      (f--0 : Square p0-0 p-00 p-10 p1-0) -- left
      (f--1 : Square p0-1 p-01 p-11 p1-1) -- right
      (f0-- : Square p0-0 p00- p01- p0-1) -- back
      (f-1- : Square p-10 p01- p11- p-11) -- bot
      (f1-- : Square p1-0 p10- p11- p1-1) -- front
      → Σ \ (f-0- : Square p-00 p00- p10- p-01) -- top
          → Cube f--0 f--1 f0-- f-0- f-1- f1--

  fill-cube-back : 
      {A : Type} 
      {a000 a010 a100 a110 a001 a011 a101 a111 : A}
      {p0-0 : a000 == a010}
      {p-00 : a000 == a100}
      {p-10 : a010 == a110}
      {p1-0 : a100 == a110}
  
      {p0-1 : a001 == a011}
      {p-01 : a001 == a101}
      {p-11 : a011 == a111}
      {p1-1 : a101 == a111}
  
      {p00- : a000 == a001}
      {p01- : a010 == a011}
      {p10- : a100 == a101}
      {p11- : a110 == a111}
      (f--0 : Square p0-0 p-00 p-10 p1-0) -- left
      (f--1 : Square p0-1 p-01 p-11 p1-1) -- right
      (f-0- : Square p-00 p00- p10- p-01) -- top
      (f-1- : Square p-10 p01- p11- p-11) -- bot
      (f1-- : Square p1-0 p10- p11- p1-1) -- front
      → Σ \       (f0-- : Square p0-0 p00- p01- p0-1) -- back
          → Cube f--0 f--1 f0-- f-0- f-1- f1--

  CubeΣ-eqv : {A : Type} {B : A → Type} {a000 : Σ B}  
              {a010 a100 a110 a001 a011 a101 a111 : Σ B}
              {p0-0 : a000 == a010}
              {p-00 : a000 == a100}
              {p-10 : a010 == a110}
              {p1-0 : a100 == a110}
              {f--0 : Square p0-0 p-00 p-10 p1-0} -- left
              {p0-1 : a001 == a011}
              {p-01 : a001 == a101}
              {p-11 : a011 == a111}
              {p1-1 : a101 == a111}
              {f--1 : Square p0-1 p-01 p-11 p1-1} -- right
              {p00- : a000 == a001}
              {p01- : a010 == a011}
              {p10- : a100 == a101}
              {p11- : a110 == a111}
              {f0-- : Square p0-0 p00- p01- p0-1} -- back
              {f-0- : Square p-00 p00- p10- p-01} -- top
              {f-1- : Square p-10 p01- p11- p-11} -- bot
              {f1-- : Square p1-0 p10- p11- p1-1} -- front
              → Equiv (Cube f--0 f--1 f0-- f-0- f-1- f1--)
                      (Σ \ (c : Cube (fst (oute SquareΣ-eqv f--0)) (fst (oute SquareΣ-eqv f--1)) (fst (oute SquareΣ-eqv f0--)) (fst (oute SquareΣ-eqv f-0-)) (fst (oute SquareΣ-eqv f-1-)) (fst (oute SquareΣ-eqv f1--))) → 
                           CubeOver B c (snd (oute SquareΣ-eqv f--0)) (snd (oute SquareΣ-eqv f--1)) (snd (oute SquareΣ-eqv f0--)) (snd (oute SquareΣ-eqv f-0-)) (snd (oute SquareΣ-eqv f-1-)) (snd (oute SquareΣ-eqv f1--)))

  ap-bifunctor-square : {A C : Type} {B : A → Type} (f : (x : A) → B x → C) → 
                {a00 a01 a10 a11 : A} 
                {la : a00 == a01}
                {ta : a00 == a10}
                {ba : a01 == a11}
                {ra : a10 == a11}
                (fa   : Square la ta ba ra)
                → ∀ {b00 b01 b10 b11} →  
                {lb : PathOver B la b00 b01}
                {tb : PathOver B ta b00 b10}
                {bb : PathOver B ba b01 b11}
                {rb : PathOver B ra b10 b11}
                (fb   : SquareOver B fa lb tb bb rb)
                → Cube (ap-square (\ {(x , y) → f x y}) (ine SquareΣ-eqv-intro (fa , fb)))
                        (oute SquareOver-constant-eqv
                           (oute SquareOver-Π-eqv (apdo-square f fa) _ _ _ _ _ _ _ _ fb))
                        (horiz-degen-square (ap-bifunctor-pair= f _ lb)) (horiz-degen-square (ap-bifunctor-pair= f _ tb)) (horiz-degen-square (ap-bifunctor-pair= f _ bb)) (horiz-degen-square (ap-bifunctor-pair= f _ rb))
  ap-bifunctor-square f .id id = {!!}
-}
