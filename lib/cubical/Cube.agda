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
                   (PathOverPathFrom.in-PathOver-=' (∘-square-vertical f-0- f1--))
                   (PathOverPathFrom.in-PathOver-=' {p0- = p0-1 ∘ p00- } {p-0 = p00- } {p-1 = p-11} {p1- = p1-1 ∘ p-01}
                                   (∘-square-vertical connection2 f--1))
      
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

  
  module SquareOver=ND where

    open PathOver=

    postulate
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

  postulate
    PathOver-square/= : {Γ A : Type} {x1 x2 : Γ} (δ : x1 == x2) {a00 a01 a10 a11 : Γ → A} 
                          {p0- : (x : Γ) → a00 x == a01 x}
                          {p-0 : (x : Γ) → a00 x == a10 x }
                          {p-1 : (x : Γ) → a01 x == a11 x }
                          {p1- : (x : Γ) → a10 x == a11 x }
                          (f1   : Square (p0- x1) (p-0 x1) (p-1 x1) (p1- x1))
                       → (f2 : Square (p0- x2) (p-0 x2) (p-1 x2) (p1- x2))
                       →     (PathOver (\ x -> Square (p0- x) (p-0 x) (p-1 x) (p1- x)) δ f1 f2)
                           == (Cube f1 f2 (PathOver=.out-PathOver-= (apdo p0- δ)) (PathOver=.out-PathOver-= (apdo p-0 δ)) (PathOver=.out-PathOver-= (apdo p-1 δ)) (PathOver=.out-PathOver-= (apdo p1- δ)))
