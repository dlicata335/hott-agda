{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open import lib.cubical.Cubical

module misc.Idempotent 
  {X : Type}
  (f : X → X)
  (I : (x : X) → f (f x) == f x)
  (J : (x : X) → ap f (I x) == I (f x))
  where

  A = Σ \ (x : X) → Σ \ (p : f x == x) → ap f p == I x

  r : X → A
  r x = f x , I x , J x

  s : A → X
  s = fst

  is-f : s o r == f
  is-f = id

  identh : (x : A) → r(s x) == x 
  identh (x' , p' , q') = 
    pair= p' (pair=o (PathOver=.in-PathOver-= square1) 
                     (PathOver=D.in-PathOver-= (SquareOver=ND.in-SquareOver-= cube1))) where
  
    thing : Cube (horiz-degen-square (! (ap (ap f) q')))
                 (horiz-degen-square (J (f x')))
                 {!J (f x')!}
                 (vertical-degen-square {!!}) 
                 (vertical-degen-square {!!})
                 {!!}
    thing = {!!}

    square1-and-cube : _
    square1-and-cube = 
      fill-cube-back
        (horiz-degen-square (! q'))
        hrefl-square
        vrefl-square 
        (vertical-degen-square (ap-id p')) 
        connection2

    square1 : Square (I x') (ap (λ z → f z) p') (ap (λ z → z) p') p'
    square1 = fst square1-and-cube

    cube4 : Cube (horiz-degen-square (J x'))
                 (horiz-degen-square q')
                 {! ap-square f square1 !}
                 (vrefl-square {p = ap (f o f) p'})
                 (vrefl-square {p = ap f p'})
                 (PathOver=.out-PathOver-= (apdo (λ x → I x) p'))
    cube4 = {!ap-cube f (snd square1-and-cube)!}

    cube3 : Cube (horiz-degen-square (J x'))
                 (horiz-degen-square q')
                 {! ap-square f square1 !}
                 (ap-square (f o f) (vrefl-square {p = p'}))
                 (ap-square (λ z → f z) (vrefl-square {p = p'}))
                 (PathOver=.out-PathOver-= (apdo (λ x → I x) p'))
    cube3 = {!ap-cube f (snd square1-and-cube)!}

    cube2 : Cube (horiz-degen-square (J x'))
                 (horiz-degen-square q')
                 (PathOver=.out-PathOver-=
                   (apdo (λ x → ap f (snd x))
                     (pair= p' (PathOver=.in-PathOver-= square1))))
                 (ap-square (λ z → f (f (fst z))) vrefl-square)
                 (ap-square (λ z → f (fst z)) vrefl-square)
                 (PathOver=.out-PathOver-=
                   (apdo (λ x → I (fst x))
                     (pair= p' (PathOver=.in-PathOver-= square1))))
    cube2 = {!(PathOver=.out-PathOver-=
                   (apdo (λ x → ap f (snd x))
                     (pair= p' (PathOver=.in-PathOver-= square1))))!}

    red1 : _ -- Id (horiz-degen-square (J x')) (PathOver=.out-PathOver-= (hom-to-over/left id (J x')))
    red1 = {!!}

    red2 : Cube (ap-square (λ z → f (fst z)) (vrefl-square {p = (pair= p' (PathOver=.in-PathOver-= square1))}))
                (ap-square f (vrefl-square{p = p'}))
                _ _ _ _ 
    red2 = {!!}

    cube1 : _
    cube1 = whisker-cube red1 {!red1 same lemma!} {!!} {!!} {!!} {!!} cube2



  ident : r o s == (\ x -> x)
  ident = λ≃ identh


