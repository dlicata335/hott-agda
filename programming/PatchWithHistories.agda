
{-# OPTIONS --new-without-K --type-in-type #-}

open import lib.Prelude
open import lib.PathOver using (PathOver; id ; _∘o_ ; apdo ; over-o-ap)

module programming.PatchWithHistories where

  data Square {A : Type} {a00 : A} : 
              {a01 a10 a11 : A} → a00 == a01 -> a00 == a10 -> a01 == a11 -> a10 == a11 -> Type where 
    idSquare : Square id id id id


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
    → Square p0-0 p00- p01- p0-1
    → Square p-00 p00- p10- p-01
    → Square p-10 p01- p11- p-11
    → Square p1-0 p10- p11- p1-1
    → Type where
    idCube : Cube idSquare idSquare idSquare idSquare idSquare idSquare
    

  data SquareOver {A : Type} (B : A → Type) {a00 : A} {b00 : B a00} : 
              {a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
              (f   : Square p0- p-0 p-1 p1-)
              {b01 : B a01} {b10 : B a10} {b11 : B a11}  
              (q0- : PathOver B p0- b00 b01)
              (q-0 : PathOver B p-0 b00 b10)
              (q-1 : PathOver B p-1 b01 b11)
              (q1- : PathOver B p1- b10 b11) → Type where
    idSquareOver : SquareOver B idSquare id id id id


  postulate 
    MS : Type
    []ms : MS
    _::ms_ : Bool → MS → MS
    Ex : (x y : Bool) (xs : MS) → (x ::ms (y ::ms xs)) == (y ::ms (x ::ms xs))

    R : Type
    doc : MS → R
    add : (x : Bool) (xs : MS) → doc xs == doc (x ::ms xs)
    ex  : (x y : Bool) (xs : MS) → 
        Square (add y (x ::ms xs) ∘ add x xs) id (ap doc (Ex y x xs)) (add x (y ::ms xs) ∘ add y xs)
    R-elim : (C : R → Type)
           → (c0 : (xs : MS) → C (doc xs))
           → (c1 : (x : Bool) (xs : MS) → PathOver C (add x xs) (c0 xs) (c0 (x ::ms xs)))
           → (c2 : (x y : Bool) (xs : MS) → 
                   SquareOver C (ex x y xs) 
                                (c1 y (x ::ms xs) ∘o c1 x xs)
                                id 
                                (over-o-ap C (apdo c0 (Ex y x xs)))
                                (c1 x (y ::ms xs) ∘o c1 y xs) )
           → (x : R) → C x

    topath : (xs : MS) → doc []ms == doc xs
    topath-square : (x : Bool) (xs : MS) →
                    PathOver (λ x₁ → doc []ms == x₁) (add x xs) (topath xs)
                    (topath (x ::ms xs))

  -- should be an equivalence
  in-PathOver-= : {A : Type} {a' : A} 
             → {a0 a1 : A}
             → {p : a0 == a1}
             → {q0 : a' == a0}
             → {q1 : a' == a1}
             → Square q0 id p q1
             → PathOver (\ x -> a' == x) p q0 q1 
  in-PathOver-= = {!!}

  out-PathOver-= : {A : Type} {a' : A} 
             → {a0 a1 : A}
             → {p : a0 == a1}
             → {q0 : a' == a0}
             → {q1 : a' == a1}
             → PathOver (\ x -> a' == x) p q0 q1 
             → Square q0 id p q1
  out-PathOver-= {q0 = id} id = idSquare

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
                 → Cube (out-PathOver-= q0-) (out-PathOver-= q1-) (out-PathOver-= q-0) idSquare f (out-PathOver-= q-1)
                 → SquareOver (\ x -> a' == x) f 
                              q0-
                              q-0
                              q-1
                              q1-
  SquareOver-= = {!!}

  contr : (x : R) → doc []ms == x
  contr = R-elim (\ x -> doc []ms == x) topath topath-square 
                 (λ x y xs → SquareOver-= _ _ _ _ _ {!!}) 
    
  
    
