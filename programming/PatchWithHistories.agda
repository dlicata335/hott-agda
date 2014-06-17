
{-# OPTIONS --new-without-K --type-in-type #-}

open import lib.Prelude
open import lib.PathOver using (PathOver; id ; _∘o_ ; apdo ; over-o-ap)

module programming.PatchWithHistories where

  data Square {A : Type} {a00 : A} : 
              {a01 a10 a11 : A} → a00 == a01 -> a00 == a10 -> a01 == a11 -> a10 == a11 -> Type where 
    idSquare : Square id id id id

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


  contr : (x : R) → doc []ms == x
  contr = R-elim (\ x -> doc []ms == x) topath topath-square 
                 (λ x y xs → {!!}) 
    
  
    
