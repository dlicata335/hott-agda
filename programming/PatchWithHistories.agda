
{-# OPTIONS --without-K --type-in-type #-}

open import lib.Prelude
open import lib.PathOver using (PathOver; id ; _∘o_ ; apdo ; over-o-ap ; over-ap-o)

module programming.PatchWithHistories where

  data Square {A : Type} {a00 : A} : 
              {a01 a10 a11 : A} → a00 == a01 -> a00 == a10 -> a01 == a11 -> a10 == a11 -> Type where 
    idSquare : Square id id id id

  hrefl-Square : {A : Type} {a00 a01 : A} {p : a00 == a01} → Square p id id p
  hrefl-Square {p = id} = idSquare

  vrefl-Square : {A : Type} {a00 a01 : A} {p : a00 == a01} → Square id p p id
  vrefl-Square {p = id} = idSquare

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


  module HistoryHIT where

    private 
      data MS' : Type where
        []ms' : MS'
        _::ms'_ : Bool → MS' → MS'

    MS = MS'
    []ms = []ms'
    _::ms_ = _::ms'_

    postulate 
      Ex : (x y : Bool) (xs : MS) → (x ::ms (y ::ms xs)) == (y ::ms (x ::ms xs))

    MS-ind : (C : MS → Type) 
           → (c0 : C []ms)
           → (c1 : (x : _) (xs : _) → C xs → C (x ::ms xs))
           → (c2 : (x y : _) (xs : _) (c : _) → PathOver C (Ex x y xs) (c1 x (y ::ms' xs) (c1 y xs c)) (c1 y (x ::ms' xs) (c1 x xs c)))
           → (xs : MS) → C xs
    MS-ind C c0 c1 c2 []ms' = c0
    MS-ind C c0 c1 c2 (x ::ms' xs) = c1 x xs (MS-ind C c0 c1 c2 xs)

    postulate 
      MS-ind/βEx : (C : MS → Type) 
                 → (c0 : C []ms)
                 → (c1 : (x : _) (xs : _) → C xs → C (x ::ms xs))
                 → (c2 : (x y : _) (xs : _) (c : _) → PathOver C (Ex x y xs) (c1 x (y ::ms' xs) (c1 y xs c)) (c1 y (x ::ms' xs) (c1 x xs c)))
                 → (x y : _) (xs : _) 
                 → apdo (MS-ind C c0 c1 c2) (Ex x y xs) == c2 x y xs (MS-ind C c0 c1 c2 xs)

  open HistoryHIT 

  postulate
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

  extend-triangle : {A : Type} {a00 a01 a11 : A}
              {p0- : a00 == a01}
              {p-1 : a01 == a11}
              {p1- : a00 == a11}
              (f   : Square p0- id p-1 p1-)
              → {a00' : A} (p : a00' == a00) 
              → Square (p0- ∘ p) id p-1 (p1- ∘ p)
  extend-triangle f id = f

  ex-front : ∀ {a'} x y xs {c : a' == doc xs } → Square
      (add x (y ::ms xs) ∘ add y xs ∘ c)
      id 
      (ap doc (Ex x y xs))
      (add y (x ::ms xs) ∘ add x xs ∘ c)
  ex-front x y xs {c} = coe (ap2 (λ x₁ y₁ → Square x₁ id (ap doc (Ex x y xs)) y₁) 
                                 (! (∘-assoc (add x (y ::ms xs)) (add y xs) c))
                                 (! (∘-assoc (add y (x ::ms xs)) (add x xs) c))) (extend-triangle (ex y x xs) c)

  topath : (xs : MS) → doc []ms == doc xs
  topath = MS-ind (\ xs -> doc []ms == doc xs) id (λ x xs p → add x xs ∘ p) 
                  (λ x y xs c → over-ap-o (λ r → doc []ms == r) {θ1 = doc} (in-PathOver-= (ex-front x y xs)))
  
  ∘-square : {A : Type} {a0 a1 a2 : A} {p : a0 == a1} {q : a1 == a2} 
           → Square p id q (q ∘ p)
  ∘-square {p = id} {q = id} = idSquare

  topath-square : (x : Bool) (xs : MS) →
                       PathOver (λ x₁ → doc []ms == x₁) (add x xs) (topath xs)
                       (topath (x ::ms xs))
  topath-square x xs = in-PathOver-= ∘-square 

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

  connection : ∀ {A} {a b : A} {p : a == b} → Square id id p p 
  connection {p = id} = idSquare

  contr : (x : R) → doc []ms == x
  contr = R-elim (\ x -> doc []ms == x) topath topath-square 
                 (λ x y xs → SquareOver-= _ _ _ _ _ goal1) where
        goal1 : ∀ {x y xs} → Cube
                (out-PathOver-= (topath-square y (x ::ms xs) ∘o topath-square x xs))
                (out-PathOver-= (topath-square x (y ::ms xs) ∘o topath-square y xs))
                (out-PathOver-= id)
                idSquare
                (ex x y xs)
                (out-PathOver-= (over-o-ap (λ x₁ → doc []ms == x₁) (apdo topath (Ex y x xs))))
        goal1 = {!!}

        -- reduce apdo topath and cancel some equivalences
        goal2 : ∀ {x y xs} → Cube
                (out-PathOver-= (topath-square y (x ::ms xs) ∘o topath-square x xs))
                (out-PathOver-= (topath-square x (y ::ms xs) ∘o topath-square y xs))
                (out-PathOver-= id)
                idSquare
                (ex x y xs)
                (ex-front y x xs {topath xs})
        goal2 = {!!}

        -- out-PathOver-= on id should be horizontal reflexivity
        goal3 : ∀ {x y xs} → Cube
                (out-PathOver-= (topath-square y (x ::ms xs) ∘o topath-square x xs))
                (out-PathOver-= (topath-square x (y ::ms xs) ∘o topath-square y xs))
                hrefl-Square
                idSquare
                (ex x y xs)
                (ex-front y x xs {topath xs})
        goal3 = {!!}

        -- expand definition of ex-front
        goal4 : ∀ {x y xs} → Cube
                (out-PathOver-= (topath-square y (x ::ms xs) ∘o topath-square x xs))
                (out-PathOver-= (topath-square x (y ::ms xs) ∘o topath-square y xs))
                hrefl-Square
                idSquare
                (ex x y xs)
                (coe
                   (ap2 (λ x₁ y₁ → Square x₁ id (ap doc (Ex y x xs)) y₁)
                    (! (∘-assoc (add y (x ::ms xs)) (add x xs) (topath xs)))
                    (! (∘-assoc (add x (y ::ms xs)) (add y xs) (topath xs))))
                   (extend-triangle (ex x y xs) (topath xs)))
        goal4 = {!!}

        -- composite of ∘-squares should be ∘-square of composite
        goal5 : ∀ {x y xs} → Cube
                (coe (ap (λ h → Square (topath xs) id (add y (x ::ms xs) ∘ add x xs) h) (! (∘-assoc (add y (x ::ms xs)) (add x xs) (topath xs))))
                     (∘-square {p = topath xs} {q = add y (x ::ms xs) ∘ add x xs}))
                (out-PathOver-= (topath-square x (y ::ms xs) ∘o topath-square y xs))
                hrefl-Square
                idSquare
                (ex x y xs)
                (coe
                   (ap2 (λ x₁ y₁ → Square x₁ id (ap doc (Ex y x xs)) y₁)
                    (! (∘-assoc (add y (x ::ms xs)) (add x xs) (topath xs)))
                    (! (∘-assoc (add x (y ::ms xs)) (add y xs) (topath xs))))
                   (extend-triangle (ex x y xs) (topath xs)))
        goal5 = {!!}

        -- composite of ∘-squares should be ∘-square of composite
        goal6 : ∀ {x y xs} → Cube
                (coe (ap (λ h → Square (topath xs) id (add y (x ::ms xs) ∘ add x xs) h) (! (∘-assoc (add y (x ::ms xs)) (add x xs) (topath xs))))
                     (∘-square {p = topath xs} {q = add y (x ::ms xs) ∘ add x xs}))
                (coe (ap (λ h → Square (topath xs) id (add x (y ::ms xs) ∘ add y xs) h) (! (∘-assoc (add x (y ::ms xs)) (add y xs) (topath xs))))
                     (∘-square {p = topath xs} {q = add x (y ::ms xs) ∘ add y xs}))
                hrefl-Square
                idSquare
                (ex x y xs)
                (coe
                   (ap2 (λ x₁ y₁ → Square x₁ id (ap doc (Ex y x xs)) y₁)
                    (! (∘-assoc (add y (x ::ms xs)) (add x xs) (topath xs)))
                    (! (∘-assoc (add x (y ::ms xs)) (add y xs) (topath xs))))
                   (extend-triangle (ex x y xs) (topath xs)))
        goal6 = {!!}

        -- remove all the reassociating, hopefully consistently
        goal7 : ∀ {x y xs} → Cube
                (∘-square {p = topath xs} {q = add y (x ::ms xs) ∘ add x xs})
                (∘-square {p = topath xs} {q = add x (y ::ms xs) ∘ add y xs})
                hrefl-Square
                idSquare
                (ex x y xs)
                (extend-triangle (ex x y xs) (topath xs))
        goal7 {xs = xs} = goal8a {p = topath xs} where

          -- remove all the reassociating, hopefully consistently
          goal8a : ∀ {x y xs} {a' : _} {p : a' == doc xs} → Cube
                  (∘-square {p = p} {q = add y (x ::ms xs) ∘ add x xs})
                  (∘-square {p = p} {q = add x (y ::ms xs) ∘ add y xs})
                  hrefl-Square
                  idSquare
                  (ex x y xs)
                  (extend-triangle (ex x y xs) p)
          goal8a {p = id} = goal8 where
    
            -- abstract topath xs and then path-induction on topath xs
            goal8 : ∀ {x y xs} → Cube
                    (∘-square {p = id} {q = add y (x ::ms xs) ∘ add x xs})
                    (∘-square {p = id} {q = add x (y ::ms xs) ∘ add y xs})
                    hrefl-Square
                    idSquare
                    (ex x y xs)
                    (ex x y xs)
            goal8 = {!!}
  
        -- cleanup, based on things that should be true
        goal9 : ∀ {x y xs} → Cube
                (connection {p = add y (x ::ms xs) ∘ add x xs})
                (connection {p = add x (y ::ms xs) ∘ add y xs})
                idSquare
                idSquare
                (ex x y xs)
                (ex x y xs)
        goal9 {x}{y}{xs} = goal10 (ex x y xs) where
          goal10 : ∀ {A}
              {a00 a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
              (f   : Square p0- p-0 p-1 p1-)
              → Cube (connection {p = p0-}) (connection {p = p1-}) vrefl-Square vrefl-Square f f 
          goal10 idSquare = idCube
                     


    
  
    
