
{-# OPTIONS --without-K --type-in-type #-}

open import lib.Prelude
open import lib.cubical.Cubical

module programming.PatchWithHistories where

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

  ex-front : ∀ {a'} x y xs (c : a' == doc xs) → Square
      (add x (y ::ms xs) ∘ add y xs ∘ c)
      id 
      (ap doc (Ex x y xs))
      (add y (x ::ms xs) ∘ add x xs ∘ c)
  ex-front x y xs c = coe (ap2 (λ x₁ y₁ → Square x₁ id (ap doc (Ex x y xs)) y₁) 
                                 (! (∘-assoc (add x (y ::ms xs)) (add y xs) c))
                                 (! (∘-assoc (add y (x ::ms xs)) (add x xs) c))) (extend-triangle (ex y x xs) c)


  topath-Ex-case = (λ x y xs c → over-ap-o (λ r → doc []ms == r) {θ1 = doc} (in-PathOver-= (ex-front x y xs c))) 

  topath : (xs : MS) → doc []ms == doc xs
  topath = MS-ind (\ xs -> doc []ms == doc xs) id (λ x xs p → add x xs ∘ p) topath-Ex-case
                  

  topath-square : (x : Bool) (xs : MS) →
                       PathOver (λ x₁ → doc []ms == x₁) (add x xs) (topath xs)
                       (topath (x ::ms xs))
  topath-square x xs = in-PathOver-= ∘-square 


  contr : (x : R) → doc []ms == x
  contr = R-elim (\ x -> doc []ms == x) topath topath-square 
                 (λ x y xs → SquareOver-= _ _ _ _ _ goal1) where
        goal1 : ∀ {x y xs} → Cube
                (out-PathOver-= (topath-square y (x ::ms xs) ∘o topath-square x xs))
                (out-PathOver-= (topath-square x (y ::ms xs) ∘o topath-square y xs))
                (out-PathOver-= id)
                id
                (ex x y xs)
                (out-PathOver-= (over-o-ap (λ x₁ → doc []ms == x₁) (apdo topath (Ex y x xs))))
        goal1{x}{y}{xs} = transport
                            (Cube (out-PathOver-= (topath-square y (x ::ms xs) ∘o topath-square x xs)) (out-PathOver-= (topath-square x (y ::ms xs) ∘o topath-square y xs)) (out-PathOver-= id) id (ex x y xs))
                            (! (out-PathOver-= (over-o-ap (_==_ (doc []ms)) (apdo topath (Ex y x xs))) ≃〈 ap (λ h → out-PathOver-= (over-o-ap (_==_ (doc []ms)) h)) (MS-ind/βEx (λ xs₁ → doc []ms == doc xs₁) id (λ x₁ xs₁ p → add x₁ xs₁ ∘ p) topath-Ex-case y x xs) 〉
                                out-PathOver-= (over-o-ap (_==_ (doc []ms)) (topath-Ex-case y x xs (topath xs))) ≃〈 ap out-PathOver-= (IsEquiv.β (snd (over-o-ap-eqv (λ x₁ → doc []ms == x₁))) (in-PathOver-= (ex-front y x xs (topath xs)))) 〉
                                out-PathOver-= (in-PathOver-= (ex-front y x xs (topath xs))) ≃〈 PathOver-=-outin (ex-front y x xs (topath xs)) 〉
                                ex-front y x xs (topath xs) ∎))
                            goal2 where
 
         -- reduce apdo topath and cancel some equivalences
 
         goal2 : ∀ {x y xs} → Cube
                 (out-PathOver-= (topath-square y (x ::ms xs) ∘o topath-square x xs))
                 (out-PathOver-= (topath-square x (y ::ms xs) ∘o topath-square y xs))
                 (out-PathOver-= id)
                 id
                 (ex x y xs)
                 (ex-front y x xs (topath xs))
         goal2 = goal3 where
           -- out-PathOver-= on id is horizontal reflexivity

          goal3 : ∀ {x y xs} → Cube
                  (out-PathOver-= (topath-square y (x ::ms xs) ∘o topath-square x xs))
                  (out-PathOver-= (topath-square x (y ::ms xs) ∘o topath-square y xs))
                  hrefl-Square
                  id
                  (ex x y xs)
                  (ex-front y x xs (topath xs))
          goal3 = goal4 where
  
           -- expand definition of ex-front

           goal4 : ∀ {x y xs} → Cube
                   (out-PathOver-= (topath-square y (x ::ms xs) ∘o topath-square x xs))
                   (out-PathOver-= (topath-square x (y ::ms xs) ∘o topath-square y xs))
                   hrefl-Square
                   id
                   (ex x y xs)
                   (coe
                      (ap2 (λ x₁ y₁ → Square x₁ id (ap doc (Ex y x xs)) y₁)
                       (! (∘-assoc (add y (x ::ms xs)) (add x xs) (topath xs)))
                       (! (∘-assoc (add x (y ::ms xs)) (add y xs) (topath xs))))
                      (extend-triangle (ex x y xs) (topath xs)))
           goal4{x}{y}{xs} = transport (λ x' → Cube x' (out-PathOver-= (topath-square x (y ::ms xs) ∘o topath-square y xs)) hrefl-Square id (ex x y xs) (coe (ap2 (λ x₁ y₁ → Square x₁ id (ap doc (Ex y x xs)) y₁) (! (∘-assoc (add y (x ::ms xs)) (add x xs) (topath xs))) (! (∘-assoc (add x (y ::ms xs)) (add y xs) (topath xs)))) (extend-triangle (ex x y xs) (topath xs)))) 
                                       ∘-square-lemma goal5 where
   
            -- composite of ∘-squares is ∘-square of composite

            -- FIXME: try doing this directly in terms of squares/cubes and then translate it to path-overs
            -- 
            -- it says that if you have
            --   ∘-square p q : Square p id q (q ∘ p)
            --   ∘-square (q ∘ p) r : Square (\q ∘ p) id r (r ∘ (q ∘ p))
            -- then horizontally composing them is the same as 
            --   ∘-square p (r ∘ q) : Square p id (r ∘ q) ((r ∘ q) ∘ r)
            -- up to associativity
            -- which is basically the definition of associativity if you did everything with fillers?
            --
            -- the coe could be phrased as path over, too
            ∘-square-lemma : {A : Type} {a0 a1 a2 a3 : A} {p01 : a0 == a1} {p12 : a1 == a2} {p23 : a2 == a3}
                           → (coe (ap (Square p01 id (p23 ∘ p12)) (! (∘-assoc p23 p12 p01))) (∘-square {p = p01} {q = p23 ∘ p12}))
                             == (out-PathOver-= (in-PathOver-= (∘-square {p = p12 ∘ p01} {q = p23}) ∘o (in-PathOver-= (∘-square{p = p01}{q = p12})))) 
            ∘-square-lemma {p01 = id} {p12 = id} {p23 = id} = id

            goal5 : ∀ {x y xs} → Cube
                    (coe (ap (λ h → Square (topath xs) id (add y (x ::ms xs) ∘ add x xs) h) (! (∘-assoc (add y (x ::ms xs)) (add x xs) (topath xs))))
                         (∘-square {p = topath xs} {q = add y (x ::ms xs) ∘ add x xs}))
                    (out-PathOver-= (topath-square x (y ::ms xs) ∘o topath-square y xs))
                    hrefl-Square
                    id
                    (ex x y xs)
                    (coe
                       (ap2 (λ x₁ y₁ → Square x₁ id (ap doc (Ex y x xs)) y₁)
                        (! (∘-assoc (add y (x ::ms xs)) (add x xs) (topath xs)))
                        (! (∘-assoc (add x (y ::ms xs)) (add y xs) (topath xs))))
                       (extend-triangle (ex x y xs) (topath xs)))
            goal5{x}{y}{xs} = transport (\ h -> Cube (coe (ap (λ h → Square (topath xs) id (add y (x ::ms xs) ∘ add x xs) h) (! (∘-assoc (add y (x ::ms xs)) (add x xs) (topath xs)))) (∘-square {p = topath xs} {q = add y (x ::ms xs) ∘ add x xs})) h hrefl-Square id (ex x y xs) (coe (ap2 (λ x₁ y₁ → Square x₁ id (ap doc (Ex y x xs)) y₁) (! (∘-assoc (add y (x ::ms xs)) (add x xs) (topath xs))) (! (∘-assoc (add x (y ::ms xs)) (add y xs) (topath xs)))) (extend-triangle (ex x y xs) (topath xs))))
                                        ∘-square-lemma goal6 where
     
             -- composite of ∘-squares is ∘-square of composite

             goal6 : ∀ {x y xs} → Cube
                     (coe (ap (λ h → Square (topath xs) id (add y (x ::ms xs) ∘ add x xs) h) (! (∘-assoc (add y (x ::ms xs)) (add x xs) (topath xs))))
                          (∘-square {p = topath xs} {q = add y (x ::ms xs) ∘ add x xs}))
                     (coe (ap (λ h → Square (topath xs) id (add x (y ::ms xs) ∘ add y xs) h) (! (∘-assoc (add x (y ::ms xs)) (add y xs) (topath xs))))
                          (∘-square {p = topath xs} {q = add x (y ::ms xs) ∘ add y xs}))
                     (hrefl-Square{_}{_}{_}{topath xs})
                     id
                     (ex x y xs)
                     (coe
                        (ap2 (λ x₁ y₁ → Square x₁ id (ap doc (Ex y x xs)) y₁)
                         (! (∘-assoc (add y (x ::ms xs)) (add x xs) (topath xs)))
                         (! (∘-assoc (add x (y ::ms xs)) (add y xs) (topath xs))))
                        (extend-triangle (ex x y xs) (topath xs)))
             goal6 = {!    !} where
     
              -- remove all the reassociating, hopefully consistently

              goal7 : ∀ {x y xs} → Cube
                      (∘-square {p = topath xs} {q = add y (x ::ms xs) ∘ add x xs})
                      (∘-square {p = topath xs} {q = add x (y ::ms xs) ∘ add y xs})
                      (hrefl-Square{_}{_}{_}{topath xs})
                      id
                      (ex x y xs)
                      (extend-triangle (ex x y xs) (topath xs))
              goal7 {xs = xs} = goal8a {p = topath xs} where
      
                -- abstract

                goal8a : ∀ {x y xs} {a' : _} {p : a' == doc xs} → Cube
                        (∘-square {p = p} {q = add y (x ::ms xs) ∘ add x xs})
                        (∘-square {p = p} {q = add x (y ::ms xs) ∘ add y xs})
                        hrefl-Square
                        id
                        (ex x y xs)
                        (extend-triangle (ex x y xs) p)
                goal8a {p = id} = goal8 where
          
                  -- path-induction 

                  goal8 : ∀ {x y xs} → Cube
                          (∘-square {p = id} {q = add y (x ::ms xs) ∘ add x xs})
                          (∘-square {p = id} {q = add x (y ::ms xs) ∘ add y xs})
                          hrefl-Square
                          id
                          (ex x y xs)
                          (ex x y xs)
                  goal8 = goal9 where
        
                   -- cleanup: hrefl-Square on id is id, ∘-square on {p=id} is connection

                   goal9 : ∀ {x y xs} → Cube
                           (connection {p = add y (x ::ms xs) ∘ add x xs})
                           (connection {p = add x (y ::ms xs) ∘ add y xs})
                           id
                           id
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
                        → Cube (connection { p = p0- }) (connection { p = p1- }) vrefl-Square vrefl-Square f f 
                    goal10 id = id
