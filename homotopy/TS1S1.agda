{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open import lib.cubical.Cubical

module homotopy.TS1S1 where

  open S¹ using (S¹ ; S¹-rec ; S¹-elimo)
  module T = Torus
  open T using (T ; T-rec ; T-elim)

  -- FIXME move to lib

  ap-uncurry' : {A B C : Type} → (f : A → B → C) {a1 a2 : A} (p1 : a1 == a2) {b1 b2 : B} (p2 : b1 == b2)
             → ap (\ {(x , y) → (f x) y}) (pair×≃ p1 p2) == ap≃₁→ (ap f p1) p2
  ap-uncurry' f id id = id

  ap≃₁→-id-fn : {A B : Type} (f : A → B) {x y : A} → (p : x ≃ y) → (ap≃₁→ id p) == ap f p
  ap≃₁→-id-fn f id = id

  ap≃₁→-id-arg : {A B : Type} {f g : A → B} {x : A} → (p : f ≃ g) → (ap≃₁→ p (id{_}{x})) == ap≃ p
  ap≃₁→-id-arg id = id


  ap-square-id! : {A : Type} {a00 a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
              (f   : Square p0- p-0 p-1 p1-)
              → Cube f (ap-square (\ x -> x) f) (horiz-degen-square (! (ap-id p0-))) (horiz-degen-square (! (ap-id p-0))) (horiz-degen-square (! (ap-id p-1))) (horiz-degen-square (! (ap-id p1-))) 
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

  ap-square-horiz-degen : {A B : Type} (f : A → B) {a1 a2 : A} {p q : a1 == a2} (r : p == q)
                  → ap-square f (horiz-degen-square r) == horiz-degen-square (ap (ap f) r)
  ap-square-horiz-degen _ {p = id} id = id

  apdo-by-equals :
    {Δ : Type} {A : Δ → Type} (f g : (θ : _) → A θ) {θ1 θ2 : Δ} (δ : θ1 == θ2) 
    (p : f == g)
    → SquareOver A hrefl-square (apdo f δ) (hom-to-over/left id (ap≃ p)) (hom-to-over/left id (ap≃ p)) (apdo g δ) 
  apdo-by-equals f .f id id = id

  ∘-cube-horiz/degen : 
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
  ∘-cube-horiz/degen = {!!} 

  _∘-cube-h/degen_ = ∘-cube-horiz/degen
  infixr 10 _∘-cube-h/degen_

  -- ap to inner argument first
  -- could do it in the other order, too
  bifunctor-square1 : {A B C : Type} (f : A → B → C) {a a' : A} {b b' : B}
                     (p : a == a') (q : b == b') 
                   → Square (ap (λ x → f x b) p)
                             (ap (λ z → f a z) q)
                             (ap (λ z → f a' z) q)
                             (ap (λ x → f x b') p)
  bifunctor-square1 f p q = PathOver=.out-PathOver-= (apdo (λ y → ap (λ x → f x y) p) q)

  ap-bifunctor-id-1 : {A B C : Type} (f : A → B → C) {a : A} {b b' : B}
                      (q : b == b') 
                    → ap (uncurry f) (pair×≃ id q) == ap (f a) q
  ap-bifunctor-id-1 f id = id

  ap-bifunctor-id-2 : {A B C : Type} (f : A → B → C) {a a' : A} {b : B}
                      (p : a == a') 
                    → ap (uncurry f) (pair×≃ p id) == ap (\ x -> f x b) p
  ap-bifunctor-id-2 f id = id

  bifunctor-cube1 : {A B C : Type} (f : A → B → C) {a a' : A} {b b' : B}
                   (p : a == a') (q : b == b') 
                   → Cube (ap-square (\ {(x , y) → f x y}) (pair-square (vrefl-square {p = p}) (hrefl-square {p = q})))
                           (square-symmetry (bifunctor-square1 f p q))
                           (horiz-degen-square (ap-bifunctor-id-1 f q))
                           (horiz-degen-square (ap-bifunctor-id-2 f p))
                           (horiz-degen-square (ap-bifunctor-id-2 f p))
                           (horiz-degen-square (ap-bifunctor-id-1 f q))
  bifunctor-cube1 f id id = id

  -- should be a symmetry of the above
  bifunctor-cube1' : {A B C : Type} (f : A → B → C) {a a' : A} {b b' : B}
                   (p : a == a') (q : b == b') 
                   → Cube (ap-square (uncurry f) (pair-square (hrefl-square {p = p}) (vrefl-square {p = q})))
                           (bifunctor-square1 f p q) 
                           (horiz-degen-square (ap-bifunctor-id-2 f p)) 
                           (horiz-degen-square (ap-bifunctor-id-1 f q)) 
                           (horiz-degen-square (ap-bifunctor-id-1 f q))
                           (horiz-degen-square (ap-bifunctor-id-2 f p)) 
  bifunctor-cube1' f id id = id



  -- haven't needed this yet

  S¹-rec1 : {C : Type} {c1 c2 : C} (α12 : c1 == c2)
             {α1 : c1 == c1} {α2 : c2 == c2}  (s : Square α1 α12 α12 α2) 
          → {p1 p2 : S¹} → (p1 == p2)
          → S¹-rec c1 α1 p1 == S¹-rec c2 α2 p2
  S¹-rec1 {c1 = c1} id s {p1 = p1} id = ap (λ z → S¹-rec c1 z p1) (horiz-degen-square-to-path s)

  S¹-rec1/βloop : {C : Type} {c1 c2 : C} (α12 : c1 == c2)
             {α1 : c1 == c1} {α2 : c2 == c2}  (s : Square α1 α12 α12 α2) 
          → S¹-rec1 α12 s S¹.loop == diag-square s
  S¹-rec1/βloop = {!!}

  ap-S¹-rec-is-1 : {A C : Type} {a1 a2 : A} (b : A → C) (l : (x : A) → b x == b x) (p : A → S¹)
             (α : a1 == a2) 
          → ap (\ x -> S¹-rec (b x) (l x) (p x)) α == S¹-rec1 (ap b α) (PathOver=.out-PathOver-= (apdo l α)) (ap p α)
  ap-S¹-rec-is-1 b l p id = {!id!}

  t2c : T -> S¹ × S¹
  t2c = T-rec (S¹.base , S¹.base) (pair×≃ id S¹.loop) (pair×≃ S¹.loop id) (pair-square vrefl-square hrefl-square)

  -- FIXME bug with unification? look at the constraints
  -- NAMETHATDOESNTOCCURANYWHEREELSE : {!Nat!}
  -- NAMETHATDOESNTOCCURANYWHEREELSE = {!Z!}

  -- FIXME: bug with unification on the following ?
  -- too many things are solved to id
  -- BUG2 = S¹-rec (S¹-rec T.a T.p) (λ≃ (S¹-elimo _ T.q 
  --               (PathOver=.in-PathOver-= ((∘-square-vertical (vertical-degen-square (S¹.βloop/rec T.a T.p)) {!!})))))

  c2t-loop-homotopy = (S¹-elimo _ T.q 
                (PathOver=.in-PathOver-= 
                  ((∘-square-vertical/degen-top
                    (vertical-degen-square (S¹.βloop/rec T.a T.p)) 
                    (∘-square-vertical/degen-bot (square-symmetry T.f)
                                                (vertical-degen-square (! (S¹.βloop/rec T.a T.p))))))))

  c2t' : S¹ → S¹ → T
  c2t' x y = S¹-rec (S¹-rec T.a T.p) (λ≃ c2t-loop-homotopy) x y 

  c2t : S¹ × S¹ → T
  c2t (x , y) = c2t' x y

  reduce-c2t-1 : ap c2t (pair×≃ (id{_}{S¹.base}) S¹.loop) == T.p
  reduce-c2t-1 = S¹.βloop/rec T.a T.p ∘ ap-bifunctor-id-1 c2t' S¹.loop 

  reduce-c2t-2'' : (y : S¹) → ap (λ x → c2t' x y) S¹.loop == c2t-loop-homotopy y
  reduce-c2t-2'' y = {!!}

  reduce-c2t-2' : ap (λ x → c2t' x S¹.base) S¹.loop == T.q
  reduce-c2t-2' = reduce-c2t-2'' S¹.base

  reduce-c2t-2 : ap c2t (pair×≃ S¹.loop (id{_}{S¹.base})) == T.q
  reduce-c2t-2 = reduce-c2t-2' ∘ ap-bifunctor-id-2 c2t' S¹.loop 

  reduction1 : ap (λ z → c2t (t2c z)) T.p == ap (λ z → z) T.p
  reduction1 = ! (ap-id T.p) ∘ 
               (reduce-c2t-1 ∘ 
                (ap (ap c2t) (T.βp/rec (S¹.base , S¹.base) (pair×≃ id S¹.loop) (pair×≃ S¹.loop id) (pair-square vrefl-square hrefl-square)) ∘ 
                 ap-o c2t t2c T.p))

  reduction2 : ap (λ z → c2t (t2c z)) T.q == ap (λ z → z) T.q
  reduction2 = ! (ap-id T.q) ∘ 
               reduce-c2t-2 ∘ 
               ap (ap c2t) (T.βq/rec (S¹.base , S¹.base) (pair×≃ id S¹.loop) (pair×≃ S¹.loop id) (pair-square vrefl-square hrefl-square)) ∘ 
               ap-o c2t t2c T.q

  t2c2t : (x : T) → c2t (t2c x) == x
  t2c2t = T-elim (\ x -> c2t (t2c x) == x) 
                 id 
                 (PathOver=.in-PathOver-= (vertical-degen-square reduction1))
                 (PathOver=.in-PathOver-= (vertical-degen-square reduction2))
                 (SquareOver=ND.in-SquareOver-= 
                   {!cube-symmetry-left-to-top goal1!}) where
        goal1 : Cube (ap-square (λ z → c2t (t2c z)) T.f)
                     (ap-square (λ z → z) T.f)
                     (horiz-degen-square reduction1)
                     (horiz-degen-square reduction2)
                     (horiz-degen-square reduction2)
                     (horiz-degen-square reduction1)
        goal1 = ∘-cube-horiz/degen (∘-cube-horiz/degen
                                      (∘-cube-horiz/degen (ap-square-o c2t t2c T.f)
                                                          goal2)
                                      {!!})
                                   (ap-square-id! T.f) where 

              goal2 : let a' = (S¹.base , S¹.base)
                          p' = (pair×≃ id S¹.loop)
                          q' = (pair×≃ S¹.loop id)
                          f' = (pair-square vrefl-square hrefl-square)
                      in 
                      Cube (ap-square c2t (ap-square (T-rec a' p' q' f') T.f))
                           (ap-square c2t f')
                           (horiz-degen-square (ap (ap c2t) (T.βp/rec a' p' q' f')))
                           (horiz-degen-square (ap (ap c2t) (T.βq/rec a' p' q' f')))
                           (horiz-degen-square (ap (ap c2t) (T.βq/rec a' p' q' f')))
                           (horiz-degen-square (ap (ap c2t) (T.βp/rec a' p' q' f')))
              goal2 = let a' = (S¹.base , S¹.base)
                          p' = (pair×≃ id S¹.loop)
                          q' = (pair×≃ S¹.loop id)
                          f' = (pair-square vrefl-square hrefl-square)
                      in 
                      coe (ap (λ x → Cube (ap-square c2t (ap-square (T-rec a' p' q' f') T.f)) (ap-square c2t f') 
                                          (horiz-degen-square (ap (ap c2t) (T.βp/rec a' p' q' f'))) x x (horiz-degen-square (ap (ap c2t) (T.βp/rec a' p' q' f'))))
                              (ap-square-horiz-degen c2t (T.βq/rec a' p' q' f')))
                          (coe (ap (λ x → Cube
                                          (ap-square c2t (ap-square (T-rec a' p' q' f') T.f))
                                          (ap-square c2t f')
                                          x
                                          (ap-square c2t (horiz-degen-square (T.βq/rec a' p' q' f')))
                                          (ap-square c2t (horiz-degen-square (T.βq/rec a' p' q' f')))
                                          x)
                                       (ap-square-horiz-degen c2t (T.βp/rec a' p' q' f')))
                        (ap-cube c2t
                         (T.βf/rec (S¹.base , S¹.base) (pair×≃ id S¹.loop)
                          (pair×≃ S¹.loop id) (pair-square vrefl-square hrefl-square))))

              goal3 : Cube (ap-square c2t (pair-square vrefl-square hrefl-square))
                           T.f
                           (horiz-degen-square reduce-c2t-1)
                           (horiz-degen-square reduce-c2t-2)
                           (horiz-degen-square reduce-c2t-2)
                           (horiz-degen-square reduce-c2t-1)
              goal3 = ∘-cube-horiz/degen (bifunctor-cube1 c2t' S¹.loop S¹.loop)
                                        {! SquareOver=ND.out-SquareOver-= (apdo-by-equals (λ y → ap (λ x → c2t' x y) S¹.loop) _ S¹.loop (λ≃ reduce-c2t-2''))  !} 


  c2t2c : (x y : S¹) → t2c (c2t' x y) == (x , y)
  c2t2c = S¹-elimo _ (S¹-elimo _ id (PathOver=.in-PathOver-= square1)) 
                     (coe (! PathOverΠ-NDdomain) (\ x -> PathOver=.in-PathOver-= 
                                                         (S¹-elimo
                                                            (λ x₁ → Square (S¹-elimo (λ x₂ → t2c (c2t' S¹.base x₂) == (S¹.base , x₂)) id (PathOver=.in-PathOver-= square1) x₁) (ap (λ z → t2c (c2t' z x₁)) S¹.loop) (ap (λ z → z , x₁) S¹.loop) (S¹-elimo (λ x₂ → t2c (c2t' S¹.base x₂) == (S¹.base , x₂)) id (PathOver=.in-PathOver-= square1) x₁))
                                                            square2
                                                            (coe (! (PathOver-square/= S¹.loop square2 square2)) 
                                                              {!!}) x))) where
    square1 : Square id (ap (λ z → t2c (c2t' S¹.base z)) S¹.loop) (ap (λ z → S¹.base , z) S¹.loop) id
    square1 = {!!}

    -- cube1 : Cube square1 (pair-square (vrefl-square{p = S¹.loop}) (hrefl-square{p = S¹.loop})) {!!} {!!} {!!} {!!}
    -- cube1 = {!!}

    square2 : Square id (ap (λ z → t2c (c2t' z S¹.base)) S¹.loop) (ap (λ z → z , S¹.base) S¹.loop) id
    square2 = {!!}

    -- cube2 : Cube square2 (pair-square (vrefl-square{p = S¹.loop}) (hrefl-square{p = S¹.loop})) {!!} {!!} {!!} {!!}
    -- cube2 = {!!}

    cube3 : Cube
            square2
            square2
            square1 
            (PathOver=.out-PathOver-=
             (apdo (λ x₁ → ap (λ z → t2c (c2t' z x₁)) S¹.loop) S¹.loop))
            (PathOver=.out-PathOver-=
              (apdo (λ x₁ → ap (λ z → z , x₁) S¹.loop) S¹.loop))
            square1 
    cube3 = {!!}

    square1' : {!!}
    square1' = {!!}

    square2' : {!!}
    square2' = {!!}

    cube4 : Cube
            (PathOver=.out-PathOver-=
             (apdo (λ x₁ → ap (λ z → t2c (c2t' z x₁)) S¹.loop) S¹.loop))
            (PathOver=.out-PathOver-=
              (apdo (λ x₁ → ap (λ z → z , x₁) S¹.loop) S¹.loop))
            square1'
            square2'
            square2'
            square1'
    cube4 = {!!} ∘-cube-h/degen
            (ap-square-id! (pair-square hrefl-square vrefl-square)) ∘-cube-h/degen
            (bifunctor-cube1' _,_ S¹.loop S¹.loop)
