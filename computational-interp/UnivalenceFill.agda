{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open import lib.cubical.Cubical

module computational-interp.UnivalenceFill where

  compose-PathOver-paths  : {Δ : Type} {A : Δ → Type} {θ1 θ2 : Δ} {δ : θ1 == θ2} {M1 M1' : A θ1} {M2 M2' : A θ2} 
                          → M1 == M1'
                          → PathOver A δ M1 M2
                          → M2 == M2'
                          → PathOver A δ M1' M2'
  compose-PathOver-paths id id id = id



  record REquiv (A0 : Type) (A1 : Type) : Type where
    field 
      for  : A0 → A1
      back : A1 → A0
      R    : A0 → A1 → Type
      het0 : (x : A0) → R x (for x)
      het1 : (x : A1) → R (back x) x
      hom0 : ∀ {x0 x1} (r : R x0 x1) → x0 == back x1
      hom1 : ∀ {x0 x1} (r : R x0 x1) → for x0 == x1
      hethom0 : ∀ {x0 x1} (r : R x0 x1) → PathOver (\ x1 → R x0 x1) (hom1 r) (het0 x0) r
      hethom1 : ∀ {x0 x1} (r : R x0 x1) → PathOver (\ x0 → R x0 x1) (hom0 r) r (het1 x1)
  open REquiv

  hom1-on-het0 : ∀ {A0 A1} (E : REquiv A0 A1) → ∀ {x} → hom1 E (het0 E x) == id
  hom1-on-het0 E {x} = {!hethom0 E (het0 E x) !}

  lift-to-id : ∀ {A0 A1} (E : REquiv A0 A1)
               → ∀ {x y z w} → R E x z → R E y w → REquiv (x == y) (z == w)
  lift-to-id E rl rr = record
                         { for = λ p → hom1 E rr ∘ ap (for E) p ∘ ! (hom1 E rl)
                         ; back = {!!}
                         ; R = λ p q → hom1 E rr ∘ ap (for E) p ∘ ! (hom1 E rl) == q
                         ; het0 = λ _ → id
                         ; het1 = {!!}
                         ; hom0 = {!!}
                         ; hom1 = (λ x → x)
                         ; hethom0 = {!!}
                         ; hethom1 = {!!}
                         }



  module Fill (A00 : Type) (A01 : Type) (A0 : A00 == A01)
              (A10 : Type) (A11 : Type) (A1 : A10 == A11) 
              (E0 : REquiv A00 A10)
              (E1 : REquiv A01 A11)
              (E : ∀ {x y z w} → R E0 x z → R E1 y w → REquiv (PathOver (λ X → X) A0 x y) (PathOver (λ X → X) A1 z w))
              (a0 : A00) (b0 : A00) (c0 : A01)
              (p0 : PathOver (\ X -> X) A0 a0 c0)
              (ty0 : a0 == b0)
              (a1 : A10) (c1 : A11) (d1 : A11)
              (p1 : PathOver (\ X -> X) A1 a1 c1)
              (ty1 : c1 == d1)
              (e0 : R E0 a0 a1)
              (e1 : R E1 c0 c1)
              (e  : R (E e0 e1) p0 p1)
         where

              ty1' : c0 == (back E1 d1)
              ty1' = (ap (back E1) ty1 ∘ hom0 E1 e1)

              r0 : PathOver (\ X -> X) A0 b0 (back E1 d1)
              r0 = compose-PathOver-paths ty0 p0 ty1'

              ty0' : Id a1 (for E0 b0)
              ty0' = (ap (for E0) ty0 ∘ ! (hom1 E0 e0))

              r1 : PathOver (\ X -> X) A1 (for E0 b0) d1
              r1 = compose-PathOver-paths ty0' p1 ty1

              ry0 : R (lift-to-id E0 e0 (het0 E0 b0)) ty0 ty0'
              ry0 = {!hom1-on-het0 E0!}

              ry1 : R (lift-to-id E1 e1 (het1 E1 d1)) ty1' ty1
              ry1 = {!hom1-on-het0 E0!}

              r : R (E (het0 E0 b0) (het1 E1 d1)) r0 r1
              r = {!compose ry0 ry1 and p!}
              
