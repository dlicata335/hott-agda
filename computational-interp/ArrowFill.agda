{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open import lib.cubical.Cubical

module computational-interp.ArrowFill where

  coe→ : {A0 A1 B0 B1 : Type} (A : A0 == A1) (B : B0 == B1) (f : A0 -> B0)
       → coe (ap (\ XY → fst XY → snd XY) (pair×≃ A B)) f == \ a1 → coe B (f (coe (! A) a1))
  coe→ id id f = id

  fill→ : {A0 A1 B0 B1 : Type} (A : A0 == A1) (B : B0 == B1) (f : A0 -> B0)
         → PathOver (\ X → X)
                    (ap (\ XY → fst XY → snd XY) (pair×≃ A B))
                    f
                    (\ a1 → coe B (f (coe (! A) a1)))
  fill→ {A0}{A1} A B f =
    over-o-ap (λ X → X) {δ' = pair×≃ A B} 
      (in-PathOverΠ (λ a0 a1 α → 
        over-ap-o (λ X → X) (changeover (λ X → X) (! red2) 
          (PathOver-transport-right' (λ X → X) B (ap f (over-to-hom/right α) · red1))))) where
        red1 : {a1 : _} → 
               (f (transport (λ v → fst v) (! (pair×≃ A B)) a1)) == 
               f (coe (! A) a1)
        red1 = {!!}

        red2 : ∀ {a0 : A0} {a1 : A1} {α : PathOver (λ v → fst v) (pair×≃ A B) a0 a1} 
                → (ap (λ z → snd (fst z)) (pair= (pair×≃ A B) α)) == B
        red2 = {!!}
