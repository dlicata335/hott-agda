{-# OPTIONS --type-in-type --without-K #-}

-- pushout of two maps f and g.
-- e.g. S2 = Pushout {S1}{Unit}{Unit} cst cst
--      has north, south, and a circle of points in between

open import lib.First
open import lib.NConnected
open import lib.Prods
open import lib.Sums
open import lib.Functions
open import lib.Paths 
open import lib.NType
open import lib.Universe
open import lib.Truncations
open import lib.WEq
open Truncation
open import lib.cubical.PathOver
open import lib.cubical.Square

module lib.Pushout where

  module Pushout where

    module P where
      private
        data Pushout' {ZZ X Y : Type} (f : ZZ → X) (g : ZZ → Y) : Type where
          inl' : X → Pushout' f g 
          inr' : Y → Pushout' f g

      Pushout : {ZZ X Y : Type} (f : ZZ → X) (g : ZZ → Y) → Type 
      Pushout = Pushout'

      inl : ∀ {ZZ X Y}{f : ZZ → X}{g : ZZ → Y} → X → Pushout f g
      inl = inl'

      inr : ∀ {ZZ X Y}{f : ZZ → X}{g : ZZ → Y} → Y → Pushout f g
      inr = inr'

      postulate {- HoTT Axiom -}
        glue : ∀ {ZZ X Y} {f : ZZ → X}{g : ZZ → Y} (z : ZZ) → Path{Pushout f g} (inl (f z)) (inr (g z))

      Pushout-rec : {ZZ X Y C : Type} 
                    {f : ZZ → X} {g : ZZ → Y}
                    (b1 : X → C)
                    (b3 : Y → C)
                    (glue' : (z : ZZ) → (b1 (f z)) ≃ b3 (g z))
                  → Pushout f g → C
      Pushout-rec b1 _ _ (inl' x) = b1 x
      Pushout-rec _ b3 _ (inr' y) = b3 y

      postulate {- HoTT Axiom -}
        βglue/rec : {ZZ X Y C : Type}
                    {f : ZZ → X} {g : ZZ → Y}
                    (b1 : X → C)
                    (b2 : Y → C)
                    (glue' : (z : ZZ) → Path (b1 (f z)) (b2 (g z))) →
                    (z : ZZ) → Path (ap (Pushout-rec b1 b2 glue') (glue z)) (glue' z)

      Pushout-elim : {ZZ X Y : Type} 
                    {f : ZZ → X} {g : ZZ → Y}
                    (C : Pushout f g -> Type)
                    (b1 : (x : X) → C (inl x))
                    (b3 : (y : Y) → C (inr y))
                    (glue' : (z : ZZ) → PathOver C (glue z) (b1 (f z)) (b3 (g z)))
                  → (p : Pushout f g) → C p
      Pushout-elim _ b1 _ _ (inl' x) = b1 x
      Pushout-elim _ _ b3 _ (inr' y) = b3 y

    open P public

    Wedge : {A B : Type} (a0 : A) (b0 : B) → Type
    Wedge {A}{B} a0 b0 = Pushout {Unit}{A}{B} (\ _ -> a0) (\ _ -> b0)

    wedge-to-prod : ∀ {A B} {a0 : A} {b0 : B} → (Wedge a0 b0) → A × B
    wedge-to-prod {a0 = a0} {b0 = b0} = Pushout-rec (λ a → a , b0) (λ b → a0 , b) (\ _ -> id) 

    module WedgeToProd {A B : Type} {m n : _} (a0 : A) (b0 : B) (cA : Connected (S m) A) (cB : Connected (S n) B) where

      i = wedge-to-prod {A}{B}{a0}{b0}

      connected : ConnectedMap (plus2 m n) i
      connected = ConnectedMap.from-UMP (plus2 m n) i 
        (λ P b → (λ y → ConnectedProduct.wedge-elim cA cB (λ x y₁ → P (x , y₁)) (Inr id) {a0} {b0} 
                    (λ y → b (inr y))
                    (λ x → b (inl x)) 
                    (! (over-to-hom (changeover _ (βglue/rec _ _ _ _) (over-o-ap (fst o P) (apdo b (glue _))))))
                    (fst y)
                    (snd y)) ,
                 Pushout-elim _ (λ x → ap≃ (ConnectedProduct.wedge-elim-βb cA cB _ (Inr id) _ _ _))
                                (λ x → ap≃ (ConnectedProduct.wedge-elim-βa cA cB _ (Inr id) _ _ _)) 
                                WedgeConnect ) where
                                postulate WedgeConnect : ∀ {A : Type} → A
{-
                                (λ <> → hom-to-over/left _ 
                                  (_ ≃〈 transport-Path-do _ _ (glue <>) _ 〉 
                                   over-to-hom
                                     (changeover (λ v → fst (P (i v)))
                                      (!-inv-r (glue <>) ∘ ap (_∘_ (glue <>)) (∘-unit-l (! (glue <>))))
                                      (apdo (λ v → b v) (glue <>) ∘o
                                       hom-to-over
                                       (ap≃
                                        (ConnectedProduct.wedge-elim-βb cA cB
                                         (λ z z₁ → fst (P (z , z₁)) , snd (P (z , z₁))) (Inr id)
                                         (λ y → b (inr y)) (λ x → b (inl x))
                                         (!
                                          (over-to-hom
                                           (changeover ((λ r → fst r) o P)
                                            (βglue/rec (λ a → a , b0) (λ b₁ → a0 , b₁) (λ z → id) <>)
                                            (over-o-ap ((λ r → fst r) o P) (apdo b (glue <>))))))))
                                       ∘o
                                       !o
                                       (apdo
                                        (λ v →
                                           ConnectedProduct.wedge-elim cA cB (λ x y₁ → P (x , y₁)) (Inr id)
                                           (λ y → b (inr y)) (λ x → b (inl x))
                                           (!
                                            (over-to-hom
                                             (changeover ((λ r → fst r) o P)
                                              (βglue/rec (λ a → a , b0) (λ b₁ → a0 , b₁) (λ z → id) <>)
                                              (over-o-ap ((λ r → fst r) o P) (apdo b (glue <>))))))
                                           (fst (i v)) (snd (i v)))
                                        (glue <>)))) ≃〈 ap
                                                           (λ Z₁ →
                                                              over-to-hom
                                                              (changeover (λ v → fst (P (i v)))
                                                               (!-inv-r (glue <>) ∘ ap (_∘_ (glue <>)) (∘-unit-l (! (glue <>))))
                                                               (apdo (λ v → b v) (glue <>) ∘o
                                                                hom-to-over
                                                                (ap≃
                                                                 (ConnectedProduct.wedge-elim-βb cA cB
                                                                  (λ z z₁ → fst (P (z , z₁)) , snd (P (z , z₁))) (Inr id)
                                                                  (λ y → b (inr y)) (λ x → b (inl x))
                                                                  (!
                                                                   (over-to-hom
                                                                    (changeover ((λ r → fst r) o P)
                                                                     (βglue/rec (λ a → a , b0) (λ b₁ → a0 , b₁) (λ z → id) <>)
                                                                     (over-o-ap ((λ r → fst r) o P) (apdo b (glue <>))))))))
                                                                ∘o !o Z₁)))
                                                           {!!} 〉 
                                   {!!} ≃〈 {!!} 〉 
                                   _ ∎
                                   )))
-}
