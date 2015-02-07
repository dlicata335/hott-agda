{-# OPTIONS --type-in-type --without-K #-}

-- pushout of two maps f and g.
-- includes a constructor for the "middle" space Z.
-- e.g. S2 = Pushout {S1}{Unit}{Unit} cst cst
--      has north, south, and a circle of points in between

open import lib.First
open import lib.NConnected
open import lib.Prods
open import lib.Functions
open import lib.Paths 
open import lib.NType
open import lib.Universe
open import lib.Truncations
open import lib.WEq
open Truncation

module lib.PushoutFat where

  module FatPushout where

    module P where
      private
        data Pushout' {Z X Y : Type} (f : Z → X) (g : Z → Y) : Type where
          inl' : X → Pushout' f g 
          inm' : Z → Pushout' f g
          inr' : Y → Pushout' f g

      Pushout : {Z X Y : Type} (f : Z → X) (g : Z → Y) → Type 
      Pushout = Pushout'

      inl : ∀ {Z X Y}{f : Z → X}{g : Z → Y} → X → Pushout f g
      inl = inl'

      inr : ∀ {Z X Y}{f : Z → X}{g : Z → Y} → Y → Pushout f g
      inr = inr'

      inm : ∀ {Z X Y}{f : Z → X}{g : Z → Y} → Z → Pushout f g
      inm = inm'

      postulate {- HoTT Axiom -}
        gluel : ∀ {Z X Y} {f : Z → X}{g : Z → Y} (z : Z) → Path{Pushout f g} (inl (f z)) (inm z)
        gluer : ∀ {Z X Y} {f : Z → X}{g : Z → Y} (z : Z) → Path{Pushout f g} (inm z) (inr (g z))

      Pushout-rec : {Z X Y C : Type} 
                    {f : Z → X} {g : Z → Y}
                    (b1 : X → C)
                    (b2 : Z → C)
                    (b3 : Y → C)
                    (gluel' : (z : Z) → (b1 (f z)) ≃ b2 z)
                    (gluer' : (z : Z) → (b2 z) ≃ b3 (g z))
                  → Pushout f g → C
      Pushout-rec b1 _ _ _ _ (inl' x) = b1 x
      Pushout-rec _ b2 _ _ _ (inm' z) = b2 z
      Pushout-rec _ _ b3 _ _ (inr' y) = b3 y

{-
      postulate {- HoTT Axiom -}
        Pushout-rec/βcross : {A B C : Type}
                             {P : A → B → Type}
                             {C : Type}
                             (f : (a : A) → C)
                             (g : (b : B) → C)
                             (cross' : (a : A) → (b : B) → (p : P a b) →
                                      Path (f a) (g b)) →
                            (a : A) → (b : B) → (p : P a b) → 
                            Path (ap (Pushout-rec f g cross') (cross p))
                                 (cross' a b p)
-}

      Pushout-elim : {Z X Y : Type} 
                    {f : Z → X} {g : Z → Y}
                    (C : Pushout f g -> Type)
                    (b1 : (x : X) → C (inl x))
                    (b2 : (z : Z) → C (inm z))
                    (b3 : (y : Y) → C (inr y))
                    (gluel' : (z : Z) → transport C (gluel z) (b1 (f z)) ≃ b2 z)
                    (gluer' : (z : Z) → transport C (gluer z) (b2 z) ≃ b3 (g z))
                  → (p : Pushout f g) → C p
      Pushout-elim _ b1 _ _ _ _ (inl' x) = b1 x
      Pushout-elim _ _ b2 _ _ _ (inm' z) = b2 z
      Pushout-elim _ _ _ b3 _ _ (inr' y) = b3 y

{-
      postulate {- HoTT Axiom -}
        Pushout-elim/βcross : {A B C : Type}
                              {P : A → B → Type}
                              (C : Pushout A B P → Type)
                              (f : (a : A) → C (inl a))
                              (g : (b : B) → C (inr b))
                              (cross' : (a : A) → (b : B) → (p : P a b) →
                                      Path (transport C (cross p) (f a)) (g b)) →
                            (a : A) → (b : B) → (p : P a b) → 
                            Path (apd (Pushout-elim C f g cross') (cross p))
                                 (cross' a b p)
-}

    open P public

{-
    module JoinOfHProps {A B : Type} {hA : HProp A} {hB : HProp B} where
      A*B = Pushout {A × B}{A}{B} fst snd

      hA*B : HProp A*B
      hA*B = unique-HProp {!Pushout-elim !}

      test : (a : A) (b : B) → Path {A*B} (inl a) (inr b)
      test a b = gluer (a , b) ∘ gluel (a , b)
-}      

{-
    Wedge : {A B : Type} (a0 : A) (b0 : B) → Type
    Wedge {A}{B} a0 b0 = Pushout {Unit}{A}{B} (\ _ -> a0) (\ _ -> b0)

    wedge-to-prod : ∀ {A B} {a0 : A} {b0 : B} → (Wedge a0 b0) → A × B
    wedge-to-prod {a0 = a0} {b0 = b0} = Pushout-rec (λ a → a , b0) (λ _ → a0 , b0) (λ b → a0 , b) (\ _ -> id) (\ _ -> id)

    module WedgeToProd {A B : Type} {m n : _} (a0 : A) (b0 : B) (cA : Connected (S m) A) (cB : Connected (S n) B) where

      i = wedge-to-prod {A}{B}{a0} {b0}

      i-ump : ConnectedMap.ConnectedMapUMP (plus2 m n) i
      i-ump P br = (λ ab → fst (ext (fst ab)) (snd ab)) ,
                   Pushout-elim _ (λ a → snd (ext a)) 
                                  (λ _ → transport (λ z' → fst (ext (fst (i z'))) (snd (i z')) ≃ br z') (gluel <>) (snd (ext a0)))
                                  (λ b → ap≃ (fst≃ ext-a0) {b})
                                  (λ _ → id)
                                  (λ _ → ext-a0-coh ∘
                                           ap≃
                                           (!
                                            (transport-∘ (λ z → fst (ext (fst (i z))) (snd (i z)) ≃ br z)
                                             (gluer _) (gluel _)))) where
        postulate -- needed for ooTopos Blakers-Massey?
          br-glue-adj : (transport (λ z → fst (P (i z))) (gluer <> ∘ gluel <>)) ≃ (\ x -> x)
          -- br-glue-adj = {!!}

        br-glue : br (inr b0) ≃ br (inl a0)
        br-glue = ap≃ br-glue-adj ∘ ! (apd br (gluer <> ∘ gluel <>))

        ext : (a : A) → Extensions.Extensions _ b0 (λ b → fst (P (a , b))) (br (inl a)) 
        ext = ConnectedFib.everywhere m {_}{a0} cA 
              (\ a -> (Extensions.Extensions-ntype cB b0 (λ b → (P (a , b))) (br (inl a))))
              ((λ b → br (inr b)) , br-glue)

        ext-a0 : (ext a0) ≃ ((λ b → br (inr b)) , br-glue)
        ext-a0 = (ConnectedFib.β m {_}{a0} cA 
                     (\ a -> (Extensions.Extensions-ntype cB b0 (λ b → (P (a , b))) (br (inl a))))
                     _)

        ext-a0-coh : (transport (λ z → fst (ext (fst (i z))) (snd (i z)) ≃ br z)
                     (gluer <> ∘ gluel <>) (snd (ext a0)))
                       ≃ (ap≃ (fst≃ ext-a0) {b0})
        ext-a0-coh = ?

      ci : ConnectedMap.ConnectedMap (plus2 m n) i
      ci = ConnectedMap.ConnectedMap-from-UMP (plus2 m n) i i-ump 
-}
