{-# OPTIONS --type-in-type --without-K #-}

-- fibrant pushout

open import lib.First
open import lib.cubical.PathOver

module lib.PushoutFib where

  module PushoutFib where

    module P where
      private
        data Pushout' (A B : Type) (P : A → B → Type) : Type where
          inl' : A → Pushout' A B P
          inr' : B → Pushout' A B P

      Pushout = Pushout'

      inl : ∀ {A B P} → A → Pushout A B P
      inl = inl'

      inr : ∀ {A B P} → B → Pushout A B P
      inr = inr'

      postulate {- HoTT Axiom -}
        glue : ∀ {A B P} → {a : A} → {b : B} → (p : P a b) → 
                        Path{Pushout A B P} (inl a) (inr b)

      Pushout-rec : {A B C : Type}
                    {P : A → B → Type}
                    (f : (a : A) → C)
                    (g : (b : B) → C)
                    (glue' : (a : A) → (b : B) → (p : P a b) → Path (f a) (g b)) →
                    Pushout A B P → C
      Pushout-rec f _ _ (inl' a) = f a
      Pushout-rec _ g _ (inr' b) = g b

      postulate {- HoTT Axiom -}
        Pushout-rec/βglue : {A B C : Type}
                             {P : A → B → Type}
                             {C : Type}
                             (f : (a : A) → C)
                             (g : (b : B) → C)
                             (glue' : (a : A) → (b : B) → (p : P a b) →
                                      Path (f a) (g b)) →
                            (a : A) → (b : B) → (p : P a b) → 
                            Path (ap (Pushout-rec f g glue') (glue p))
                                 (glue' a b p)

      Pushout-elim : {A B : Type}
                     {P : A → B → Type}
                     (C : Pushout A B P → Type)
                     (f : (a : A) → C (inl a))
                     (g : (b : B) → C (inr b))
                     (glue' : (a : A) → (b : B) → (p : P a b) → PathOver C (glue p)(f a) (g b)) →
                     (x : Pushout A B P) → C x
      Pushout-elim _ f g H' (inl' a) = f a
      Pushout-elim _ f g H' (inr' b) = g b

      postulate {- HoTT Axiom -}
        Pushout-elim/βglue : {A B : Type}
                              {P : A → B → Type}
                              (C : Pushout A B P → Type)
                              (f : (a : A) → C (inl a))
                              (g : (b : B) → C (inr b))
                              (glue' : (a : A) → (b : B) → (p : P a b) →
                                      PathOver C (glue p) (f a) (g b)) →
                            (a : A) → (b : B) → (p : P a b) → 
                            Path (apdo (Pushout-elim C f g glue') (glue p))
                                 (glue' a b p)

    open P public
