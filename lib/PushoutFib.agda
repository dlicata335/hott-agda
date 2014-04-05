{-# OPTIONS --type-in-type --new-without-K #-}

-- fibrant pushout

open import lib.First

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
        cross : ∀ {A B P} → {a : A} → {b : B} → (p : P a b) → 
                        Path{Pushout A B P} (inl a) (inr b)

      Pushout-rec : {A B C : Type}
                    {P : A → B → Type}
                    (f : (a : A) → C)
                    (g : (b : B) → C)
                    (cross' : (a : A) → (b : B) → (p : P a b) → Path (f a) (g b)) →
                    Pushout A B P → C
      Pushout-rec f _ _ (inl' a) = f a
      Pushout-rec _ g _ (inr' b) = g b

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
      -- FIXME path β

      Pushout-elim : {A B : Type}
                     {P : A → B → Type}
                     (C : Pushout A B P → Type)
                     (f : (a : A) → C (inl a))
                     (g : (b : B) → C (inr b))
                     (cross' : (a : A) → (b : B) → (p : P a b) → 
                           Path (transport C (cross p) (f a)) (g b)) →
                     (x : Pushout A B P) → C x
      Pushout-elim _ f g H' (inl' a) = f a
      Pushout-elim _ f g H' (inr' b) = g b

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

    open P public
