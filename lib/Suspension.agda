{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open Paths

module lib.Suspension where

  module Suspension where

    module S  where
      private
        data Susp' (A : Type) : Type where
          No'  : Susp' A
          So'  : Susp' A

      Susp = Susp'

      No : ∀ {A} → Susp A
      No = No'

      So : ∀ {A} → Susp A
      So = So'
      
      postulate 
        mer : ∀ {A} → A -> Path{Susp A} No So
     
      Susp-rec : {A C : Type}
                 (N' S' : C) 
                 (mer' : A -> Path N' S')
               -> Susp A -> C
      Susp-rec N' S' _ No' = N'
      Susp-rec N' S' _ So' = S'

      postulate 
        Susp-rec/βmer : {A C : Type} {N' S' : C} {mer' : A → N' ≃ S'} {x : A} → ap (Susp-rec N' S' mer') (mer x) ≃ mer' x

      Susp-elim : {A : _} (C : Susp A → Type)
                  (N' : C No) 
                  (S' : C So) 
                  (mer' : (x : A) -> Path (transport C (mer x) N') S')
                -> (x : Susp A) -> C x
      Susp-elim _ N' S' _ No' = N'
      Susp-elim _ N' S' _ So' = S'

      {- FIXME: 
      postulate 
        Susp-elim/βmer : {A C : Type} {N' S' : C} {mer' : A → N' ≃ S'} {x : S¹.S¹} → ap (Susp-rec N' S' mer') (mer x) ≃ mer' x
      -}

    open S public