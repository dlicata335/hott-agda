{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open import lib.NConnected
open import lib.Truncations
open Truncation

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
      
      postulate {- HoTT Axiom -} 
        mer : ∀ {A} → A -> Path{Susp A} No So
     
      Susp-rec : {A C : Type}
                 (N' S' : C) 
                 (mer' : A -> Path N' S')
               -> Susp A -> C
      Susp-rec N' S' _ No' = N'
      Susp-rec N' S' _ So' = S'

      postulate {- HoTT Axiom -} 
        Susp-rec/βmer : {A C : Type} {N' S' : C} {mer' : A → N' ≃ S'} {x : A} → ap (Susp-rec N' S' mer') (mer x) ≃ mer' x

      Susp-elim : {A : _} (C : Susp A → Type)
                  (N' : C No) 
                  (S' : C So) 
                  (mer' : (x : A) -> Path (transport C (mer x) N') S')
                -> (x : Susp A) -> C x
      Susp-elim _ N' S' _ No' = N'
      Susp-elim _ N' S' _ So' = S'

      {- FIXME: elim 
      -}

    open S public

    abstract
      Susp-Connected : ∀ n {A} → Connected n A → Connected (S n) (Susp A)
      Susp-Connected n nA = 
        ntype ([ No ] ,
                 Trunc-elim _ (λ _ → path-preserves-level Trunc-level) 
                              (Susp-elim _ id (Trunc-rec (use-level (Trunc-level{S n}) _ _)
                                                         (λ a → ap [_] (mer a)) (fst (use-level nA)))
                                              (λ x → Trunc-elim
                                                       (λ y →
                                                          Path (transport (λ z → Path{Trunc (S n) (Susp _)} [ No ] [ z ]) (mer x) id)
                                                          (Trunc-rec (use-level (Trunc-level{S n}) [ No ] [ So ])
                                                           (λ a → ap [_] (mer a)) y))
                                                       (λ _ → path-preserves-level (use-level (Trunc-level {S n}) _ _))
                                                       (λ x' → transport (λ z → Path{Trunc (S n) (Susp _)} [ No ] [ z ]) (mer x) id ≃〈 transport-Path-post' [_] (mer x) id 〉
                                                               ap [_] (mer x) ≃〈 mers-eq n nA _ _ 〉
                                                               (ap [_] (mer x') ∎))
                                                       (fst (use-level nA))))) where 
            mers-eq : ∀ n {A} → Connected n A → (x x' : A) → Path{Path {Trunc (S n) (Susp A)} [ No ] [ So ]} (ap [_] (mer x)) (ap [_] (mer x'))
            mers-eq -2 nA x x' = HProp-unique (path-preserves-level (Trunc-level {S -2})) _ _
            mers-eq (S n) nA x x' = ConnectedFib.everywhere n {a0 = x} nA
                                      (λ x0 → ap [_] (mer x) ≃ ap [_] (mer x0) , use-level (use-level (Trunc-level {S (S n)}) _ _) _ _) id x'


