{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open import lib.Prods
open import lib.NConnected
open import lib.Truncations
open import lib.Int
open import lib.Nat
open import lib.NType
open Truncation
open Int
open Nat

module lib.Suspension where

  module Suspension where

    module S  where
      private
        data Susp' (A : Type) : Type where
          No'  : Susp' A
          So'  : Susp' A

        data Susp'' (A : Type) : Type where
          mkSusp'' : Susp' A → (Unit -> Unit) -> Susp'' A

      Susp = Susp''

      No : ∀ {A} → Susp A
      No = mkSusp'' No' _

      So : ∀ {A} → Susp A
      So = mkSusp'' So' _
      
      postulate {- HoTT Axiom -} 
        mer : ∀ {A} → A -> Path{Susp A} No So
     
      Susp-rec : {A C : Type}
                 (N' S' : C) 
                 (mer' : A -> Path N' S')
               -> Susp A -> C
      Susp-rec N' S' _ (mkSusp'' No' _) = N'
      Susp-rec N' S' _ (mkSusp'' So' _) = S'

      postulate {- HoTT Axiom -} 
        Susp-rec/βmer : {A C : Type} {N' S' : C} {mer' : A → N' ≃ S'} {x : A} → ap (Susp-rec N' S' mer') (mer x) ≃ mer' x

      Susp-elim : {A : _} (C : Susp A → Type)
                  (N' : C No) 
                  (S' : C So) 
                  (mer' : (x : A) -> Path (transport C (mer x) N') S')
                -> (x : Susp A) -> C x
      Susp-elim _ N' S' _ (mkSusp'' No' _) = N'
      Susp-elim _ N' S' _ (mkSusp'' So' _) = S'

      postulate {- HoTT Axiom -} 
        Susp-elim/βmer : {A : _} (C : Susp A → Type)
                  (N' : C No) 
                  (S' : C So) 
                  (mer' : (x : A) -> Path (transport C (mer x) N') S') {x : A}
                -> apd (Susp-elim C N' S' mer') (mer x) ≃ mer' x

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
            mers-eq (S n) nA x x' = Connected.everywhere n {a0 = x} nA
                                      (λ x0 → ap [_] (mer x) ≃ ap [_] (mer x0) , use-level (use-level (Trunc-level {S (S n)}) _ _) _ _) id x'


    Susp^ : (n : Nat) → Type → Type
    Susp^ Z A = A
    Susp^ (S n) A = Susp (Susp^ n A)

    point^ : (n : Nat) → {A : Type} (a : A) → Susp^ n A
    point^ Z a = a
    point^ (S _) _ = No

    -- FIXME : generalize
    abstract
      Susp^-Connected-1 : (n : Nat) {A : Type} (a : A)
                      → Connected (tl n) (Susp^ (S n) A)
      Susp^-Connected-1 Z a =
        ntype ([ No ] , Trunc-elim _ (λ _ → path-preserves-level Trunc-level)
                                   (Susp-elim _ id (ap [_] (mer a)) 
                                   (λ x → HProp-unique (use-level (Trunc-level {S (S -2)}) _ _) _ _)))
      Susp^-Connected-1 (S n) a = Susp-Connected _ (Susp^-Connected-1 n a)

      Susp^-Connected0 : (n : Nat) {A : Type} 
                      → Connected (S (S -2)) A 
                      → Connected (tl n) (Susp^ n A)
      Susp^-Connected0 Z nA = nA
      Susp^-Connected0 (S n) a = Susp-Connected _ (Susp^-Connected0 n a)

    transport-Susp^-number : ∀ {m n} (α : m ≃ n) {A}(a : A)
                              -> (transport (\x -> Susp^ x A) α (point^ m a)) ≃ (point^ n a)
    transport-Susp^-number id _ = id

