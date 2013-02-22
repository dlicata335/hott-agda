{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open LoopSpace
open Int
open Truncation

module homotopy.PiLessOfConnected where

   π1Connected≃Unit : (n : TLevel)
             (A : Type) (a : A)
             (cA : Connected n A)
             (lt : (tl 1) <=tl n) 
             → π One A a ≃ Unit
   π1Connected≃Unit -2 A a cA (Inl ())
   π1Connected≃Unit -2 A a cA (Inr ())
   π1Connected≃Unit (S n) A a cA lt = 
     Contractible≃Unit 
               (use-level { -2} (lower-Connected (<=-unS lt) (Connected-Path cA)))

{-
  module PiKLessConnected
       (k : Positive)
       (n : TLevel)
       (A : Type) (a : A)
       (cA : Connected n A)
       (lt : tlp k <tl n) where

       -- ENH: could strengthen conclusion by defining subtraction
       doloop : ∀ k {n} {A} (a : A) → tlp k <tl n 
               → Connected n A → Connected (S (S -2)) (Loop k A a)
       doloop One a lt cA = {!!}
       doloop (S k) a lt cA = {!doloop k _ (subtract-left lt) cA!}

       πk-Unit : π k A a ≃ Unit
       πk-Unit = Contractible≃Unit (use-level { -2} (doloop k a lt cA))
-}