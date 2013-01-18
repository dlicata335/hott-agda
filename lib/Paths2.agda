-- lemmas about Paths that need equivalences / other things that come after paths

{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths 
open Paths
open import lib.AdjointEquiv
open import lib.Prods
open import lib.Univalence
open import lib.Functions

module lib.Paths2 where

  Path-equiv : ∀ {A B} (α : Path A B) 
               {x y : A} 
             -> Path (Path{A} x y) (Path{B} (coe α x) (coe α y))
  Path-equiv α = ap (λ (p : Σ (λ (A : Type) → A × A)) → Path (fst (snd p)) (snd (snd p)))
                    (pair≃ α (pair×≃ (ap fst (ap≃ (transport-× α (λ x → x) (λ x → x))))
                                     (ap snd (ap≃ (transport-× α (λ x → x) (λ x → x))))))

  run-Path-equiv : ∀ {A B} (α : Path A B) 
                         {x y : A} -> Path{(Path{A} x y) → (Path{B} (coe α x) (coe α y))}
                                          (coe (Path-equiv α))
                                          (ap (coe α))
  run-Path-equiv id = ! (λ≃ ap-id)
