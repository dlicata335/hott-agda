{-# OPTIONS --type-in-type #-}

open import lib.First
open import lib.Paths
open Paths
open import lib.HigherHomotopyAbelian

module lib.WrappedPath where

  data WrapPath (A : Type) (outs : A) (ins : A) : Type {- +1 -} where
       wrap : (wrapper : Path ins outs) (middle : Path ins ins) → WrapPath A outs ins

  unwrap : ∀ {A outs ins} → WrapPath A outs ins → Path outs outs
  unwrap (wrap wrapper middle) = wrapper ∘ middle ∘ ! wrapper

  inside : ∀ {A outs ins} → WrapPath A outs ins → Path ins ins
  inside (wrap _ middle) = middle

  abstract
    uww : {A : Type} {outs ins : A} → (Path ins outs → Path ins ins → Path outs outs)
    uww w m = unwrap (wrap w m)
  
    uww-def : {A : Type} {outs ins : A} (w : Path ins outs) (m : Path ins ins) → uww w m ≃ unwrap (wrap w m)
    uww-def w m = id

  postulate
    comp-uww : {A : Type} {outs mid ins : A} (w : Path mid outs) (w' : Path ins mid) (m : Path ins ins) → uww w (uww w' m) ≃ uww (w ∘ w') m

  -- can ignore wrappers in a doubly iterated identity type
  postulate
    ignore-wrappers : ∀ {A}{a : A} {ins out : Path a a} 
          → (w w' : WrapPath (Path a a) out ins)
          → inside w ≃ inside w'  
          → unwrap w ≃ unwrap w'
    -- ignore-wrappers {A}{a} (wrap w1 i1) (wrap w2 i2) α = 
    --     w1 ∘ i1 ∘ ! w1 ≃〈 ap (λ x → w1 ∘ x ∘ ! w1) α 〉 
    --     w1 ∘ i2 ∘ ! w1 ≃〈 equate-wrappers-!R A a w1 w2 i2 〉 
    --     w2 ∘ i2 ∘ ! w2 ∎ 

  postulate
    ap-loop-by-equals  : {A B : Type} {f g : A → B}
                      (α : (x : _) → g x ≃ f x) 
                    → {M : A} (β : M ≃ M)
                    → (ap f β ≃ uww (α M) (ap g β))
--  ap-loop-by-equals α id =  ! (!-inv-r (α _) ∘ ap (λ x → α _ ∘ x) (∘-unit-l (! (α _)))) 

  uww-ap-loop-by-equals : {A B : Type} {f g : A → B}
                          (α : (x : _) → g x ≃ f x) 
                          → {M : A} (β : M ≃ M) {b : B}
                          → (p : Path (f M) b)
                          → uww p (ap f β) ≃ uww (p ∘ α M) (ap g β)
  uww-ap-loop-by-equals α β p = comp-uww _ (α _) _ ∘ ap (uww p) (ap-loop-by-equals α β)