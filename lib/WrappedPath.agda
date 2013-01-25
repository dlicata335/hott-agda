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

  adjust : {A : Type} {outs ins : A} → (Path ins outs → Path ins ins → Path outs outs)
  adjust w m = unwrap (wrap w m)

  abstract
    adj : {A : Type} {outs ins : A} → (Path ins outs → Path ins ins → Path outs outs)
    adj w m = unwrap (wrap w m)
  
    adj-def : {A : Type} {outs ins : A} (w : Path ins outs) (m : Path ins ins) → adj w m ≃ adjust w m
    adj-def w m = id

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

  adj-eq : ∀ {A}{a : A} {ins outs : Path a a} 
          → (wrapper : Path ins outs) (middle : Path ins ins)
          → (wrapper' : Path ins outs) (middle' : Path ins ins)
          → middle ≃ middle'  
          → adj wrapper middle ≃ adj wrapper' middle'
  adj-eq wrapper middle wrapper' middle' α = ! (adj-def _ _) ∘
                                               ignore-wrappers (wrap wrapper middle) (wrap wrapper' middle') α ∘
                                               adj-def _ _

  ap-loop-by-equals  : {A B : Type} {f g : A → B}
                      (α : (x : _) → g x ≃ f x) 
                    → {M : A} (β : M ≃ M)
                    → (ap f β ≃ adj (α M) (ap g β))
  ap-loop-by-equals α id = ! (!-inv-r (α _) ∘ ap (λ x → α _ ∘ x) (∘-unit-l (! (α _))) ∘ adj-def _ _) 

  postulate
    adj-∘ : {A : Type} {outs mid ins : A} (w : Path mid outs) (w' : Path ins mid) (m : Path ins ins)
          → adj w (adj w' m) ≃ adj (w ∘ w') m

  adj-bind : {A : Type} {outs mid ins : A} {w : Path mid outs} {w' : Path ins mid} {m : Path ins ins} {α : _}
            → α ≃ (adj w' m)
            → adj w α ≃ adj (w ∘ w') m
  adj-bind β = adj-∘ _ _ _ ∘ ap (adj _) β 

  adj-id : {A : Type} {a : A} (α : Path a a) ->
             α ≃ adj id α
  adj-id α = ! (∘-unit-l α ∘ adj-def id _)

  ap-adj : ∀ {A B}{a a1} → (f : A → B) (α : Path a a) (q : Path _ a1)
             -> (ap f (adj q α)) ≃ adj (ap f q) (ap f α)
  ap-adj f α id = ! (adj-def id (ap f α)) ∘ ! (ap (ap f) (adj-id α) ∘ ∘-unit-l (ap f α))

  adj-! : {A : Type} {outs ins : A} → (w : Path ins outs) (m : Path ins ins)
        → adj w (! m) ≃ ! (adj w m)
  adj-! w m = ap ! (! (adj-def w m)) ∘ (! (!-∘3 w m (! w)) ∘ ap (λ x → x ∘ ! m ∘ ! w) (! (!-invol w))) ∘ adj-def w (! m)

  {- don't need these--just use adj-bind at the call site! it's easy!
  adj-ap-adj : ∀ {A B}{a a1 b} → (f : A → B) (α : Path a a) (p : Id _ b) (q : Path _ a1)
             -> adj p (ap f (adj q α)) ≃ adj (p ∘ ap f q) (ap f α)
  adj-ap-adj f α p q = adj-bind (ap-adj f α q) 

  adj-ap-loop-by-equals : {A B : Type} {f g : A → B}
                          (α : (x : _) → g x ≃ f x) 
                          → {M : A} (β : M ≃ M) {b : B}
                          → (p : Path (f M) b)
                          → adj p (ap f β) ≃ adj (p ∘ α M) (ap g β)
  adj-ap-loop-by-equals α β p = adj-∘ _ (α _) _ ∘ ap (adj p) (ap-loop-by-equals α β)
  -}
 