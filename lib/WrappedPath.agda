{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open Paths
open import lib.HigherHomotopyAbelian
open HigherHomotopyAbelian
open import lib.Functions
open import lib.Prods

module lib.WrappedPath where

  data WrapPath (A : Type) (outs : A) (ins : A) : Type where
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

    adj-∘ : {A : Type} {outs mid ins : A} (w : Path mid outs) (w' : Path ins mid) (m : Path ins ins)
          → adj w (adj w' m) ≃ adj (w ∘ w') m
    adj-∘ id id m = ∘-unit-l (id ∘ m)

    -- can ignore wrappers in a doubly iterated identity type
    ignore-wrappers : ∀ {A}{a : A} {ins out : Path a a} 
          → (w w' : WrapPath (Path a a) out ins)
          → inside w ≃ inside w'  
          → unwrap w ≃ unwrap w'
    ignore-wrappers {A}{a} (wrap w1 i1) (wrap w2 i2) α = 
        w1 ∘ i1 ∘ ! w1 ≃〈 ap (λ x → w1 ∘ x ∘ ! w1) α 〉 
        w1 ∘ i2 ∘ ! w1 ≃〈 equate-wrappers-!R A a w1 w2 i2 〉 
        w2 ∘ i2 ∘ ! w2 ∎ 
  
    adj-eq : ∀ {A}{a : A} {ins outs : Path a a} 
            → (wrapper : Path ins outs) (middle : Path ins ins)
            → (wrapper' : Path ins outs) (middle' : Path ins ins)
            → middle ≃ middle'
            → adj wrapper middle ≃ adj wrapper' middle'
    adj-eq wrapper middle wrapper' middle' α = ignore-wrappers (wrap wrapper middle) (wrap wrapper' middle') α

    adj-id : {A : Type} {a : A} (α : Path a a) ->
               α ≃ adj id α
    adj-id α = ! (∘-unit-l α)

    ap-adj : ∀ {A B}{a a1} → (f : A → B) (α : Path a a) (q : Path _ a1)
               -> (ap f (adj q α)) ≃ adj (ap f q) (ap f α)
    ap-adj f α id = ! (adj-def id (ap f α)) ∘ ! (ap (ap f) (adj-id α) ∘ ∘-unit-l (ap f α))

    ap-loop-by-equals  : {A B : Type} {f g : A → B}
                        (α : (x : _) → g x ≃ f x) 
                      → {M : A} (β : M ≃ M)
                      → (ap f β ≃ adj (α M) (ap g β))
    ap-loop-by-equals {f = f} {g = g} α β = ! (∘-assoc (α _) (ap g β) (! (α _))) ∘
                                              !
                                              (move-left-right (α _ ∘ ap g β) (ap (λ z → f z) β) (α _)
                                               (move-left-! (ap g β) (α _) (ap (λ z → f z) β ∘ α _)
                                                (ap-by-equals α β)))

    adj-ap≃ : ∀ {A : Type} {B : A → Type} {x : A} {f g : (x : A) → B x}
              (α : Path f f) (q : Path f g)
            → adj (ap≃ q{x}) (ap≃ α {x}) ≃ ap≃ (adj q α) {x}
    adj-ap≃ {x = x} α id = ap (ap (λ f → f x)) (! (∘-unit-l α)) ∘ ∘-unit-l (ap≃ α)

    adj-ap≃-pointwise : ∀ {A : Type} {B : A → Type} {x : A} {f g : (x : A) → B x}
              (α : Path f f) (q : (x : A) → Path (f x) (g x))
            → adj (q x) (ap≃ α {x}) ≃ ap≃ (adj (λ≃ q) α) {x}
    adj-ap≃-pointwise {x = x} α q = adj-ap≃ α (λ≃ q) ∘ ap (λ y → adj y (ap≃ α)) (! (Π≃β q))

    -- adj-split : ∀ {A : Type}{B : A → Type} {p q : Σ B} (α : p ≃ p) (a : Path p q)
    --           -> Path{Σ \ (α : Path{A} (fst q) (fst q)) → Path{B (fst q)} (transport B α (snd q)) (snd q)} 
    --                 (let γ = adj a α in (fst≃ γ , snd≃ γ))
    --                 (adj (fst≃ a) (fst≃ α) , {!(snd≃ α)!})
    -- adj-split = {!!}

    adj-! : {A : Type} {outs ins : A} → (w : Path ins outs) (m : Path ins ins)
          → adj w (! m) ≃ ! (adj w m)
    adj-! w m = (! (!-∘3 w m (! w)) ∘ ap (λ x → x ∘ ! m ∘ ! w) (! (!-invol w)))

    adj-∘-adjs : {A : Type} {a1 a1' a2 a2' : A} 
               (w : Path a1' a2') (w1 : Path a1 a1') (w2 : Path a2 a1') 
               (m1 : Path a1 a1) (m2 : Path a2 a2)
               → adj w ((adj w1 m1) ∘ (adj w2 m2))  ≃ (adj (w ∘ w1) m1) ∘ (adj (w ∘ w2) m2)
    adj-∘-adjs id id id m1 m2 = coh m1 m2 where
      coh : ∀ {A} {a b : A} -> (m1 : Id a b) (m2 : Id b a)
          -> Id (id ∘ (id ∘ m1) ∘ id ∘ m2) ((id ∘ m1) ∘ id ∘ m2)
      coh m1 id = ∘-unit-l (id ∘ m1)

  adj-bind : {A : Type} {outs mid ins : A} {w : Path mid outs} {w' : Path ins mid} {m : Path ins ins} {α : _}
            → α ≃ (adj w' m)
            → adj w α ≃ adj (w ∘ w') m
  adj-bind β = adj-∘ _ _ _ ∘ ap (adj _) β 

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
 