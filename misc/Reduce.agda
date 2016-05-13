{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude

module misc.Reduce where

  data Tree (A : Set) : Set where
    Empty : Tree A
    Leaf : A -> Tree A
    Node : Tree A -> Tree A -> Tree A

  ecase : ∀ {A} (t : Tree A) → Either (t == Empty) (t == Empty → Void)
  ecase Empty = Inl id
  ecase (Leaf x) = Inr (λ { () })
  ecase (Node _ _ ) = Inr (λ { () })

  opt : ∀ {A} → Tree A → Tree A
  opt Empty = Empty
  opt (Leaf x) = Leaf x
  opt (Node l r) with ecase (opt l) | ecase (opt r)
  ... | Inl p | _ = opt r
  ... | _ | Inl p = opt l
  ... | _ | _ = Node (opt l) (opt r)

  reduce : ∀ {A : Set} → (A → A → A) → A → Tree A → A
  reduce n e Empty = e
  reduce n e (Leaf x) = x
  reduce n e (Node l r) = n (reduce n e l) (reduce n e r)

  thm : ∀ {A : Set} (n : A → A → A) (e : A) (t : Tree A)
      → ((x : A) → n x e == x)
      → ((x : A) → n e x == x)
      → reduce n e t == reduce n e (opt t)
  thm n e Empty ru lu = id
  thm n e (Leaf x) ru lu = id
  thm n e (Node l r) ru lu with ecase (opt l) | ecase (opt r)
  ... | Inl p | _ = (thm n e r ru lu ∘ lu _) ∘ ap (λ x → n x (reduce n e r)) (ap (reduce n e) p ∘ thm n e l ru lu)
  ... | Inr _ | Inl p = (thm n e l ru lu ∘ ru _) ∘ ap (λ x → n (reduce n e l) x) (ap (reduce n e) p ∘ thm n e r ru lu)
  ... | Inr _ | Inr _ = ap2 n (thm n e l ru lu) (thm n e r ru lu)


  data Order : Set where
    Less : Order
    Equal : Order
    Greater : Order

  module Filter (A : Set) (compare : A → A → Order) where
    
    keeplt : Tree A → A → Tree A
    keeplt Empty x = ?
    keeplt (Leaf x) x₁ = ?
    keeplt (Node t t₁) x = ?

