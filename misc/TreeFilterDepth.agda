{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude

module misc.TreeFilterDepth where

  data Order : Set where
      Less : Order
      Equal : Order
      Greater : Order

  data _≤_ : Nat → Nat → Set where
    Le0  : ∀ {m} → 0 ≤ m 
    LeS : ∀ {n m} → n ≤ m → S n ≤ S m 

  ≤-refl : (x : Nat) → x ≤ x 
  ≤-refl Z = Le0
  ≤-refl (S x) = LeS (≤-refl x)

  ≤-S : (x : Nat) → x ≤ S x
  ≤-S Z = Le0
  ≤-S (S x) = LeS (≤-S x)

  _≤-trans_ : {x y z : Nat} → x ≤ y → y ≤ z → x ≤ z
  _≤-trans_ Le0 e2 = Le0
  _≤-trans_ (LeS e1) (LeS e2) = LeS (e1 ≤-trans e2)

  check≤ : (m n : Nat) → Either (m ≤ n) (n ≤ m)
  check≤ Z _ = Inl Le0
  check≤ (S m) Z = Inr Le0
  check≤ (S m) (S n) with check≤ m n
  ...                     | Inl p = Inl (LeS p)
  ...                     | Inr q = Inr (LeS q)

  max : Nat → Nat → Nat
  max n m with check≤ n m 
  ... | Inl _ = m
  ... | Inr _ = n

  max-≤ : {n m p : Nat} → n ≤ p → m ≤ p → max n m ≤ p
  max-≤ {n}{m} le1 le2 with check≤ n m 
  ... | Inl _ = le2
  ... | Inr _ = le1

  max-≥-1 : {a1 a2 : Nat} → a1 ≤ max a1 a2 
  max-≥-1 {a1}{a2} with check≤ a1 a2
  ... | Inl p = p
  ... | Inr q = ≤-refl _

  max-≥-2 : {a1 a2 : Nat} → a2 ≤ max a1 a2
  max-≥-2 {a1}{a2} with check≤ a1 a2
  ... | Inl p = ≤-refl _
  ... | Inr q = q

  max-monotone : {a1 a1' a2 a2' : Nat} → a1 ≤ a1' -> a2 ≤ a2' -> max a1 a2 ≤ max a1' a2'
  max-monotone{a1 = a1}{a1'}{a2}{a2'} lt1 lt2 = 
    max-≤ {n = a1} {m = a2} 
          (lt1 ≤-trans max-≥-1)
          (lt2 ≤-trans max-≥-2 {a1'} {a2'})

  module Filter (A : Set) (compare : A → A → Order) where
    
    data Tree (A : Set) : Set where
      Empty : Tree A
      Node : Tree A -> A → Tree A -> Tree A

    keeplt : Tree A → A → Tree A
    keeplt Empty x = Empty
    keeplt (Node l y r) x with compare x y
    ... | Less = keeplt l x
    ... | Equal = l
    ... | Greater = Node l y (keeplt r x)

    depth : {A : Set} → Tree A → Nat
    depth Empty = 0
    depth (Node l x r) = S (max (depth l) (depth r))

    thm : (t : _) (x : A) → depth (keeplt t x) ≤ depth t
    thm Empty x = Le0
    thm (Node l y r) x with compare x y
    thm (Node l y r) x | Less = (thm l x ≤-trans max-≥-1) ≤-trans ≤-S _
    thm (Node l y r) x | Equal = max-≥-1 ≤-trans ≤-S _
    thm (Node l y r) x | Greater = LeS (max-monotone (≤-refl (depth l)) (thm r x))
