
{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open Paths
open import lib.Nat
open import lib.Prods

module lib.NTypes where

  data TLevel : Type where
    -2 : TLevel 
    S : TLevel -> TLevel

  -1 : TLevel
  -1 = S -2

  tl : Nat -> TLevel
  tl Z = (S (S -2))
  tl (S n) = (S (tl n))

  {-
  record Contractible (A : Type) : Type where
    constructor 
    field
      center : A
      paths  : (x : A) -> Path center x
  -}

  Contractible : Type -> Type
  Contractible A = Σ \(c : A) → (y : A) → Path c y

  contract : {A : Type} -> (x : A) -> ((y : A) -> Path x y) -> Contractible A
  contract = _,_

  -- want some control over unfolding
  mutual
    data NType (n : TLevel) (A : Type) : Type where
      ntype  : NType' n A -> NType n A
  
    NType' : TLevel -> Type -> Type 
    NType' -2 A = Contractible A
    NType' (S n) A = (x y : A) → NType n (Path x y)

  use-level : ∀ {n A} → NType n A -> NType' n A
  use-level (ntype p) = p

  HProp : Type -> Type
  HProp A = NType -1 A

  HSet : Type -> Type
  HSet A = NType (tl 0) A

  HSet-UIP : ∀ {A} -> HSet A -> (x y : A) (p q : x ≃ y) -> p ≃ q
  HSet-UIP h x y p q = fst (use-level (use-level (use-level h x y) p q))

  HProp-unique : ∀ {A} -> HProp A -> (x y : A) -> x ≃ y
  HProp-unique h x y = fst (use-level (use-level h x y))

  unique-HProp : ∀ {A} -> ((x y : A) -> x ≃ y) -> HProp A
  unique-HProp f = ntype (λ x y → ntype (f x y , contra)) where
    contra : ∀ {x y} → (α : Path x y) → Path (f x y) α
    contra {x} id = square-id (f x x) (! lemma) where 
       lemma = 
               f x x ≃〈 ! (apd (f x) (f x x)) 〉 
               transport (λ z → Id x z) (f x x) (f x x) ≃〈 transport-Path-right (f x x) (f x x) 〉 
               (f x x ∘ (f x x)) ∎

  UIP-HSet : ∀ {A} -> ((x y : A) (p q : x ≃ y) -> p ≃ q) → HSet A 
  UIP-HSet u = ntype (λ x y → unique-HProp (u _ _))
  
  HGpd : Type -> Type
  HGpd A = NType (tl 1) A

  Contractible-Path : ∀ {A} -> Contractible A → (x y : A) -> Contractible (Path x y)
  Contractible-Path (acenter , apaths) x y = 
    contract (apaths y ∘ ! (apaths x)) 
             (λ α → move-left-right (apaths y) α (apaths x)
                      (! (apd apaths α ∘ ! (transport-Path-right α (apaths x)))))

  NTypes : TLevel -> Type
  NTypes n = Σ \ (A : Type) → NType n A


