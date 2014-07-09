
{-# OPTIONS --type-in-type --new-without-K #-}

open import lib.First
open import lib.NType
open import lib.Universe

module lib.Groupoid where

 module Groupoid where
  Ident : ∀ {A} -> (A -> A -> Type) -> Type
  Ident Arr = ∀ {x} -> Arr x x

  Inv : ∀ {A} -> (A -> A -> Type) -> Type
  Inv Arr = ∀ {x y} -> Arr x y -> Arr y x

  Comp : ∀ {A} -> (A -> A -> Type) -> Type
  Comp Arr = ∀ {x y z} -> Arr x y -> Arr y z -> Arr x z

  record Gpd : Type where
   field
    Ob   : Type
    Arr  : Ob -> Ob -> Type
    Arr-level  : ∀ {x y} -> NType (tl 0) (Arr x y)
    ident   : ∀ {x} -> Arr x x
    inv     : ∀ {x y} -> Arr x y -> Arr y x
    comp    : ∀ {x y z} -> Arr x y -> Arr y z -> Arr x z
  open Gpd
  
  Reify : (A : NTypes (tl 1)) -> Gpd 
  Reify (A , A-level) = record { Ob = A; Arr = Id; Arr-level = use-level A-level _ _; ident = id; inv = !; comp = \ x y -> y ∘ x }

  ActionOnArrows : {A B : Gpd} -> (f : Ob A -> Ob B) -> Set
  ActionOnArrows{A}{B} _·_ = ∀ {x y} -> Arr A x y -> Arr B (_·_ x) (_·_ y)

  record Func (A B : Gpd) : Set where
    constructor func
    field
      _·_ : Ob A -> Ob B
      _⊙_ : ActionOnArrows{A}{B} _·_
      
  open Func

  idfunc : ∀ {A} -> Func A A
  idfunc = func (\ x -> x) (\ x -> x)

  _∘f_ : ∀ {A B C} -> Func B C -> Func A B -> Func A C
  F ∘f G = func (\ x -> F · (G · x)) (λ p → F ⊙ (G ⊙ p))

