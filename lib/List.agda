{-# OPTIONS --type-in-type #-}

open import lib.First
open import lib.Paths
open import lib.Nat
open import lib.Maybe

module lib.List where

  data List (a : Type) : Type where
    []  : List a
    _::_ : a -> List a -> List a 

  {-# COMPILED_DATA List [] [] (:) #-}
  {-# BUILTIN LIST List #-}
  {-# BUILTIN NIL [] #-}
  {-# BUILTIN CONS _::_ #-}

  infixr 99 _::_

  module ListM where
    -- we expand this out, rather than using (Somewhere (\x -> Id x a) l)
    -- so that we don't have to write the silly identity proof in the deBruijn index 
    data _∈_ {A : Type} : A -> List A -> Type where
      i0 : {x : A}   {xs : List A} -> x ∈ (x :: xs )
      iS : {x y : A} {xs : List A} -> y ∈ xs -> y ∈ (x :: xs)
    infix 10 _∈_
  
    data Everywhere {A : Type} (P : A -> Type) : List A -> Type where
      E[] : Everywhere P []
      _E::_ : forall {x xs} -> P x -> Everywhere P xs -> Everywhere P (x :: xs) 
  
    infixr 98 _E::_
  
    [_] : {A : Type} -> A -> List A
    [_] x  = x :: []
  
    append : {A : Type} -> List A -> List A -> List A
    append [] l2 = l2
    append (x :: xs) l2 = x :: (append xs l2)
  
    _++_ : {A : Type} -> List A -> List A -> List A
    _++_ = append
    infixr 20 _++_

    length : {a : Type} -> List a -> Nat
    length [] = 0
    length (x :: xs) = S (length xs)
  
    fold : {a b : Type} -> b -> (a -> b -> b) -> List a -> b
    fold n c [] = n
    fold n c (x :: xs) = c x (fold n c xs)
  
    map : {a b : Type} -> (a -> b) -> List a -> List b
    map f [] = []
    map f (x :: xs) = f x :: (map f xs)

    nth : {A : Type} -> List A -> Nat -> Maybe A
    nth [] _ = None
    nth (x :: xs) 0 = Some x
    nth (x :: xs) (S n) = nth xs n

    tabulate' : {A : Type} -> (Nat -> A) -> Nat -> Nat -> List A
    tabulate' f 0 cur = []
    tabulate' f (S n) cur = f cur :: tabulate' f n (S cur)

    tabulate : {A : Type} -> (Nat -> A) -> Nat -> List A
    tabulate f n = tabulate' f n 0

    fuse-map : {A B C : Type} {f : A -> B} {g : B -> C} (l : List A) -> 
                map g (map f l)
              ≃ map (\ x -> g (f x)) l
    fuse-map [] = id
    fuse-map {f = f} {g = g} (x :: xs) = ap (\ xs -> (g (f x)) :: xs) (fuse-map xs)
