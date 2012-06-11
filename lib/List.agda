{-# OPTIONS --type-in-type #-}

open import lib.Paths
open import lib.Nat
open import lib.Maybe

module lib.List where

  data List (a : Set) : Set where
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
    data _∈_ {A : Set} : A -> List A -> Set where
      i0 : {x : A}   {xs : List A} -> x ∈ (x :: xs )
      iS : {x y : A} {xs : List A} -> y ∈ xs -> y ∈ (x :: xs)
    infix 10 _∈_
  
    data Everywhere {A : Set} (P : A -> Set) : List A -> Set where
      E[] : Everywhere P []
      _E::_ : forall {x xs} -> P x -> Everywhere P xs -> Everywhere P (x :: xs) 
  
    infixr 98 _E::_
  
    [_] : {A : Set} -> A -> List A
    [_] x  = x :: []
  
    append : {A : Set} -> List A -> List A -> List A
    append [] l2 = l2
    append (x :: xs) l2 = x :: (append xs l2)
  
    _++_ : {A : Set} -> List A -> List A -> List A
    _++_ = append
    infixr 20 _++_

    length : {a : Set} -> List a -> Nat
    length [] = 0
    length (x :: xs) = S (length xs)
  
    fold : {a b : Set} -> b -> (a -> b -> b) -> List a -> b
    fold n c [] = n
    fold n c (x :: xs) = c x (fold n c xs)
  
    map : {a b : Set} -> (a -> b) -> List a -> List b
    map f [] = []
    map f (x :: xs) = f x :: (map f xs)

    nth : {A : Set} -> List A -> Nat -> Maybe A
    nth [] _ = None
    nth (x :: xs) 0 = Some x
    nth (x :: xs) (S n) = nth xs n

    tabulate' : {A : Set} -> (Nat -> A) -> Nat -> Nat -> List A
    tabulate' f 0 cur = []
    tabulate' f (S n) cur = f cur :: tabulate' f n (S cur)

    tabulate : {A : Set} -> (Nat -> A) -> Nat -> List A
    tabulate f n = tabulate' f n 0

    fuse-map : {A B C : Set} {f : A -> B} {g : B -> C} (l : List A) -> 
                map g (map f l)
              ≃ map (\ x -> g (f x)) l
    fuse-map [] = Refl
    fuse-map {f = f} {g = g} (x :: xs) = Paths.resp (\ xs -> (g (f x)) :: xs) (fuse-map xs)
