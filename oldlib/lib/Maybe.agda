{-# OPTIONS --type-in-type #-}

open import lib.Bool
open BoolM

module lib.Maybe where

  data Maybe (a : Set) : Set where
    Some : a -> Maybe a
    None : Maybe a

  module MaybeM where
    mapMaybe : ∀ {A B} -> (A -> B) -> Maybe A -> Maybe B
    mapMaybe f (Some x) = Some (f x)
    mapMaybe f None = None

    isSome : ∀ {A} → Maybe A → Bool 
    isSome (Some _) = True
    isSome None = False

    valOf : ∀ {A} (s : Maybe A) → {_ : Check (isSome s)} → A
    valOf (Some x) = x
    valOf None {()}

    getSome : {A : Set} (s : Maybe A) -> {_ : Check (isSome s)} -> A
    getSome = valOf

    solve : {A : Set} (s : Maybe A) -> {_ : Check (isSome s)} -> A
    solve = getSome

    case_None⇒_Some⇒ : ∀ {A C : Set} -> (Maybe A) -> C -> (A -> C) -> C
    case None None⇒ e1 Some⇒ e2 = e1
    case (Some x) None⇒ e1 Some⇒ e2 = e2 x

    none⇒_some⇒ : ∀ {A C : Set} -> C -> (A -> C) -> Maybe A -> C
    none⇒ n some⇒ y e = case e None⇒ n Some⇒ y

    forgetMaybe2  : {a : Set}{C : a -> a -> Set}  -> ((x : a) -> (y : a) -> Maybe (C x y)) -> (a -> a -> Bool)
    forgetMaybe2 f x y  with (f x y) 
    ...                | Some t = True
    ...                | None = False
