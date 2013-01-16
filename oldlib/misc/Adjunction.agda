
{-# OPTIONS --type-in-type --without-K #-}

-- ???? can we do adjunctions as isomorphism of hom-sets? 

open import lib.Prelude

module misc.Adjunction where


  Adjunction : {A B : Set} (F : A -> B) (G : B -> A) -> Set
  Adjunction {A}{B} F G = (x : A) (y : B) -> WEq (Id (F x) y) (Id x (G y))

  naturalx☆ : {A B : Set} (F : A -> B) (G : B -> A) (i : Adjunction F G) 
            -> {x x' : A} {y : B} 
            -> (p : Id x x')
            -> Id {!trans ? (i ☆ x)!} {!!} 
  naturalx☆ F G i p = {!!}