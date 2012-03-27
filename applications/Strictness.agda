{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open import applications.HigherHomotopyAbelian 
open Paths

module applications.Strictness where

   -- conjecture: if you make the functor laws hold definitionally,
   -- then each type is a *strict* omega groupoid
   --
   -- at least associativity holds up to equality
   -- can you get the other unit?  

   trans' : {A : Set} {M N P : A} -> Id M N -> Id N P -> Id M P
   trans' {A}{M}{N}{P} a b = Paths.subst (\ x -> Id M x) b a
  
   postulate -- suppose this held definitionally
     functor :  {A : Set} {M N P : A} -> (α : Id M N) -> (β : Id N P)
                {C : A -> Set} {m : C M}
             -> subst C (trans' α β) m ≃ subst C β (subst C α m)

   trans'-assoc : {A : Set} {M N P Q : A} -> (p : Id M N) (q : Id N P) (r : Id P Q) -> Id (trans' (trans' p q) r) (trans' p (trans' q r))
   trans'-assoc {A}{M}{N}{P}{Q} p q r = subst (Id M) r (subst (Id M) q p) ≃〈 ! (functor q r {Id M} {p}) 〉 
                                        subst (Id M) (trans' q r) p ≃〈 Refl 〉 
                                        (subst (Id M) (subst (Id N) r q) p ∎)

   trans'-unit-r : {A : Set} {M N : A} -> (p : Id M N) -> Id (trans' p Refl) p
   trans'-unit-r p = Refl

   trans'-unit-l : {A : Set} {M N : A} -> (p : Id M N) -> Id (trans' Refl p) p
   trans'-unit-l p = {!!}