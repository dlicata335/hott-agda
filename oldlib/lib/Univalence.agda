{-# OPTIONS --type-in-type --without-K #-}

open import lib.Paths 
open import lib.AdjointEquiv
open import lib.Prods
open Paths

module lib.Univalence where

  Type = Set

  postulate 
    univalence : ∀ {A B} -> IsAEq {Id A B} {AEq A B} (\ α -> subst(\ x -> AEq A x) α id⊣)
  
  ua : ∀ {A B} -> AEq A B -> Id A B
  ua = IsAEq.g univalence

  -- FIXME prove from univalence
  postulate
    subst-aeq-post : ∀ {A B C} {b : AEq B C} {a : AEq A B} -> Id (subst (\ X -> AEq A X) (ua b) a) (comp a b)
    subst-univ : {A B : Type} (w : AEq A B) -> Id (subst (\ A -> A) (ua w)) (_·⊢_ w)

    !-adj : {A B : Type} (f : A -> B) (feq : IsAEq f)
            (geq : IsAEq (_·⊣_ (f , feq)))
            -> (! (ua (f , feq))) ≃ (ua (_·⊣_ (f , feq) , geq))

  subst-univ-back : {A B : Type} {a : AEq A B}
             -> subst (\ x -> x) (! (ua a)) ≃ _·⊣_ a
  subst-univ-back {a = a} = subst-univ _ ∘ resp (subst (λ X → X)) (!-adj (fst a) (snd a) (snd (aeq-inv a)))