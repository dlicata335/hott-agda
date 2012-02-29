{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude hiding (WEq ; univalence ; subst-univ)
open Paths

module misc.SetExtFunExt  where

  record WEq (A B : Set0) : Set where
   field
    f : A -> B
    g : B -> A
    α : (a : A) -> Id (g (f a)) a
    β : (b : B) -> Id (f (g b)) b
    tri : (b : B) → Id (α (g b)) (resp g (β b))

  postulate 
    univalence : ∀ {A B} -> WEq A B -> Id{Set} A B
    subst-univ : {A B : Set} (w : WEq A B) -> Id (subst (\ A -> A) (univalence w)) (WEq.f w) 

  module WEqIsEpi where
    substIsEpi : {A B : Set} (p : Id A B) -> ∀ {C} (h h' : B -> C) -> Id (h o subst (\ A -> A) p) (h' o subst (\ A -> A) p) -> Id h h'
    substIsEpi pab = jay (\ A B p -> ∀ {C} (h h' : B -> C) -> Id (h o subst (\ A -> A) p) (h' o subst (\ A -> A) p) -> Id h h') pab (λ _ _ _ x → x)

    weqIsEpi : {A B : Set} (w : WEq A B) -> ∀ {C} (h h' : B -> C) -> Id (h o WEq.f w) (h' o WEq.f w) -> Id h h'
    weqIsEpi w h h' p = substIsEpi (univalence w) h h' (subst (λ x → Id (h o x) (h' o x)) (sym (subst-univ w)) p)

  -- anything is weakely equivalent to the arrow category over it
  module WEqArrow (B : Set) where
    B≅ = Σ (\(x : B) -> Σ \ y -> Id x y)

    f : B -> B≅
    f b = (b , b , Refl)

    g : Σ (\(x : B) -> Σ \ y -> Id x y) -> B
    g = fst

    α : (b : B) -> Id (g (f b)) b
    α b = Refl

    β : (p : B≅) -> Id (f (g p)) p
    β (a , b , p) = jay (λ a b p → Id (a , a , Refl) (a , b , p))
                        p 
                        (\ x -> Refl)

    tri : (p : B≅) → Id (α (g p)) (resp g (β p))
    tri (a , b , p) = jay (λ x y p' → Id Refl (resp fst (jay (λ x' y' p0 → Id{B≅} (x' , x' , Refl) (x' , y' , p0)) p' (λ x' → Refl)))) 
                          p 
                          (λ _ → Refl)

    tri2 : (b : B) → Id (β (f b)) (resp f (α b))
    tri2 b = Refl

    bweqb≅ : WEq B B≅
    bweqb≅ = record { f = f; g = g; α = α; β = β; tri = tri }

  module Exten where
    ext : {A B : Set} {h h' : A -> B} -> ((x : A) -> Id (h x) (h' x)) -> Id h h'
    ext {A}{B}{h}{h'} all =
        -- fst o k and (fst o snd) o k are equal, which gives the result by the way k is defined
        resp (λ x → x o k) epi 
     where
      -- by the second lemma, the map f : B -> B≅ is a weak equivalence 
      module BWeqArrow = WEqArrow B
      B≅ = BWeqArrow.B≅
      weq = BWeqArrow.bweqb≅  

      -- by the first lemma, it is therefore epi, so fst = fst o snd at B≅ -> B
      epi : Id fst (λ x → fst (snd x))
      epi =  WEqIsEpi.weqIsEpi weq fst (λ x → fst (snd x)) Refl

      -- define k to pair, h, h', and the proof that they are equal
      k : A -> B≅
      k a = h a , h' a , all a