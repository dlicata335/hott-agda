{-# OPTIONS --type-in-type --without-K #-}

-- FIXME get working again and move into lib

open import lib.Paths
open Paths
open import lib.Prods

module misc.TwoWeqs where

  Contractible : Set -> Set
  Contractible A = Σ \ (t : A) -> (x : A) -> Id t x

  HFiber : {A B : Set} -> (A -> B) -> B -> Set
  HFiber f y = Σ \x -> Id (f x) y

  IsWEq : {A B : Set} -> (f : A -> B) -> Set
  IsWEq f = (y : _) -> Contractible (HFiber f y)

  WEq : (A B : Set) -> Set
  WEq A B = Σ \(f : A -> B) -> IsWEq f

  record IsAdjointEquiv {A B : Set} (f : A -> B) : Set where
    constructor adj
    field
      g  : B -> A
      α : (y : _) -> Id (f (g y)) y
      β : (x : _) -> Id (g (f x)) x
--      γ : (y : _) → Id (Stuck.resp' g (α y)) (β (g y))
      γ : (x : _) → Id (α (f x)) (resp f (β x))

  
  -- FIXME do a nice version
  htoq : {A B : Set} (f : A -> B) -> IsWEq f -> IsAdjointEquiv f
  htoq f is = record { g = g; 
                       α = α; 
                       β = λ x → fst≃ (snd (is (f x)) (x , Refl)); 
                       γ = λ x → trans (trans (sym (trans-unit-r (snd (fst (is (f x)))))) (resp (λ h → trans (snd (fst (is (f x)))) h) (sym (resp-constant _ _))))
                                   (trans
                                    (sym
                                     (swap-left
                                      (trans (sym (snd≃ (snd (is (f x)) (x , Refl))))
                                       {! (subst-Id f (λ _ → f x)
                                        {p = resp fst (snd (is (f x)) (x , Refl))}
                                        {p' = snd (fst (is (f x)))}) !})))
                                    (trans-unit-r _)) } where --sndPath, then fire the subst, then massage
       g = λ y → fst (fst (is y))
       α = λ y → snd (fst (is y))

  qtoh : {A B : Set} {f : A -> B} -> IsAdjointEquiv f -> IsWEq f
  qtoh (adj g α β γ) = λ y → (g y , α y) , (λ x → pair≃ (trans (sym (resp g (snd x))) (β (fst x))) {!!})

