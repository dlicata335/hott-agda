{-# OPTIONS --without-K --type-in-type #-}

open import lib.First
open import lib.Paths
open import lib.Prods
open import lib.Sums
open import lib.Bool

module lib.DecidablePath where

  DecPath : Type -> Type
  DecPath A = (x y : A) -> Either (Path x y) (Path x y -> Void)

  -- Nicolai Kraus's version from the HoTT blog
  module Hedberg {A : Set} (d : DecPath A) (x : A) where

    Lemma : ∀ {y} → Path x y -> Type
    Lemma {y} α = Sums.case (\ _ -> Type) 
                            (\ b1 -> Sums.case (\ _ -> Type) 
                                               (\ b2 -> α ≃ b1 ∘ ! b2) 
                                               (\ _ -> Void)
                                               (d x x))
                            (\ _ -> Void)
                            (d x y)

    lemma : ∀ {y} → (α : Path x y) -> Lemma α
    lemma {.x} id with d x x 
    ... | Inl a = ! (!-inv-r a)
    ... | Inr r = r id

    UIP : {y : A} (p q : Path x y) -> p ≃ q
    UIP id q with d x x | lemma q 
    ... | Inl a | p' = ! p' ∘ ! (!-inv-r a)
    ... | Inr r | _ with r id
    ...                | ()

{-
  module Hedberg2 {A : Set} (d : DecPath A) where
    
    eq : A → A → Bool
    eq a a' with d a a'
    ... | Inl _ = True
    ... | Inr _ = False

    l : (a a' : A) → a == a' → BoolM.Check (eq a a')
    l a a' p with d a a'
    ... | Inl q = <>
    ... | Inr r = r p

    r : (a a' : A) → BoolM.Check (eq a a') → a == a'
    r a a' p with d a a'
    ... | Inl q = q
    ... | Inr r = Sums.abort p

    c1 : (a a' : A) → (p : _) → l a a' (r a a' p) == p
    c1 a a' p with d a a'
    ... | Inl q = id -- uses η for Unit, but we could work around that
    ... | Inr q = Sums.abort p

    -- c2 : (a a' : A) → (p : _) → r a a' (l a a' p) == p
    -- c2 a a' p with d a a'
    -- ... | Inl q = {!!}
    -- ... | Inr q = Sums.abort (q p)

    c2 : (a a' : A) → (p : _) → r a a' (l a a' p) == p
    c2 a .a id with d a a
    ... | Inl x = {!!}
    ... | Inr y = {!!}
    
-}
{-
  module Hedberg {A : Set} (d : DecPath A) (x : A) where

    open BoolM

    F : A -> Type
    F y = Check (forget (d x y))

    diagonal : Σ \ α → d x x ≃ Inl α
    diagonal with d x x 
    ... | Inl α = α , id
    ... | Inr r with r id
    ...            | ()

    refl : Check (forget (d x x))
    refl = transport (Check o forget) (! (snd diagonal)) <>

    encode : ∀ {y} → Path x y → F y
    encode α = transport F α refl

    decode : ∀ {y} → F y → Path x y
    decode {y} b with d x y
    ... | Inl α = α
    decode {y} () | Inr α

    encode-decode : ∀ {y} (b : F y) -> encode (decode b) ≃ b
    encode-decode {y} b = {!!}

    decode-encode : ∀ {y} (α : Path x y) -> decode (encode α) ≃ α
    decode-encode id with d x x
    decode-encode id | Inl y = {!!} -- need to have UIP already
    decode-encode id | Inr y with y id
    ... | ()

    decode-encode : ∀ {y} (α : Path x y) -> decode (encode α) ≃ α
    encode-decode : ∀ {y} (b : F y) -> encode (decode b) ≃ b
    encode-decode {y} b = {!!}

    decode-encode id with d x x
    decode-encode id | Inl y = {!!}
    decode-encode id | Inr y with y id
    ... | ()

  module Hedberg3 {A : Set} (d : DecPath A) (x : A) where

    center : {y : A} → Path x y -> Path x y
    center {y} α with d x y
    ... | Inl β = β
    ... | Inr r with r α
    ...            | ()

    diagonal-Inl : Σ \ α' → d x x ≃ Inl α'
    diagonal-Inl with d x x
    ... | Inl α' = α' , id
    ... | Inr r with r id
    ... | () 

    center-id : (α : Path x x) → center α ≃ {!fst (diagonal-Inl!}
    center-id α with d x x
    ... | Inl α' = {!!}
    ... | Inr r = {!!}
-}
