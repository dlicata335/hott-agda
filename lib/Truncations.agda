
{-# OPTIONS --no-termination-check --type-in-type #-}

open import lib.First
open import lib.Paths
open Paths
open import lib.Prods
open import lib.Functions

module lib.Truncations where

  data TLevel : Type where
    -2 : TLevel 
    S : TLevel -> TLevel
  
  {-
  record Contractible (A : Type) : Type where
    constructor 
    field
      center : A
      paths  : (x : A) -> Path center x
  -}

  Contractible : Type -> Type
  Contractible A = Σ \(c : A) → (y : A) → Path c y

  contract : {A : Type} -> (x : A) -> ((y : A) -> Path x y) -> Contractible A
  contract = _,_

  IsTrunc : TLevel -> Type -> Type
  IsTrunc -2 A = Contractible A
  IsTrunc (S n) A = (x y : A) → IsTrunc n (Path x y)

  HProp : Type -> Type
  HProp A = IsTrunc (S -2) A

  HSet : Type -> Type
  HSet A = IsTrunc (S (S -2)) A

  HGpd : Type -> Type
  HGpd A = IsTrunc (S (S (S -2))) A

  Contractible-Path : ∀ {A} -> Contractible A → (x y : A) -> Contractible (Path x y)
  Contractible-Path (acenter , apaths) x y = 
    contract (apaths y ∘ ! (apaths x)) 
             (λ α → move-left-right (apaths y) α (apaths x)
                      (! (apd apaths α ∘ ! (transport-Path-right α (apaths x)))))

  IsTrunc-Path : {n : TLevel} (A : Type) -> IsTrunc n A -> (x y : A) -> IsTrunc n (Path x y)
  IsTrunc-Path { -2 } A tA x y = Contractible-Path tA x y
  IsTrunc-Path { S n } A tA x y = λ p q → IsTrunc-Path {n} (Path x y) (tA x y) p q

  {-
  Contractible-is-HProp : (A : Type) -> HProp (Contractible A)
  Contractible-is-HProp A = λ c1 c2 → (pair≃ (fst (Contractible-Path c1 (fst c1) (fst c2))) {!snd (Contractible-Path c1 (fst c1) (fst c2)) !}) , 
                                      {!!}

  Trunc-is-HProp : {n : TLevel} (A : Type) -> HProp (IsTrunc n A)
  Trunc-is-HProp { -2 } A = Contractible-is-HProp A
  Trunc-is-HProp {S n} A = {!Trunc-is-HProp {n}  !}
  -}

  module Truncation where

   module T where
    private
      data Trunc' (n : TLevel) (A : Type) : Type where
        trunc' : A -> Trunc' n A

    Trunc : (n : TLevel) (A : Type) → Type
    Trunc = Trunc' 

    [_] : {n : TLevel} {A : Type} → A -> Trunc n A
    [ x ] = trunc' x

    postulate 
      Trunc-is : {n : TLevel} {A : Type} → IsTrunc n (Trunc n A)

    Trunc-rec : {A C : Type} {n : TLevel} (tC : IsTrunc n C)
          -> (A → C)
          → (Trunc n A) → C
    Trunc-rec _ f (trunc' x) = f x

    Trunc-elim : {A : Type} {n : TLevel} {C : Trunc n A → Type} 
                (tC : (x : Trunc n A) → IsTrunc n (C x))
          -> ((x : A) → C [ x ])
          → (x : (Trunc n A)) → C x
    Trunc-elim _ f (trunc' x) = f x
   open T public

   τ₋₁ = Trunc (S -2)
   τ₀ = Trunc (S (S -2))
   τ₁ = Trunc (S (S (S -2)))

   module TruncPath {n : _} {A : _} {x y : A} where
     decode' : 
          (Trunc n (Path x y))
        → Path {(Trunc (S n) A)} [ x ] [ y ]
     decode' = Trunc-rec (Trunc-is {S n} {A} [ x ] [ y ]) (ap [_]) 

     postulate
       encode' : 
           Path {(Trunc (S n) A)} [ x ] [ y ]
         → (Trunc n (Path x y))

       encode-decode : encode' o decode' ≃ (\ x -> x)
       decode-encode : decode' o encode' ≃ (\ x -> x)


    