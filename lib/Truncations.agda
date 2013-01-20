
{-# OPTIONS --no-termination-check --type-in-type #-}

open import lib.First
open import lib.Paths
open Paths
open import lib.Prods
open import lib.Functions
open import lib.Nat

module lib.Truncations where

  data TLevel : Type where
    -2 : TLevel 
    S : TLevel -> TLevel

  -1 : TLevel
  -1 = S -2

  tl : Nat -> TLevel
  tl Z = (S (S -2))
  tl (S n) = (S (tl n))

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

  -- want some control over unfolding
  mutual
    data IsTrunc : TLevel -> Type -> Type where
      istrunc  : ∀ {n} {A} → IsTrunc' n A -> IsTrunc n A
  
    IsTrunc' : TLevel -> Type -> Type 
    IsTrunc' -2 A = Contractible A
    IsTrunc' (S n) A = (x y : A) → IsTrunc n (Path x y)

  use-trunc : ∀ {n A} → IsTrunc n A -> IsTrunc' n A
  use-trunc (istrunc p) = p

  HProp : Type -> Type
  HProp A = IsTrunc -1 A

  HSet : Type -> Type
  HSet A = IsTrunc (tl 0) A

  postulate
    HSet-UIP : ∀ {A} -> HSet A -> (x y : A) (p q : x ≃ y) -> p ≃ q

  HGpd : Type -> Type
  HGpd A = IsTrunc (tl 1) A

  Contractible-Path : ∀ {A} -> Contractible A → (x y : A) -> Contractible (Path x y)
  Contractible-Path (acenter , apaths) x y = 
    contract (apaths y ∘ ! (apaths x)) 
             (λ α → move-left-right (apaths y) α (apaths x)
                      (! (apd apaths α ∘ ! (transport-Path-right α (apaths x)))))

  IsTrunc-Path : {n : TLevel} (A : Type) -> IsTrunc n A -> (x y : A) -> IsTrunc n (Path x y)
  IsTrunc-Path { -2 } A tA x y = istrunc (Contractible-Path (use-trunc tA) x y)
  IsTrunc-Path { S n } A tA x y = istrunc (λ p q → IsTrunc-Path {n} (Path x y) (use-trunc tA x y) p q)

  {-
  Contractible-is-HProp : (A : Type) -> HProp (Contractible A)
  Contractible-is-HProp A = λ c1 c2 → (pair≃ (fst (Contractible-Path c1 (fst c1) (fst c2))) {!snd (Contractible-Path c1 (fst c1) (fst c2)) !}) , 
                                      {!!}

  Trunc-is-HProp { -2 } A = Contractible-is-HProp A
  Trunc-is-HProp {S n} A = {!Trunc-is-HProp {n}  !}
  -}
  postulate
    IsTrunc-is-HProp   : {n : TLevel} (A : Type) -> HProp (IsTrunc n A)

  increment-IsTrunc : {n : TLevel} {A : Type} -> (IsTrunc n A) → (IsTrunc (S n) A)
  increment-IsTrunc {n}{A} tA = istrunc (λ x y → IsTrunc-Path {n} A tA x y)

  postulate 
    ΠIsTrunc : ∀{A n}{B : A → Type} → ((x : A) -> IsTrunc n (B x)) → IsTrunc n ((x : A) → B x)

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

    Trunc-elim : {A : Type} {n : TLevel} (C : Trunc n A → Type)
                (tC : (x : Trunc n A) → IsTrunc n (C x))
          -> ((x : A) → C [ x ])
          → (x : (Trunc n A)) → C x
    Trunc-elim _ _ f (trunc' x) = f x
   open T public

   τ₋₁ = Trunc -1
   τ₀ = Trunc (tl 0)
   τ₁ = Trunc (tl 1)
   τ₂ = Trunc (tl 2)

   module TruncPath {n : _} {A : _} {x y : A} where
     decode' : 
          (Trunc n (Path x y))
        → Path {(Trunc (S n) A)} [ x ] [ y ]
     decode' = Trunc-rec (use-trunc (Trunc-is {S n} {A}) [ x ] [ y ]) (ap [_]) 

     postulate
       encode' : 
           Path {(Trunc (S n) A)} [ x ] [ y ]
         → (Trunc n (Path x y))

       encode-decode' : encode' o decode' ≃ (\ x -> x)
       decode-encode' : decode' o encode' ≃ (\ x -> x)

   Trunc-simple-η : ∀ {n A} {y : Trunc n A} 
                  → Trunc-rec{A}{Trunc n A}{n} (Trunc-is{n}{A}) [_] y ≃ y
   Trunc-simple-η {n}{A}{y} = Trunc-elim (λ z → Path (Trunc-rec (Trunc-is{n}{A}) [_] z) z) 
                                      (λ x → IsTrunc-Path{n} _ (Trunc-is {n} {A}) _ _)
                                      (λ _ → id)
                                      y
                                      
   transport-Trunc : {n : TLevel} {Γ : Type} (A : Γ → Type) {θ1 θ2 : Γ} (δ : θ1 ≃ θ2)
                   →  transport (\ x -> Trunc n (A x)) δ 
                    ≃ Trunc-rec (Trunc-is {n} {A θ2}) (λ x → [ transport A δ x ])
   transport-Trunc A id = λ≃ (\ y -> ! (Trunc-simple-η {_} {_} {y}))

   -- avoid the λ≃ because it's annoying to unpack later
   transport-Trunc' : {n : TLevel} {Γ : Type} (A : Γ → Type) {θ1 θ2 : Γ} (δ : θ1 ≃ θ2) (y : Trunc n (A θ1))
                     →  transport (\ x -> Trunc n (A x)) δ y
                    ≃ Trunc-rec (Trunc-is {n} {A θ2}) (λ x → [ transport A δ x ]) y
   transport-Trunc' A id y = ! (Trunc-simple-η {_} {_} {y})

   Trunc-func : {n : TLevel} {A B : Type} -> (A -> B) -> (Trunc n A -> Trunc n B)
   Trunc-func f = Trunc-rec Trunc-is ([_] o f)

  