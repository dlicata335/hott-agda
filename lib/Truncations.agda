
{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open import lib.Prods
open import lib.Sums
open import lib.Functions
open import lib.Nat
open import lib.NType
open import lib.Universe
open import lib.AdjointEquiv

module lib.Truncations where

  module Truncation where

   module T where
    private
      data Trunc' (n : TLevel) (A : Type) : Type where
        trunc' : A -> Trunc' n A

    Trunc : (n : TLevel) (A : Type) → Type
    Trunc = Trunc' 

    [_] : {n : TLevel} {A : Type} → A -> Trunc n A
    [ x ] = trunc' x

    postulate {- HoTT Axiom -}
      Trunc-level : {n : TLevel} {A : Type} → NType n (Trunc n A)

    Trunc-rec : {A C : Type} {n : TLevel} (tC : NType n C)
          -> (A → C)
          → (Trunc n A) → C
    Trunc-rec _ f (trunc' x) = f x

    Trunc-elim : {A : Type} {n : TLevel} (C : Trunc n A → Type)
                (tC : (x : Trunc n A) → NType n (C x))
          -> ((x : A) → C [ x ])
          → (x : (Trunc n A)) → C x
    Trunc-elim _ _ f (trunc' x) = f x
   open T public

   τ₋₁ = Trunc -1
   τ₀ = Trunc (tl 0)
   τ₁ = Trunc (tl 1)
   τ₂ = Trunc (tl 2)

   Trunc-simple-η : ∀ {n A} {y : Trunc n A} 
                  → Trunc-rec{A}{Trunc n A}{n} (Trunc-level{n}{A}) [_] y ≃ y
   Trunc-simple-η {n}{A}{y} = Trunc-elim (λ z → Path (Trunc-rec (Trunc-level{n}{A}) [_] z) z) 
                                         (λ x → path-preserves-level (Trunc-level {n} {A}) )
                                         (λ _ → id)
                                         y
                                      
   transport-Trunc : {n : TLevel} {Γ : Type} (A : Γ → Type) {θ1 θ2 : Γ} (δ : θ1 ≃ θ2)
                   →  transport (\ x -> Trunc n (A x)) δ 
                    ≃ Trunc-rec (Trunc-level {n} {A θ2}) (λ x → [ transport A δ x ])
   transport-Trunc A id = λ≃ (\ y -> ! (Trunc-simple-η {_} {_} {y}))

   transport-Trunc-tlevel : {n k : TLevel} (A : Type) (a : A) (δ : n ≃ k)
                   →  transport (\ x -> Trunc x A) δ [ a ] ≃ [ a ]
   transport-Trunc-tlevel A a id = id

   coe-Trunc-tlevel : {n k : TLevel} (A : Type) (a : A) (δ : n ≃ k)
                   →  coe (ap (\ x -> Trunc x A) δ) [ a ] ≃ [ a ]
   coe-Trunc-tlevel A a id = id

   -- avoid the λ≃ because it's annoying to unpack later
   transport-Trunc' : {n : TLevel} {Γ : Type} (A : Γ → Type) {θ1 θ2 : Γ} (δ : θ1 ≃ θ2) (y : Trunc n (A θ1))
                     →  transport (\ x -> Trunc n (A x)) δ y
                    ≃ Trunc-rec (Trunc-level {n} {A θ2}) (λ x → [ transport A δ x ]) y
   transport-Trunc' A id y = ! (Trunc-simple-η {_} {_} {y})

   Trunc-func : {n : TLevel} {A B : Type} -> (A -> B) -> (Trunc n A -> Trunc n B)
   Trunc-func f = Trunc-rec Trunc-level ([_] o f)

   Trunc-reflective : ∀ k {A} -> NType k A → Trunc k A ≃ A
   Trunc-reflective k tA = ua (improve (hequiv (Trunc-rec tA (λ x → x)) [_] (Trunc-elim _ (λ _ → path-preserves-level Trunc-level) (λ _ → id)) (λ _ → id)))

   module TruncPath (n : _) {A : _} {x : A} where

     decode' : {y : _} → (Trunc n (Path x y)) → Path {(Trunc (S n) A)} [ x ] [ y ]
     decode' {y} = Trunc-rec (use-level (Trunc-level {S n} {A}) [ x ] [ y ]) (ap [_]) 

     Codes : Trunc (S n) A → NTypes n
     Codes = Trunc-rec (NTypes-level n) 
                       (λ y → Trunc n (Path x y) , Trunc-level) 
     
     encode : {y : Trunc (S n) A}
           → Path {(Trunc (S n) A)} [ x ] y
           → fst (Codes y)
     encode α = transport (fst o Codes) α [ id ]

     encode' : {y : A}
           → Path {(Trunc (S n) A)} [ x ] [ y ]
           → (Trunc n (Path x y))
     encode'{y} = encode {[ y ]}

     encode-decode' : {y : A} (c : fst (Codes [ y ]))
                    → encode'{y} (decode'{y} c) ≃ c
     encode-decode' = Trunc-elim _ (λ x' → path-preserves-level Trunc-level) 
       (λ α → transport (λ x' → fst (Trunc-rec (NTypes-level n) (λ y → Trunc n (Id x y) , Trunc-level) x')) (ap [_] α) [ id ] ≃〈 ! (ap≃ (transport-ap-assoc' (λ x' → fst (Trunc-rec (NTypes-level n) (λ y → Trunc n (Id x y) , Trunc-level) x')) [_] α)) 〉 
              transport (λ y → Trunc n (Id x y)) α [ id ] ≃〈 ap≃ (transport-Trunc (λ y → Id x y) α) 〉
              [ transport (\ y -> (Id x y)) α id ] ≃〈 ap [_] (transport-Path-right α id) 〉
              [ α ] ∎)

     decode : {y : Trunc (S n) A}
           → fst (Codes y)
           → Path {(Trunc (S n) A)} [ x ] y
     decode {y} = Trunc-elim (\ y -> fst (Codes y) → Path {(Trunc (S n) A)} [ x ] y)
                             (λ x' → Πlevel (λ x'' → path-preserves-level Trunc-level))
                             (λ y' → decode' {y'})
                             y
 
     decode-encode : {y : _} (p : Path [ x ] y) → decode{y} (encode{y} p) ≃ p
     decode-encode id = id

     eqv : {y : A} -> Equiv (Trunc n (Path x y)) (Path {(Trunc (S n) A)} [ x ] [ y ])
     eqv {y} = improve (hequiv decode encode encode-decode' decode-encode)

     path : {y : A} -> (Trunc n (Path x y)) ≃ (Path {(Trunc (S n) A)} [ x ] [ y ])
     path {y} = ua eqv

