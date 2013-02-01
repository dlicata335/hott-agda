
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

  HSet-UIP : ∀ {A} -> HSet A -> (x y : A) (p q : x ≃ y) -> p ≃ q
  HSet-UIP h x y p q = fst (use-trunc (use-trunc (use-trunc h x y) p q))

  HProp-unique : ∀ {A} -> HProp A -> (x y : A) -> x ≃ y
  HProp-unique h x y = fst (use-trunc (use-trunc h x y))

  HGpd : Type -> Type
  HGpd A = IsTrunc (tl 1) A

  Contractible-Path : ∀ {A} -> Contractible A → (x y : A) -> Contractible (Path x y)
  Contractible-Path (acenter , apaths) x y = 
    contract (apaths y ∘ ! (apaths x)) 
             (λ α → move-left-right (apaths y) α (apaths x)
                      (! (apd apaths α ∘ ! (transport-Path-right α (apaths x)))))

  postulate 
    ΠIsTrunc : ∀{A n}{B : A → Type} → ((x : A) -> IsTrunc n (B x)) → IsTrunc n ((x : A) → B x)

  postulate
    use-trunc≃ : ∀ {n A} -> IsTrunc n A ≃ IsTrunc' n A
    -- arrange modules so we can use univalence here 

  postulate
    Contractible-is-HProp : (A : Type) -> HProp (Contractible A)
    -- Contractible-is-HProp A = {!!} 
    -- λ c1 c2 → (pair≃ (fst (Contractible-Path c1 (fst c1) (fst c2))) {!snd (Contractible-Path c1 (fst c1) (fst c2)) !}) , 
    --           {!!}

  IsTrunc-is-HProp   : {n : TLevel} (A : Type) -> HProp (IsTrunc n A)
  IsTrunc-is-HProp { -2 } A = transport (HProp) (! use-trunc≃) (Contractible-is-HProp A)
  IsTrunc-is-HProp {S n} A = transport HProp (! use-trunc≃) (ΠIsTrunc (λ _ → ΠIsTrunc (λ _ → IsTrunc-is-HProp {n} _)))

  -- in fact, it decrements, but often you want this lemma
  path-preserves-IsTrunc : {n : TLevel} {A : Type} -> IsTrunc n A -> {x y : A} -> IsTrunc n (Path x y)
  path-preserves-IsTrunc { -2 } {A} tA {x} {y} = istrunc (Contractible-Path (use-trunc tA) x y)
  path-preserves-IsTrunc { S n } {A} tA {x} {y} = istrunc (λ p q → path-preserves-IsTrunc (use-trunc tA x y))

  increment-IsTrunc : {n : TLevel} {A : Type} -> (IsTrunc n A) → (IsTrunc (S n) A)
  increment-IsTrunc {n}{A} tA = istrunc (λ x y → path-preserves-IsTrunc tA)


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

   NType : TLevel -> Type
   NType n = Σ \ (A : Type) → IsTrunc n A

   postulate
     IsTrunc-NType : ∀ n → IsTrunc (S n) (NType n)

   Trunc-simple-η : ∀ {n A} {y : Trunc n A} 
                  → Trunc-rec{A}{Trunc n A}{n} (Trunc-is{n}{A}) [_] y ≃ y
   Trunc-simple-η {n}{A}{y} = Trunc-elim (λ z → Path (Trunc-rec (Trunc-is{n}{A}) [_] z) z) 
                                         (λ x → path-preserves-IsTrunc (Trunc-is {n} {A}) )
                                         (λ _ → id)
                                         y
                                      
   transport-Trunc : {n : TLevel} {Γ : Type} (A : Γ → Type) {θ1 θ2 : Γ} (δ : θ1 ≃ θ2)
                   →  transport (\ x -> Trunc n (A x)) δ 
                    ≃ Trunc-rec (Trunc-is {n} {A θ2}) (λ x → [ transport A δ x ])
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
                    ≃ Trunc-rec (Trunc-is {n} {A θ2}) (λ x → [ transport A δ x ]) y
   transport-Trunc' A id y = ! (Trunc-simple-η {_} {_} {y})

   Trunc-func : {n : TLevel} {A B : Type} -> (A -> B) -> (Trunc n A -> Trunc n B)
   Trunc-func f = Trunc-rec Trunc-is ([_] o f)

   module TruncPath {n : _} {A : _} {x : A} where

     decode' : {y : _} → (Trunc n (Path x y)) → Path {(Trunc (S n) A)} [ x ] [ y ]
     decode' {y} = Trunc-rec (use-trunc (Trunc-is {S n} {A}) [ x ] [ y ]) (ap [_]) 

     Codes : Trunc (S n) A → NType n
     Codes = Trunc-rec (IsTrunc-NType n) 
                       (λ y → Trunc n (Path x y) , Trunc-is) 
     
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
     encode-decode' = Trunc-elim _ (λ x' → path-preserves-IsTrunc Trunc-is) 
       (λ α → transport (λ x' → fst (Trunc-rec (IsTrunc-NType n) (λ y → Trunc n (Id x y) , Trunc-is) x')) (ap [_] α) [ id ] ≃〈 ! (ap≃ (transport-ap-assoc' (λ x' → fst (Trunc-rec (IsTrunc-NType n) (λ y → Trunc n (Id x y) , Trunc-is) x')) [_] α)) 〉 
              transport (λ y → Trunc n (Id x y)) α [ id ] ≃〈 ap≃ (transport-Trunc (λ y → Id x y) α) 〉
              [ transport (\ y -> (Id x y)) α id ] ≃〈 ap [_] (transport-Path-right α id) 〉
              [ α ] ∎)

     decode : {y : Trunc (S n) A}
           → fst (Codes y)
           → Path {(Trunc (S n) A)} [ x ] y
     decode {y} = Trunc-elim (\ y -> fst (Codes y) → Path {(Trunc (S n) A)} [ x ] y)
                             (λ x' → ΠIsTrunc (λ x'' → path-preserves-IsTrunc Trunc-is))
                             (λ y' → decode' {y'})
                             y
 
     decode-encode : {y : _} (p : Path [ x ] y) → decode{y} (encode{y} p) ≃ p
     decode-encode id = id

     -- need to change module structure so we can wrap it up
     -- eqv : {y : A} -> Equiv (Trunc n (Path x y)) (Path {(Trunc (S n) A)} [ x ] [ y ])
     -- eqv {y} = improve (hequiv decode encode ? ?)

  