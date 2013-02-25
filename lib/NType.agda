
{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open import lib.Nat
open import lib.Prods
open import lib.Sums
open import lib.Functions

module lib.NType where

  tl : Nat -> TLevel
  tl Z = (S (S -2))
  tl (S n) = (S (tl n))

  -- less than for tlevels
  data _<tl_ : TLevel -> TLevel -> Type where
    ltS   : ∀ {m} → m <tl (S m)
    ltSR  : ∀ {n m} → n <tl m → n <tl (S m)

  lt-subtract-left : ∀ {n m} -> (S n) <tl m → n <tl m
  lt-subtract-left ltS = ltSR ltS
  lt-subtract-left (ltSR lt) = ltSR (lt-subtract-left lt)

  lt-unS : ∀ {n m} → (S n) <tl (S m) → n <tl m
  lt-unS ltS = ltS
  lt-unS (ltSR lt) = lt-subtract-left lt

  lt-unS-right : ∀ {n m} → n <tl (S m) → Either (n <tl m) (m ≃ n)
  lt-unS-right ltS = Inr id
  lt-unS-right (ltSR y) = Inl y

  nothing<-2 : ∀ {n} -> n <tl -2 -> Void
  nothing<-2 ()

  -2< : ∀ n -> -2 <tl (S n)
  -2< -2 = ltS 
  -2< (S n) = ltSR (-2< n) 

  -2<nat : ∀ n → -2 <tl (tl n)
  -2<nat Z = ltSR ltS
  -2<nat (S y) = ltSR (-2<nat y)

  ltSCong : ∀ {n} {m} -> n <tl m -> (S n) <tl (S m)
  ltSCong {n} { -2 } () 
  ltSCong { -2 } {(S -2)} lt = ltS
  ltSCong { -2 } { (S (S y)) } (ltSR lt') = ltSR (ltSCong lt')
  ltSCong { (S y) } { (S y') } lt with lt-unS-right lt
  ... | Inl a = ltSR (ltSCong a) 
  ... | Inr b = transport (λ x → S (S y) <tl x) (ap (S o S) (! b)) ltS 

  -- less than or equal to for tlevel
  _<=tl_ : TLevel -> TLevel -> Type 
  x <=tl y = Either (x <tl y) (x ≃ y)

  -1<= : ∀ {n} -> -2 <tl n → -1 <=tl n
  -1<= { -2 } () 
  -1<= {(S -2)} lt = Inr id
  -1<= {(S (S n))} (ltSR lt') = Inl (ltSCong lt')

  -2<= : ∀ n -> -2 <=tl n
  -2<= -2 = Inr id
  -2<= (S n) = Inl (-2< n)

  <=-unS : ∀ {n m} → (S n) <=tl (S m) → n <=tl m
  <=-unS (Inl lt) = Inl (lt-unS lt)
  <=-unS (Inr e) = Inr (ap tpred e) where
    tpred : TLevel -> TLevel
    tpred (S n) = n
    tpred -2 = -2

  <=SCong : ∀ {n} {m} -> n <=tl m -> (S n) <=tl (S m)
  <=SCong (Inl lt) = Inl (ltSCong lt)
  <=SCong (Inr eq) = Inr (ap S eq)


  -- min for tlevels
  mintl : TLevel -> TLevel -> TLevel 
  mintl -2 n = -2
  mintl m -2 = -2
  mintl (S m) (S n) = S (mintl m n)

  mintl<=1 : (m n : TLevel) -> mintl m n <=tl m 
  mintl<=1 -2 n = Inr id
  mintl<=1 (S m) -2 = Inl (-2< m)
  mintl<=1 (S m) (S n) with mintl<=1 m n
  ... | Inl lt = Inl (ltSCong lt)
  ... | Inr eq = Inr (ap S eq)

  mintl<=2 : (m n : TLevel) -> mintl m n <=tl n
  mintl<=2 -2 n = -2<= n
  mintl<=2 (S m) -2 = Inr id
  mintl<=2 (S m) (S n) with mintl<=2 m n
  ... | Inl lt = Inl (ltSCong lt)
  ... | Inr eq = Inr (ap S eq)

  mintl-comm : (m n : TLevel) → mintl m n ≃ mintl n m
  mintl-comm -2 -2 = id
  mintl-comm -2 (S n) = id
  mintl-comm (S m) -2 = id
  mintl-comm (S m) (S n) = ap S (mintl-comm m n)

  -- funny addition for tlevels
  -- n + m + 2
  -- (not total otherwise)
  plus2 : TLevel -> TLevel -> TLevel
  plus2 -2 n = n
  plus2 (S n) m = S (plus2 n m)


  -- alternate characterizations

  contract : {A : Type} -> (x : A) -> ((y : A) -> Path x y) -> Contractible A
  contract = _,_

  use-level≃ : ∀ {n A} -> NType n A ≃ NType' n A
  use-level≃ = ua (improve (hequiv use-level ntype (\ {(ntype _)  -> id}) (\ x -> id)))


  -- more weakening

  abstract
    raise-HProp : ∀ {n} {A : Type} → HProp A → NType (S n) A
    raise-HProp { -2 } hA = hA
    raise-HProp {S n} hA = increment-level (raise-HProp hA)

    raise-level : ∀ {n m} {A} -> n <=tl m -> NType n A -> NType m A
    raise-level (Inl ltS) nA = increment-level nA
    raise-level (Inl (ltSR y)) nA = increment-level (raise-level (Inl y) nA)
    raise-level (Inr id) nA = nA

  -- level of NType predicate

  abstract 
    Contractible-is-HProp : (A : Type) -> HProp (Contractible A)
    Contractible-is-HProp A = unique-HProp 
      (λ p q → pair≃ (snd p (fst q)) 
                     (λ≃ (λ x → transport (λ v → (y : A) → Path v y) (snd p (fst q)) (snd p) x ≃〈 ap≃ (transport-Π-post' Path (snd p (fst q)) (snd p))〉 
                                transport (λ v → Path v x) (snd p (fst q)) (snd p x) ≃〈 transport-Path-pre (snd p (fst q)) (snd p x)〉 
                                (snd p x) ∘ ! (snd p (fst q)) ≃〈 rearrange (snd p x) (snd p (fst q)) (snd q x) (STS p q x)〉 
                                snd q x ∎))) where
      STS : (p q : Contractible A) (x : A) -> snd q x ∘ snd p (fst q) ≃ (snd p x)
      STS p q x = 
        ((snd q x) ∘ (snd p (fst q))) ≃〈 ! (transport-Path-right (snd q x) (snd p (fst q))) 〉 
        (transport (λ z → Id (fst p) z) (snd q x) (snd p (fst q))) ≃〈 apd (snd p) (snd q x) 〉 
        (snd p x) ∎
      rearrange : {a b c : A} (α : a ≃ b) (β : a ≃ c) (γ : c ≃ b) → (γ ∘ β ≃ α) → (α ∘ ! β ≃ γ) 
      rearrange id id g = !
  
    NType-is-HProp   : {n : TLevel} (A : Type) -> HProp (NType n A)
    NType-is-HProp { -2 } A = transport (HProp) (! use-level≃) (Contractible-is-HProp A)
    NType-is-HProp {S n} A = transport HProp (! use-level≃) (Πlevel (λ _ → Πlevel (λ _ → NType-is-HProp {n} _)))


  -- lemmas about contractibility

  out-of-contractible : ∀ {A C} (f : A -> C) (cA : NType -2 A) (a b : A)
                      → f a ≃ f b
  out-of-contractible f cA _ _ = ap f (HProp-unique (increment-level cA) _ _ )

  out-of-contractible-id : ∀ {A C} (f : A -> C) (cA : NType -2 A) (a : A)
                         → out-of-contractible f cA a a ≃ id
  out-of-contractible-id f cA a = ap (ap f) (HSet-UIP (increment-level (increment-level cA)) _ _ _ id)

