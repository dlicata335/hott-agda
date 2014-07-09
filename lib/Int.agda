{-# OPTIONS --type-in-type --without-K #-}

open import lib.First public
open import lib.Paths public
open import lib.Prods public
open import lib.Sums public
open import lib.AdjointEquiv 
open import lib.NType
open import lib.Truncations
open Truncation
open import lib.Nat
open import lib.DecidablePath


module lib.Int where

module Int where
  data Positive : Type where
    One : Positive
    S   : (n : Positive) → Positive

  _+1 : Positive -> Positive
  _+1 = S

  data Int : Type where
    Pos  : (n : Positive) → Int
    Zero : Int
    Neg  : (n : Positive) → Int
 
  succ : Int → Int
  succ Zero = Pos One
  succ (Pos n) = Pos (S n)
  succ (Neg One) = Zero
  succ (Neg (S n)) = Neg n
 
  pred : Int → Int
  pred Zero = Neg One
  pred (Pos (S n)) = Pos n
  pred (Pos One) = Zero
  pred (Neg n) = Neg (S n)
 
  _+_ : Int → Int → Int
  Zero + m        = m
  (Pos One) + m   = succ m
  (Pos (S n)) + m = succ (Pos n  +  m)
  (Neg One)   + m = pred m
  (Neg (S n)) + m = pred (Neg n  +  m)
 
  succ-pred : (n : Int) → Path (succ (pred n)) n
  succ-pred (Pos One) = id
  succ-pred (Pos (S y)) = id
  succ-pred (Zero) = id
  succ-pred (Neg y) = id
 
  pred-succ : (n : Int) → Path (pred (succ n)) n
  pred-succ (Pos y) = id
  pred-succ (Zero) = id
  pred-succ (Neg One) = id
  pred-succ (Neg (S y)) = id
 
  succ-pred-triangle : (x : _) → Id (succ-pred (succ x)) (ap succ (pred-succ x))
  succ-pred-triangle (Pos y) = id
  succ-pred-triangle Zero = id
  succ-pred-triangle (Neg One) = id
  succ-pred-triangle (Neg (S y)) = id
 
  pred-succ-triangle : (x : _) → Id (pred-succ (pred x)) (ap pred (succ-pred x))
  pred-succ-triangle (Pos One) = id
  pred-succ-triangle (Pos (S _)) = id
  pred-succ-triangle Zero = id
  pred-succ-triangle (Neg y) = id
 
  succEquiv : Equiv Int Int
  succEquiv = improve (hequiv succ pred pred-succ succ-pred)


  -- decidable equality and sets

  tpred : Positive -> Positive
  tpred One = One
  tpred (S n) = n

  decidePath-Positive : DecPath Positive
  decidePath-Positive One One = Inl id
  decidePath-Positive One (S n) = Inr (λ ())
  decidePath-Positive (S n) One = Inr (λ ())
  decidePath-Positive (S n) (S n') = lemma (decidePath-Positive n n') where
    lemma : Either (n == n') (n == n' → Void) → Either (S n == S n') (S n == S n' → Void)
    lemma (Inl p) = Inl (ap S p)
    lemma (Inr p) = Inr (λ x → p (ap tpred x))
  
  outject : Int -> Positive
  outject (Pos n) = n
  outject (Neg n) = n
  outject (Zero) = One

  decidePath-Int : DecPath Int
  decidePath-Int (Pos n) (Pos n') with decidePath-Positive n n' 
  ... | Inl x = Inl (ap Pos x)
  ... | Inr x = Inr (x o ap outject)
  decidePath-Int (Pos n) Zero = Inr (λ ())
  decidePath-Int (Pos n) (Neg n') = Inr (λ ())
  decidePath-Int Zero (Pos n) = Inr (λ ())
  decidePath-Int Zero Zero = Inl id
  decidePath-Int Zero (Neg n) = Inr (λ ())
  decidePath-Int (Neg n) (Pos n') = Inr (λ ())
  decidePath-Int (Neg n) Zero = Inr (λ ())
  decidePath-Int (Neg n) (Neg n') with decidePath-Positive n n' 
  ... | Inl x = Inl (ap Neg x)
  ... | Inr x = Inr (x o ap outject)

  abstract
    HSet-Int : HSet Int
    HSet-Int = UIP-HSet (λ x y p q → Hedberg.UIP decidePath-Int x {y} p q)
    
  τ₀Int-is-Int : τ₀ Int ≃ Int
  τ₀Int-is-Int = Trunc-reflective (S (S -2)) HSet-Int


  -- relating Int/Pos to other kinds of numbers

  -- coercions
  
  tlp : Positive -> TLevel
  tlp One = tl 1
  tlp (S n) = S (tlp n)

  pos2nat : Positive -> Nat
  pos2nat One = S Z
  pos2nat (S n) = S (pos2nat n)

  _+1np : Nat → Positive
  Z +1np = One
  (S n) +1np = S (n +1np)

  _-1pn : Positive → Nat
  One -1pn = Z
  (S n) -1pn = pos2nat n

  _+pn_ : Positive → Nat → Positive
  One +pn k = k +1np
  S n +pn k = S (n +pn k)

  -2ptl : Positive -> TLevel
  -2ptl One = (S -2)
  -2ptl (S One) = (S (S -2))
  -2ptl (S (S n)) = tl (pos2nat n)

  2*_-2 : Positive -> TLevel
  2* n -2 = plus2 (-2ptl n) (-2ptl n)

  -- properties
  -- ENH: organize/systemetize

  abstract
    +pn-rh-Z : ∀ n -> n +pn Z ≃ n
    +pn-rh-Z One = id
    +pn-rh-Z (S n) = ap S (+pn-rh-Z n)
  
    +pn-rh-S : ∀ n k -> n +pn (S k) ≃ S (n +pn k)
    +pn-rh-S One k = id
    +pn-rh-S (S n) k = ap S (+pn-rh-S n k)
  
    tlp+1 : (k : Nat) → tlp (k +1np) ≃ S (tl k)
    tlp+1 Z = id
    tlp+1 (S k) = ap S (tlp+1 k)
  
    pos2nat-is-S : ∀ n → (pos2nat n) ≃ S (n -1pn)
    pos2nat-is-S One = id
    pos2nat-is-S (S n) = id
  
    n-1<n : ∀ n → tl (n -1pn) <tl tl (pos2nat n)
    n-1<n n = transport (λ x → tl (n -1pn) <tl tl x) (! (pos2nat-is-S n)) ltS
  
    pos2nat-+1np : ∀ n' -> (pos2nat n' +1np) ≃ S n'
    pos2nat-+1np One = id
    pos2nat-+1np (S n') = ap S (pos2nat-+1np n')
  
    pos2nat-of-+1np : ∀ n' -> (pos2nat (n' +1np)) ≃ S n'
    pos2nat-of-+1np Z = id
    pos2nat-of-+1np (S y) = ap S (pos2nat-of-+1np y)
  
    +1-1-cancel : ∀ n → (n +1np) -1pn ≃ n
    +1-1-cancel Z = id
    +1-1-cancel (S y) = pos2nat-of-+1np y
  
    -2<pos-2 : ∀ n → -2 <tl -2ptl n
    -2<pos-2 One = ltS
    -2<pos-2 (S One) = ltSR ltS
    -2<pos-2 (S (S n')) = -2<nat (pos2nat n')
  
    pos-not-<=-2 : (p : Positive) → tlp p <=tl -2 -> Void
    pos-not-<=-2 One (Inl ())
    pos-not-<=-2 One (Inr ())
    pos-not-<=-2 (S n) (Inl y) = pos-not-<=-2 n (Inl (lt-unS-left y))
    pos-not-<=-2 (S n) (Inr ())
  
    pos-not-<=-1 : (p : Positive) → tlp p <=tl (S -2) -> Void
    pos-not-<=-1 One (Inl (ltSR ()))
    pos-not-<=-1 One (Inr ())
    pos-not-<=-1 (S p) lte = pos-not-<=-2 p (<=-unS lte)
  
    pos-not-<=0 : (p : Positive) → tlp p <=tl (S (S -2)) -> Void
    pos-not-<=0 One (Inl (ltSR (ltSR ())))
    pos-not-<=0 One (Inr ())
    pos-not-<=0 (S n) lt = pos-not-<=-1 n (<=-unS lt)

    {-# NO_TERMINATION_CHECK #-}
    -- FIXME: doesn't work in 2.4.1 without-K 
    1<=pos : (p : Positive) → tl 1 <=tl (tlp p)
    1<=pos One = Inr id
    1<=pos (S n) with 1<=pos n
    ... | Inl lt = Inl (ltSR lt)
    ... | Inr eq = transport (λ x → tl 1 <=tl S x) eq (Inl ltS)
  
    >pos->1 : ∀ k n -> tlp k <tl tlp n -> tl 1 <tl tlp n 
    >pos->1 k' One lt' = Sums.abort ( pos-not-<=0 k' (lt-unS-right lt'))
    >pos->1 One (S n') lt' = lt'
    >pos->1 (S n') (S n0) lt'' = ltSR (>pos->1 n' n0 (lt-unS lt''))
  
    -2ptl-S-1pn : ∀ n → (-2ptl (S n)) ≃ (tl (n -1pn))
    -2ptl-S-1pn One = id
    -2ptl-S-1pn (S n) = id
  
    -2ptl-S : ∀ n' →  -2ptl (S n') ≃ (S (-2ptl n'))
    -2ptl-S One = id
    -2ptl-S (S n) = ap S (! (-2ptl-S-1pn n)) ∘ ap tl (pos2nat-is-S n)
  
    pos-1< : ∀ n → tl (n -1pn) <tl tl (pos2nat n)
    pos-1< One = ltS
    pos-1< (S n) = ltS
  
    n-1<=2n-2 : ∀ n → (tl (n -1pn)) <=tl 2* n -2
    n-1<=2n-2 One = Inr id
    n-1<=2n-2 (S One) = Inl ltS
    n-1<=2n-2 (S (S n')) = <=trans (<=SCong (n-1<=2n-2 (S n'))) 
                                   (<=trans (Inr (ap (λ x → plus2 x (-2ptl (S n'))) (! (-2ptl-S (S n')))))
                                             (Inl (plus2-monotone-2 (tl (pos2nat n')) _ _ (transport (λ x → x <tl tl (pos2nat n')) (! (-2ptl-S-1pn n')) (pos-1< n')))))
  
    tl-pos2nat-tlp : ∀ n → tl (pos2nat n) ≃ (tlp n)
    tl-pos2nat-tlp One = id
    tl-pos2nat-tlp (S n) = ap S (tl-pos2nat-tlp n)
  
    lt-1pn-right : ∀ k n → k <tl tlp n → k <=tl (tl (n -1pn))
    lt-1pn-right k One lt = lt-unS-right lt
    lt-1pn-right k (S n) lt = transport (λ x → k <=tl x) (! (tl-pos2nat-tlp n)) (lt-unS-right lt)
  
    2*S-2 : ∀ n → S (2* n -2) <tl 2* (S n) -2
    2*S-2 One = ltS
    2*S-2 (S n) = transport (λ x → x <tl plus2 (tl (pos2nat n)) (tl (pos2nat n))) 
                            (ap (λ x → plus2 x (-2ptl (S n))) (-2ptl-S (S n)))
                            (plus2-monotone-2 (tl (pos2nat n)) (-2ptl (S n)) (tl (pos2nat n)) (transport (λ x → x <tl tl (pos2nat n)) (! (-2ptl-S-1pn n)) (n-1<n n)))
  
    {-# NO_TERMINATION_CHECK #-}
    -- FIXME: doesn't work in 2.4.1 without-K 
    n<=2*n-2 : ∀ n → tl 1 <tl tlp n → tlp n <=tl 2* n -2
    n<=2*n-2 One (ltSR (ltSR y)) = Inl (ltSR y)
    n<=2*n-2 (S n) lt with (lt-unS-right lt) 
    ... | Inl lt' = <=trans (<=SCong (n<=2*n-2 n lt')) (Inl (2*S-2 n))
    ... | Inr eq  = transport (λ x → S x <=tl plus2 (-2ptl (S n)) (-2ptl (S n))) eq
                      (arith n (! eq)) where
      arith : ∀ n -> tlp n ≃ (tl 1) → (tl 2) <=tl 2* (S n) -2
      arith One eq' = Inr id
      arith (S n) eq' with pos-not-<=0 n (<=-unS (Inr eq'))
      ... | ()
  
    min-1nat : (m : Nat) → mintl (S -2) (tl m) ≃ (S -2)
    min-1nat Z = id
    min-1nat (S y) = id
  
    min0nat : (m : Nat) → mintl (tl 0) (tl m) ≃ (tl 0)
    min0nat Z = id
    min0nat (S y) = ap S (min-1nat y)

    -- need that n>1 when they're equal
    k<=n->k<=2n-2 : ∀ k n → Either (tlp k <tl tlp n) ((tlp k ≃ tlp n) × (tl 1 <tl tlp n)) → tlp k <=tl 2* n -2
    k<=n->k<=2n-2 k n (Inl lt)        = <=trans (Inl lt) (n<=2*n-2 n (>pos->1 k n lt))  
    k<=n->k<=2n-2 k n (Inr (eq , lt)) = <=trans (Inr eq) (n<=2*n-2 n lt)

  {-# NO_TERMINATION_CHECK #-}
  -- FIXME: doesn't work in 2.4.1 without-K 
  <=-to-+ : ∀ {n m} -> tlp n <=tl tlp m -> Σ \ k -> tlp (n +pn k) ≃ tlp m
  <=-to-+ {n}{m} (Inr p) = 0 , p ∘ ap tlp (+pn-rh-Z n)
  <=-to-+ {One} {One} (Inl (ltSR (ltSR (ltSR ()))))
  <=-to-+ {S n} {One} (Inl lt) with pos-not-<=0 n (Inl (lt-unS lt))
  ... | () 
  <=-to-+ {n} {S n'} (Inl lt) with lt-unS-right lt
  ... | Inr eq = S Z , (ap S eq) ∘ ap (S o tlp) (+pn-rh-Z n) ∘ ap tlp (+pn-rh-S n Z)
  ... | Inl lt' with <=-to-+ {n}{n'} (Inl lt') 
  ...              | (n'' , eq''') = S n'' , ap S eq''' ∘ ap tlp (+pn-rh-S n n'')

