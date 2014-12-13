{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude hiding (id ; _∘_ ; !) 

module programming.Patch where

  _∘p_ = lib.Prelude._∘_
  !p = lib.Prelude.!
  idp = \{A}{x} → lib.Prelude.id{A}{x}

  data Vec (A : Set) : Nat → Set where
    []   : Vec A 0
    _::_ : {n : Nat} → A → Vec A n → Vec A (S n)

  module R (n : Nat) where

    data Patch : Set where
      id     : Patch
      _∘_    : Patch → Patch → Patch
      !      : Patch → Patch
      _↔_at_ : Char → Char → Fin n → Patch

    infixr 8 _∘_
      
    swapchar : Char → Char → Char → Char
    swapchar a b c with Char.equals a c
    ... | Inl _ = b 
    ... | Inr _ with Char.equals b c
    ...            | Inl _ = a 
    ...            | Inr _ = c

    swapchar-inv : (a b c : Char) → swapchar a b (swapchar a b c) == c
    swapchar-inv a b c with Char.equals a c 
    ... | Inl a=c with Char.equals a b 
    ...            | Inl a=b = a=c ∘p !p a=b
    ...            | Inr p with Char.equals b b 
    ...                       | Inl _ = a=c
    ...                       | Inr neq = Sums.abort (neq idp)
    swapchar-inv a b c | Inr a!=c with Char.equals b c
    ...                              | Inl b=c with Char.equals a a 
    ...                                           | Inl _ = b=c
    ...                                           | Inr neq = Sums.abort (neq idp)
    swapchar-inv a b c | Inr a!=c    | Inr b!=c with Char.equals a c 
    ... | Inl eq = Sums.abort (a!=c eq) 
    ... | Inr _ with Char.equals b c
    ...            | Inl eq = Sums.abort (b!=c eq) 
    ...            | Inr neq = idp 

    swapchar≃ : (a b : Char) → Equiv Char Char
    swapchar≃ a b = improve (hequiv (swapchar a b) (swapchar a b) (swapchar-inv a b) (swapchar-inv a b))

    apply-at : {A : Set} {n : Nat} (f : A → A) → (i : Fin n) → Vec A n → Vec A n
    apply-at f () [] 
    apply-at f Z (x :: v) = f x :: v
    apply-at f (S i) (x :: v) = x :: apply-at f i v

    apply-at-inv : {A : Set} {n : Nat} (f : Equiv A A) (i : Fin n) (v : Vec A n)
                 → (apply-at (fst f) i (apply-at (IsEquiv.g (snd f)) i v)) == v
    apply-at-inv f () []
    apply-at-inv f Z (x :: v) = ap (λ x₁ → x₁ :: v) (IsEquiv.β (snd f) x)
    apply-at-inv f (S i) (x :: v) = ap (λ xs → x :: xs) (apply-at-inv f i v)

    apply-at-equiv : {A : Set} {n : Nat} (f : Equiv A A) (i : Fin n) → Equiv (Vec A n) (Vec A n)
    apply-at-equiv f i = improve (hequiv (apply-at (fst f) i) (apply-at (IsEquiv.g (snd f)) i) 
                                          (apply-at-inv (!equiv f) i) (apply-at-inv f i))

    -- swapat a b i v  permutes a and b at position i in v
    swapat : Char → Char → Fin n → Vec Char n → Vec Char n
    swapat a b i = apply-at (swapchar a b) i

    interp : Patch → (Vec Char n → Vec Char n) × 
                     (Vec Char n → Vec Char n)
    interp id = (λ x → x) , (λ x → x)
    interp (q ∘ p) = fst (interp q) o fst (interp p) ,
                     snd (interp p) o snd (interp q)
    interp (! p) = snd (interp p) , fst (interp p)
    interp (a ↔ b at i) = swapat a b i , swapat a b i

    mutual
      interp-lr : (p : Patch) (v : Vec Char n) → snd (interp p) (fst (interp p) v) == v
      interp-lr id v = idp
      interp-lr (q ∘ p) v = interp-lr p v ∘p
                              ap≃
                              (ap (λ x → snd (interp p) o x o fst (interp p))
                               (λ≃ (λ x → interp-lr q x)))
      interp-lr (! p) v = interp-rl p v
      interp-lr (a ↔ b at i) v = IsEquiv.α (snd (apply-at-equiv (swapchar≃ a b) i)) v

      interp-rl : (p : Patch) (v : Vec Char n) → fst (interp p) (snd (interp p) v) == v
      interp-rl id v = idp
      interp-rl (q ∘ p) v = interp-rl q v ∘p
                              ap≃
                              (ap (λ x → fst (interp q) o x o snd (interp q))
                               (λ≃ (λ x → interp-rl p x)))
      interp-rl (! p) v = interp-lr p v
      interp-rl (a ↔ b at i) v = IsEquiv.β (snd (apply-at-equiv (swapchar≃ a b) i)) v

    module Infer where
      
      Spec = Vec (Maybe Char) n 

      editc : Char → Char → Char → Char
      editc a b c with Char.equals a c 
      ...            | Inl _ = b
      ...            | Inr _ = c

      postulate {- HoTT Axiom -}
        R    : Type
        mkr  : Spec → R
        edit : (c d : Char) (i : Fin n) {φ : Spec} →
             (mkr (apply-at (\ _ -> Some d) i φ)) == (mkr (apply-at (\ _ -> Some d) i φ))

  module Test where
    module TestR = R 3
    open TestR public
  
    example : Vec Char 3
    example = 'a' :: 'u' :: 's' :: []
 
    patch = ('a' ↔ 'b' at Z) ∘ ('x' ↔ 'y' at (S Z)) ∘ ('s' ↔ 'b' at (S (S Z)))

{-
    open Infer
    test : Path (mkr (apply-at (λ _ → Some 'd') (S Z) (None :: None :: None :: [])))
                (mkr (apply-at (λ _ → Some 'b') Z _))
    test = edit 'a' 'b' Z ∘p edit 'c' 'd' (S Z)
-}

  open Test

