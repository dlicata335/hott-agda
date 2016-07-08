{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Nat
open import lib.Prods
open import lib.Paths

module lib.Sums where

  data Void : Set where

  data Either (a : Set) (b : Set) : Set where
    Inl : a -> Either a b
    Inr : b -> Either a b

  data Fin : Nat → Set where
    Z : ∀ {n} → Fin (S n) 
    S : ∀ {n} → Fin n → Fin (S n)

  module Sums where
    case : {A B : Type} (C : Either A B → Type) 
             → ((x : A) → C (Inl x))
             → ((y : B) → C (Inr y))
             → (e : Either A B) -> C e
    case C l r (Inl x) = l x
    case C l r (Inr y) = r y

    Either-UMP : ∀ {A B C} → Equiv ((A → C) × (B → C)) (Either A B → C)
    Either-UMP = improve (hequiv (λ fg → case _ (fst fg) (snd fg)) (λ f → (λ x → f (Inl x)) , (λ x → f (Inr x))) (λ _ → id) (λ y → λ≃ (λ { (Inl x) → id ; (Inr y) → id })))

    casest : {A B C : Type} 
             → (A → C)
             → (B → C)
             → (e : Either A B) -> C 
    casest l r (Inl x) = l x
    casest l r (Inr y) = r y

    abort : {A : Type} → Void → A
    abort ()

    Fin-case : (C : Σ Fin → Type)
             → ((n : Nat) → C (S n , Z))
             → ((p : Σ Fin) → C (S (fst p) , S (snd p)))
             → (p : Σ Fin) → C p
    Fin-case C m0 m1 (.(S n) , Z{n}) = m0 n
    Fin-case C m0 m1 (.(S n) , S{n} y) = m1 (n , y)
    
    FinCodes : Σ Fin → Σ Fin → Type
    FinCodes x y = Fin-case (\ _ -> Type) 
                            (λ n → Fin-case (λ _ → Type) (λ m → n == m) (λ _ → Void) y) 
                            (λ x' → Fin-case (λ _ → Type) (λ _ → Void) (λ y' → Id{Σ Fin} x' y') y)
                            x

    FinCodes-id : (x : Σ Fin) → FinCodes x x
    FinCodes-id = Fin-case (\x -> FinCodes x x) (λ n → id) (λ _ → id) 

    Fin-encode : { p q : Σ Fin } → p == q → FinCodes p q
    Fin-encode {p} {q} α = transport (λ x → FinCodes p x) α (FinCodes-id p)

    transport-Fin-S : ∀ {m n } (α : m == n) {y : Fin m} → transport (\ n -> Fin (S n)) α (S y) == S (transport Fin α y)
    transport-Fin-S id = id

    Fin-decode : { p q : Σ Fin } → FinCodes p q → p == q
    Fin-decode {p} {q} c = Fin-case (λ p₁ → (q₁ : Σ Fin) → FinCodes p₁ q₁ → p₁ == q₁) 
                                    (λ n → Fin-case _ 
                                                    (λ m → λ p₁ → ap (λ y → S y , Z {y}) p₁)
                                                    (λ _ x → abort x))
                                    (λ p₁ → Fin-case _ (λ _ y → abort y)
                                                       (λ q₁ → λ α → pair≃ (ap S (fst≃ α)) 
                                                         (((apd S (snd≃ α) ∘ ! (ap≃ (transport-constant (snd≃ α)))) ∘ transport-Fin-S (fst≃ α)) ∘ ! (ap≃ (transport-ap-assoc' Fin S (fst≃ α)))))) p q
                                    c

    Fin-encdec-id : (p : Σ Fin) -> Fin-decode {p}{p} (FinCodes-id p) == id 
    Fin-encdec-id = Fin-case _ (λ _ → id) (λ _ → id)

    Fin-encdec : { p q : Σ Fin } → (α : p == q) → Fin-decode (Fin-encode α) == α
    Fin-encdec {p} {q} α = path-induction (λ q₁ α₁ → Fin-decode (Fin-encode α₁) == α₁) (Fin-encdec-id p) α

    injectivity' : (u : Nat) (s : Fin u) (t : Fin u) 
                 → (C : Path {Σ Fin} (S u , S s) (S u , S t) → Type)
                 → ((p : Path {Σ Fin} (u , s) (u , t)) → C (Fin-decode p))
                   -- → ((p : s == t) → C (Fin-decode (pair≃ id p)))
                 → (e : S s == S t) → C (pair≃ id e)
    injectivity' u s t C b e = transport C (Fin-encdec (pair≃ id e)) (b (Fin-encode {S u , S s} {S u , S t} (pair≃ id e)))

  
  
