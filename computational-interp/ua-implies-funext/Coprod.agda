
{-# OPTIONS --type-in-type --without-K #-}

open import NoFunextPrelude
open import Funext using (Paths ; contract-Paths)

module Coprod where

  data Void : Set where

  data Either (a : Set) (b : Set) : Set where
      Inl : a -> Either a b
      Inr : b -> Either a b

  module Coprod (A : Type) (B : Type) where

    eqv : Paths (Either A B) == Either (Paths A) (Paths B)
    eqv = ap2 Either (! (contract-Paths {A})) (! (contract-Paths {B}))  ∘ (contract-Paths {Either A B})

    C : (x y : Either A B) → Type
    C (Inl a) (Inl a') = a == a'
    C (Inr b) (Inr b') = b == b'
    C _ _ = Void

    step : (a : A) → coe (! eqv) (Inl ((a , a) , id)) == ((Inl a , Inl a) , id)
    step = {!!}

    e' : (p : Either A B × Either A B) → Equiv (Σ \ (q : Paths (Either A B)) → fst q == p) (C (fst p) (snd p))
    e' p = improve (hequiv l {!!} {!!} {!!}) where
      l : (Σ \ (q : Paths (Either A B)) → fst q == p) → _
      l = {!!}

    e : (p : Either A B × Either A B) → Equiv (Σ \ (q : Either (Paths A) (Paths B)) → fst (coe (! eqv) q) == p) (C (fst p) (snd p)) 
    e p = improve (hequiv l (r p) {!!} {!!}) where
      l : Σ (λ q → fst (coe (! eqv) q) == p) -> _
      l (Inl ((x , .x) , id) , eq) = path-induction (λ p₁ eq₁ → C (fst p₁) (snd p₁)) (transport (λ x₁ → C (fst (fst x₁)) (snd (fst x₁))) (! (step x)) id) eq
      l (Inr ((y , .y) , id) , eq) = {!!}

      r : (p : Either A B × Either A B) → (C (fst p) (snd p)) -> (Σ \ (q : Either (Paths A) (Paths B)) → fst (coe (! eqv) q) == p)
      r (Inl x , Inl y) c = (Inl ((x , y) , c)) , {!!}
      r (Inl x , Inr y) ()
      r (Inr x , Inl y) c = {!!}
      r (Inr x , Inr y) c = {!!}

    -- seems like you could do it, but would the fact that eqv is an equivalence help at all?

{-
    another attempt

    C : (a a' : A) → Either (Paths A) (Paths B) → Type
    C a a' (Inl ((a1 , a1'), p)) = (a == a1) × (a' == a1')
    C a a' (Inr _) = Void 

    coprod2 : (a a' : A) (p : Paths (Either A B)) → C a a' (coe eqv p) == (fst p == (Inl a , Inl a'))
    coprod2 a a' ((Inl x , .(Inl x)) , id) = {!!}
    coprod2 a a' ((Inr x , .(Inr x)) , id) = {!!}

    coprod3 : (a a' : A) (p : Either (Paths A) (Paths B)) → C a a' p == (fst (coe (! eqv) p) == (Inl a , Inl a'))
    coprod3 a a' (Inl ((x , .x) , id)) = (a == x) × (a' == x) ≃〈 {!!} 〉
                                         Path {(Either A B × Either A B)} (Inl x , Inl x) (Inl a , Inl a') ≃〈 {!!} 〉 
                                         (fst (coe (! eqv) (Inl ((x , x) , id))) == (Inl a , Inl a') ∎)
    coprod3 a a' (Inr ((x , .x) , id)) = {!!}

    fiberwise-eqv : {A : Type} {B B' : A → Type} → (f : (a : A) → B a → B' a)
                  → IsEquiv {(Σ B)} {(Σ B')} (fiberwise-to-total f) 
                  → (a : A) → B a == B' a
    fiberwise-eqv f (isequiv g α β _) a = ua (improve (hequiv (f a) (λ b' → coe {!!} (snd (g (a , b')))) {!!} {!!}))

    movearg : ∀ {A B} → Equiv (A → Paths B) (Σ (λ (p₁ : (A → B) × (A → B)) → (x : A) → fst p₁ x == snd p₁ x)) 
    movearg = improve (hequiv ((λ f →
                                      ((\ x -> fst (fst (f x))) , (λ x₁ → snd (fst (f x₁)))) ,
                                      (λ x₁ → snd (f x₁))))
                               (λ x x₁ → ((fst (fst x) x₁) , (snd (fst x) x₁)) , (snd x x₁))
                               (λ _ → id) (λ _ → id))

    funext : {A B : Type} (f g : A → B) → (f == g) == ((x : A) → f x == g x)
    funext {A} {B} f g = fiberwise-eqv {A = (A → B) × (A → B)} {B = \ p → fst p == snd p} {B' = \ p → (x : A) → fst p x == snd p x}
                                       (λ {(f , g) → λ p₁ x → ap≃ p₁ {x}})
                                       STS
                                       (f , g) where
        tot : (Paths (A → B)) → Σ (λ (p₁ : (A → B) × (A → B)) → (x : A) → fst p₁ x == snd p₁ x)
        tot = fiberwise-to-total {A = (A → B) × (A → B)} {B = \ p → fst p == snd p} {B' = \ p → (x : A) → fst p x == snd p x} (λ {(f , g) → λ p₁ x → ap≃ p₁ {x}})

        e : Equiv (Paths (A → B)) (Σ (λ (p₁ : (A → B) × (A → B)) → (x : A) → fst p₁ x == snd p₁ x))
        e = movearg ∘equiv coe-equiv eqv

        STS : IsEquiv {Paths (A → B)} {Σ (λ (p₁ : (A → B) × (A → B)) → (x : A) → fst p₁ x == snd p₁ x)} 
                      tot
        STS = transport IsEquiv (fst e ≃〈 {!!} 〉 
                                 fst movearg o coe eqv ≃〈 {!!} 〉 
                                 fst movearg o coe (! (ap (\ y -> A → y) (contract-Paths {B}))) o coe (contract-Paths {A → B}) ≃〈 {!!} 〉 
                                 fst movearg o coe (ap (\ y -> A → y) (! (contract-Paths {B}))) o coe (contract-Paths {A → B}) ≃〈 {!!} 〉 
                                 fst movearg o (\ z -> coe (! (contract-Paths {B})) o z) o coe (contract-Paths {A → B}) ≃〈 {!!} 〉 
                                 ((λ f →
                                      ((\ x -> fst (fst (f x))) , (λ x₁ → snd (fst (f x₁)))) ,
                                      (λ x₁ → snd (f x₁)))) o (\ z -> coe (! (contract-Paths {B})) o z) o coe (contract-Paths {A → B}) ≃〈 {!!} 〉 
                                 (\ p -> fst p , λ x → ap≃ (snd p) {x}) ≃〈 {!!} 〉 
                                 tot ∎)
                                (snd e) 
-}
