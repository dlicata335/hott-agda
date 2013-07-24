
{-# OPTIONS --without-K --type-in-type #-}

open import lib.Prelude

module JGross (A : Type) where

  paths-sym : Path{A} ≃ BackPath{A}
  paths-sym = λ≃ (λ x → λ≃ (λ y → flip≃{A}{x}{y}))

  lemma : transport (\ (D : A → A → Type) → (x y z : A) → D y z → D x y → D x z) paths-sym (λ _ _ _ q p → q ∘ p)
          ≃ (\ x y z p q → q ∘ p)
  lemma = transport (λ (D : A → A → Type) → (x y z : A) → D y z → D x y → D x z) paths-sym (λ _ _ _ q p → q ∘ p) ≃〈 reduce-transport _ _ paths-sym _ 〉 
          (λ x y z p q → coe (ap≃ (ap≃ paths-sym)) (coe (! (ap≃ (ap≃ paths-sym))) p ∘ coe (! (ap≃ (ap≃ paths-sym))) q)) ≃〈 λ≃ (λ x → λ≃ (λ y → λ≃ (λ z → λ≃ (λ p → λ≃ (λ q → ap2 (λ f x₁ → f x₁) reduce-coe (ap2 (λ f g → f p ∘ g q) reduce-coe! reduce-coe!)))))) 〉 
          (λ x y z p q → ! (! p ∘ ! q)) ≃〈 λ≃ (λ x → λ≃ (λ y → λ≃ (λ z → λ≃ (λ p → λ≃ (λ q → coh p q))))) 〉 
          (λ x y z z₁ z₂ → z₂ ∘ z₁) ∎  where

     reduce-transport : (F G : A → A → Type) (α : F ≃ G) (f : (x x₁ x₂ : A) (x₃ : F x₁ x₂) (x₄ : F x x₁) → F x x₂)
                      → (transport (\ (D : A → A → Type) → (x y z : A) → D y z → D x y → D x z) α f) ≃
                        (λ x y z p q → coe (ap≃ (ap≃ α {x}) {z}) (f x y z (coe (! (ap≃ (ap≃ α {y}) {z})) p) (coe (! (ap≃ (ap≃ α {x}) {y})) q)))
     reduce-transport F .F id x = id

     reduce-paths-sym : {x y : A} → (ap≃ (ap≃ paths-sym{x}) {y}) ≃ flip≃{A}{x}{y}
     reduce-paths-sym {x}{y} = (ap≃ (ap≃ paths-sym {x}) {y}) ≃〈 ap (λ (z : Path x ≃ BackPath x) → (ap≃ z {y})) (Π≃β {_} {_} {Path} {BackPath} (λ x₁ → λ≃ (λ y₁ → flip≃ {A} {x₁} {y₁})) {x}) 〉 
                               (ap≃ (λ≃ (λ y → flip≃{_}{x}{y})) {y}) ≃〈 (Π≃β (λ y₁ → flip≃ {A} {x} {y₁})) 〉 
                               (flip≃{_}{x}{y}) ∎

     reduce-coe : {x y : A} → coe (ap≃ (ap≃ paths-sym{x}) {y}) ≃ !
     reduce-coe = type≃β (improve (hequiv ! ! !-invol !-invol)) ∘ ap coe reduce-paths-sym

     reduce-coe! : {x y : A} → coe (! (ap≃ (ap≃ paths-sym{x}) {y})) ≃ !
     reduce-coe! = type≃β! (improve (hequiv ! ! !-invol !-invol)) ∘ ap (\ z -> coe (! z)) reduce-paths-sym

     coh : {x y z : A} (p : x ≃ y) (q : y ≃ z) → ! (! p ∘ ! q) ≃ q ∘ p
     coh id id = id
