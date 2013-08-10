{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude

module programming.Semigroup-talk where

  cast :  {B : Type} (E : B → Type) 
            {b1 b2 : B} → Path b1 b2 → (E b1 → E b2)
  cast = transport 

  cast-is-bijection :  {B : Type} (E : B → Type) {b1 b2 : B} 
                 → (α : Path b1 b2) → IsEquiv {(E b1)} {(E b2)} (cast E α)
  cast-is-bijection E α = transport-isequiv E α

  Bijection : Type -> Type -> Type
  Bijection = Equiv 

  is-bijection : {A B : Type}
     {f : A → B}
     (g : B → A)
     (α : (x : A) → Path (g (f x)) x)
     (β : (y : B) → Path (f (g y)) y)
     → IsEquiv f
  is-bijection {f = f} g α β = snd (improve (hequiv f g α β))

  bijection : {A B : Type}
     (f : A → B)
     (g : B → A)
     (α : (x : A) → Path (g (f x)) x)
     (β : (y : B) → Path (f (g y)) y)
     → Equiv A B
  bijection f g α β = (improve (hequiv f g α β))

  bijection' : {A B : Type}
     (f : A → B)
     (g : B → A)
     (α : (x : A) → Path (g (f x)) x)
     (β : (y : B) → Path (f (g y)) y)
     (γ : _)
     → Equiv A B
  bijection' = equiv

  Semigroup : Type → Type
  Semigroup A = Σ \ (_⊙_ : A → A → A) → 
                    (x y z : A) → x ⊙ (y ⊙ z) ≃ (x ⊙ y) ⊙ z

  module ByHand where

    convert-Semigroup : ∀ {A B} → Bijection A B → Semigroup A → Semigroup B
    convert-Semigroup {A}{B}(f , isequiv g α β γ) (_⊙_ , assoc) = (_⊙'_ , assoc') where
      _⊙'_ : B → B → B
      y1 ⊙' y2 = f (g y1 ⊙ g y2) 
  
      assoc' : ∀ y1 y2 y3 -> y1 ⊙' (y2 ⊙' y3) ≃ (y1 ⊙' y2) ⊙' y3
      assoc' y1 y2 y3 = y1 ⊙' (y2 ⊙' y3)               ≃〈 id 〉 
                        f (g y1 ⊙ g (f (g y2 ⊙ g y3))) ≃〈 ap (λ z → f (g y1 ⊙ z)) (α (g y2 ⊙ g y3)) 〉 
                        f (g y1 ⊙ (g y2 ⊙ g y3))       ≃〈 ap f (assoc (g y1) (g y2) (g y3)) 〉 
                        f ((g y1 ⊙ g y2) ⊙ g y3)       ≃〈 ap (λ z → f (z ⊙ g y3)) (! (α (g y1 ⊙ g y2))) 〉 
                        f (g (f (g y1 ⊙ g y2)) ⊙ g y3) ≃〈 id 〉 
                        (y1 ⊙' y2) ⊙' y3 ∎
  
    convert-Semigroup-bijection : ∀ {A B} → NType (tl 0) A → NType (tl 0) B 
                                → Bijection A B 
                                → Bijection (Semigroup A) (Semigroup B)
    convert-Semigroup-bijection nA nB (f , isequiv g α β γ) = 
      bijection (convert-Semigroup (bijection' f g α β γ))
                (convert-Semigroup (!equiv (bijection' f g α β γ)))
                (λ {(_⊙_ , assoc) → pair≃ (λ≃ (λ y1 → λ≃ (λ y2 → 
                                              ap2 _⊙_ (α y1) (α y2) ∘ α (g (f y1) ⊙ g (f y2))))) 
                                          (λ≃ (λ x → λ≃ (λ y → λ≃ (λ z → HSet-UIP nA _ _ _ _))))})
                (λ {(_⊙_ , assoc) → pair≃ (λ≃ (λ y1 → λ≃ (λ y2 → 
                                              ap2 _⊙_ (β y1) (β y2) ∘ β (f (g y1) ⊙ f (g y2))))) 
                                          (λ≃ (λ x → λ≃ (λ y → λ≃ (λ z → HSet-UIP nB _ _ _ _))))})


  module HoTT where

    convert-Semigroup-bijection : ∀ {A B} 
                                → Bijection A B
                                → Bijection (Semigroup A) (Semigroup B)
    convert-Semigroup-bijection b = (cast Semigroup (ua b) ,
                                     cast-is-bijection Semigroup (ua b))


