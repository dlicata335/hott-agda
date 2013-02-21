{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude

module programming.Semigroup where

  Semigroup : Type → Type
  Semigroup A = Σ \ (_⊙_ : A → A → A) → 
                  (x y z : A) → x ⊙ (y ⊙ z) ≃ (x ⊙ y) ⊙ z

  transport-Semigroup-eqv : ∀ {A B} -> Equiv A B → Semigroup A → Semigroup B
  transport-Semigroup-eqv {A}{B}(f , isequiv g α β γ) (_⊙_ , assoc) = (_⊙'_ , assoc') where
    _⊙'_ : B → B → B
    y1 ⊙' y2 = f (g y1 ⊙ g y2) 

    assoc' : ∀ y1 y2 y3 -> y1 ⊙' (y2 ⊙' y3) ≃ (y1 ⊙' y2) ⊙' y3
    assoc' y1 y2 y3 = y1 ⊙' (y2 ⊙' y3)               ≃〈 id 〉 
                      f (g y1 ⊙ g (f (g y2 ⊙ g y3))) ≃〈 ap (λ z → f (g y1 ⊙ z)) (α (g y2 ⊙ g y3)) 〉 
                      f (g y1 ⊙ (g y2 ⊙ g y3))       ≃〈 ap f (assoc (g y1) (g y2) (g y3)) 〉 
                      f ((g y1 ⊙ g y2) ⊙ g y3)       ≃〈 ap (λ z → f (z ⊙ g y3)) (! (α (g y1 ⊙ g y2))) 〉 
                      f (g (f (g y1 ⊙ g y2)) ⊙ g y3) ≃〈 id 〉 
                      (y1 ⊙' y2) ⊙' y3 ∎

  transport-Semigroup-eqv-id : ∀ {A} -> transport-Semigroup-eqv{A}{A} id-equiv ≃ (\ x -> x)
  transport-Semigroup-eqv-id = 
    λ≃ λ {(_⊙_ , assoc) → pair≃ id 
                                (λ≃ (λ y1 → λ≃ (λ y2 → λ≃ (λ y3 → 
                                 ap-id (assoc y1 y2 y3) ∘ ∘-unit-l (ap (λ x → x) (assoc y1 y2 y3))))))}

  transport-isequiv : ∀ {A : Type} {M N : A} (B : A → Type) (α : M ≃ N) 
                  -> IsEquiv (transport B α)
  transport-isequiv {A}{M} B α = isequiv (transport B (! α)) (λ x → ap≃ (transport-inv-1 B α)) (λ x → ap≃ (transport-inv-2 B α)) 
                                  (coh α) where
                    coh : {N : _} (α : Path M N) 
                        → (x : B M) → Path (ap≃ (transport-inv-2 B α)) (ap (transport B α) (ap≃ (transport-inv-1 B α) {x}))
                    coh id = λ _ → id

  transport-Semigroup : ∀ {A : Type} {M N : A} (B : A → Type) (α : M ≃ N) 
                      → transport (\ x → Semigroup (B x)) α 
                      ≃ transport-Semigroup-eqv (transport B α , transport-isequiv B α)
  transport-Semigroup B id = ! transport-Semigroup-eqv-id


{-
  transport-Semigroup' : ∀ {A : Type} {M N : A} (B : A → Type) (α : M ≃ N) 
                      → transport (\ x → Semigroup (B x)) α 
                      ≃ transport-Semigroup-eqv (transport B α , transport-isequiv B α)
  transport-Semigroup' B α = λ≃ (\ { (_⊙_ , assoc) ->
    transport (\ x → Semigroup (B x)) α (_⊙_ , assoc) ≃〈 transport-Σ α (λ x → B x → B x → B x) (λ _ _⊙_ → (x y z : _) → x ⊙ (y ⊙ z) ≃ (x ⊙ y) ⊙ z) (_⊙_ , assoc)〉 

    (transport (λ x' → B x' → B x' → B x') α _⊙_ ,
     transport
        (λ (a⊙ : Σ (λ a → B a → B a → B a)) → 
           let a = fst a⊙
               _⊙_ = snd a⊙
           in (x y z : B a) → x ⊙ (y ⊙ z) ≃ (x ⊙ y) ⊙ z)
        (pair≃ α id) assoc) ≃〈 pair≃⁻ (λ≃ (λ a → transport-→ B B α (_⊙_ (transport B (! α) a))) ∘ transport-→ B (λ a → B a → B a) α _⊙_)
                                  {!id!} 〉 

    ((λ y1 y2 → transport B α (transport B (! α) y1 ⊙ transport B (! α) y2))
       , {!!}) ≃〈 {!!} 〉 

    transport-Semigroup-eqv (transport B α , transport-isequiv B α) (_⊙_ , assoc) ∎
   })
-}