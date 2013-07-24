{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude

module programming.Semigroup where

  Semigroup : Type → Type
  Semigroup A = Σ \ (_⊙_ : A → A → A) → 
                  (x y z : A) → x ⊙ (y ⊙ z) ≃ (x ⊙ y) ⊙ z

  transport-Semigroup-eqv  : ∀ {A B} -> Equiv A B → Semigroup A → Semigroup B
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

  -- proof that it's an equivalence (hsets only; couldn't stand to do the calculation otherwise)
  transport-Semigroup-eqv-eqv : ∀ {A B} -> NType (tl 0) A → NType (tl 0) B 
                              → Equiv A B → Equiv (Semigroup A) (Semigroup B)
  transport-Semigroup-eqv-eqv nA nB (f , isequiv g α β γ) = 
    improve (hequiv (transport-Semigroup-eqv (equiv f g α β γ))
                    (transport-Semigroup-eqv (!equiv (equiv f g α β γ)))
                    (λ {(_⊙_ , assoc) → pair≃ (λ≃ (λ y1 → λ≃ (λ y2 → 
                                                   ap2 _⊙_ (α y1) (α y2) ∘ α (g (f y1) ⊙ g (f y2))))) 
                                               (λ≃ (λ x → λ≃ (λ y → λ≃ (λ z → HSet-UIP nA _ _ _ _))))})
                    (λ {(_⊙_ , assoc) → pair≃ (λ≃ (λ y1 → λ≃ (λ y2 → 
                                                   ap2 _⊙_ (β y1) (β y2) ∘ β (f (g y1) ⊙ f (g y2))))) 
                                               (λ≃ (λ x → λ≃ (λ y → λ≃ (λ z → HSet-UIP nB _ _ _ _))))}))

  -- proof that that's what transport does

  transport-Semigroup-eqv-id : ∀ {A} -> transport-Semigroup-eqv{A}{A} id-equiv ≃ (\ x -> x)
  transport-Semigroup-eqv-id {A} = 
    λ≃ λ {(_⊙_ , assoc) → pair≃ {_}{_}{(transport-Semigroup-eqv id-equiv (_⊙_ , assoc))}{_⊙_ , assoc} 
                                id
                                (λ≃ (λ y1 → λ≃ (λ y2 → λ≃ (λ y3 → ap-id (assoc y1 y2 y3) ∘ ∘-unit-l (ap (λ x → x) (assoc y1 y2 y3))))))}

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