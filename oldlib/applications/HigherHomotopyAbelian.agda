{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open Paths

module applications.HigherHomotopyAbelian (A : Set) (base : A) where

  Ω1 : Set
  Ω1 = base ≃ base

  Ω2 : Set
  Ω2 = Id{Ω1} Refl Refl 

  _⊙_ : Ω2 → Ω2 → Ω2 
  a ⊙ b =  resp∘ a b

  ⊙-unit-l : (p : Ω2) → (Refl ⊙ p) ≃ p
  ⊙-unit-l p = ∘-unit-l p ∘ resp∘-unit-l p -- because we know the base is Refl, the adjustment cancels

  ⊙-unit-r : (a : Ω2) → (a ⊙ Refl) ≃ a
  ⊙-unit-r a = resp∘-unit-r a 

  interchange : (a b c d : _) → ((a ∘ b) ⊙ (c ∘ d)) ≃ ((a ⊙ c)  ∘ (b ⊙ d))
  interchange a b c d = ichange-type d c b a

  same : (a b : Ω2) → (a ∘ b) ≃ (a ⊙ b)
  same a b = (( a         ∘ b)          ≃〈 resp (λ x → x ∘ b) (sym (⊙-unit-r a)) 〉 
              ((a ⊙ Refl) ∘ b)          ≃〈 resp (λ x → (a ⊙ Refl) ∘ x) (sym (⊙-unit-l b)) 〉 
              ((a ⊙ Refl) ∘ (Refl ⊙ b)) ≃〈 sym (interchange a Refl Refl b) 〉 
              ((a ∘ Refl) ⊙ (Refl ∘ b))  ≃〈 resp (λ x → x ⊙ (Refl ∘ b)) (trans-unit-l a) 〉 
              (a ⊙ (Refl ∘ b))           ≃〈 resp (λ x → a ⊙ x) (∘-unit-l b) 〉 
              (a ⊙ b) 
              ∎)

  abelian : (a b : Ω2) → (a ∘ b) ≃ (b ∘ a)
  abelian a b = (a ∘ b) ≃〈 resp (λ x → x ∘ b) (sym (⊙-unit-l a)) 〉 
                   ((Refl ⊙ a) ∘ b)          ≃〈 resp (λ x → (Refl ⊙ a) ∘ x) (sym (⊙-unit-r b)) 〉 
                   ((Refl ⊙ a) ∘ (b ⊙ Refl)) ≃〈 ! (interchange Refl b a Refl) 〉 
                   ((Refl ∘ b) ⊙ (a ∘ Refl)) ≃〈 resp (λ x → x ⊙ (a ∘ Refl)) (∘-unit-l b) 〉 
                   (b         ⊙ (a ∘ Refl)) ≃〈 resp (λ x → b ⊙ x) (∘-unit-r a) 〉 
                   (b ⊙ a)                   ≃〈 sym (same b a) 〉 
                   (b ∘ a) 
                   ∎
  
  {-
      -- for reference, this is the minimal generalization of the IH that goes through
      -- for proving the interchange law
      ichange : (p q : Ω1) 
               → (a : Id p q) (r : Ω1) (b : Id q r) (p' q' : Ω1) 
                 (c : Id p' q') (r' : Ω1) (d : Id q' r') 
               → Id (resptrans (trans a b) (trans c d)) (trans (resptrans a c) (resptrans b d))
      ichange p q a = jay
                        (λ p' q' a' →
                           (r : Ω1) (b : Id q' r) (p0 q0 : Ω1) (c : Id p0 q0) (r' : Ω1)
                           (d : Id q0 r') →
                           Id (resptrans (trans a' b) (trans c d))
                           (trans (resptrans a' c) (resptrans b d)))
                        a
                        (λ pq r b →
                           jay
                           (λ pq' r' b' →
                              (p' q' : Ω1) (c : Id p' q') (r0 : Ω1) (d : Id q' r0) →
                              Id (resptrans (trans Refl b') (trans c d))
                              (trans (resptrans Refl c) (resptrans b' d)))
                           b
                           (λ pqr p' q' c →
                              jay
                              (λ p0 q0 c' →
                                 (r' : Ω1) (d : Id q0 r') →
                                 Id (resptrans Refl (trans c' d))
                                 (trans (resptrans Refl c') (resptrans Refl d)))
                              c
                              (λ p'q' r' d →
                                 jay
                                 (λ p'q0 r0 d' →
                                    Id (resptrans Refl (trans Refl d'))
                                    (trans Refl (resptrans Refl d')))
                                 d (λ _ → Refl))))
  -}
      
      -- ENH: can you relax the restriction that the base point is identity?
      -- abelian' : {loop : Id base base} {a b : Id loop loop} → Id (trans a b) (trans b a)

  -- shorter proof by Favonia
  module BifunctorLemma where

    bifunctor-lemma : ∀ {A B C : Set} 
                        (f : A -> B -> C)
                        {a a' : A} {b b' : B}
                        (α : a ≃ a') (β : b ≃ b')
                     -> (resp (\ x -> f a' x) β ∘ resp (\ x -> f x b) α)
                      ≃ (resp (\ x -> f x b') α ∘ resp (\ x -> f a x) β)
    bifunctor-lemma f Refl Refl = Refl 

    bifunctor-lemma-∘ : (α β : Ω2)
                     -> (resp (\ x -> Refl ∘ x) β ∘ resp (\ x -> x ∘ Refl) α)
                      ≃ (resp (\ x -> x ∘ Refl) α ∘ resp (\ x -> Refl ∘ x) β) 
    bifunctor-lemma-∘ α β = bifunctor-lemma _∘_ {Refl} {Refl} {Refl} {Refl} α β

    commute : (α β : Ω2) -> (α ∘ β) ≃ (β ∘ α)
    commute α β = α ∘ β                                              ≃〈 resp (λ f → f α ∘ β) (! is-id-resp-2) 〉
                  resp (λ x → x ∘ Refl) α ∘ β                        ≃〈 resp (λ f → resp (λ x → x ∘ Refl) α ∘ f β) (! is-id-resp-1) 〉
                  resp (λ x → x ∘ Refl) α ∘ resp (λ x → Refl ∘ x) β  ≃〈 ! (bifunctor-lemma-∘ α β) 〉 
                  resp (λ x → Refl ∘ x) β ∘ resp (\ x -> x ∘ Refl) α ≃〈 resp (λ f → f β ∘ resp (λ x → x ∘ Refl) α) is-id-resp-1 〉 
                  β ∘ resp (\ x -> x ∘ Refl) α                       ≃〈 resp (λ f → β ∘ f α) is-id-resp-2 〉 
                  β ∘ α ∎ where
      is-id-resp-1 : resp (\ (x : Ω1) -> Refl ∘ x) ≃ (\ (x : Ω2) -> x)
      is-id-resp-1 = λ≃ (\ x → ∘-unit-l x ∘ resp-by-id (\ y → ! (∘-unit-l y)) x) 
  
      is-id-resp-2 : resp (\ (x : Ω1) -> x ∘ Refl) ≃ (\ (x : Ω2) -> x)
      is-id-resp-2 = λ≃ resp-id -- cancels definitionally on this side

 