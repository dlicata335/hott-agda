{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open Paths
open S¹

module homotopy.HigherHomotopyAbelian (A : Set) (base : A) where

  Ω1 : Set
  Ω1 = base ≃ base

  Ω2 : Set
  Ω2 = Path{Ω1} id id 

  _⊙_ : Ω2 → Ω2 → Ω2 
  a ⊙ b =  ap∘ a b

  ⊙-unit-l : (p : Ω2) → (id ⊙ p) ≃ p
  ⊙-unit-l p = ∘-unit-l p ∘ ap∘-unit-l p -- because we know the base is id, the adjustment cancels

  ⊙-unit-r : (a : Ω2) → (a ⊙ id) ≃ a
  ⊙-unit-r a = ap∘-unit-r a 

  interchange : (a b c d : _) → ((a ∘ b) ⊙ (c ∘ d)) ≃ ((a ⊙ c)  ∘ (b ⊙ d))
  interchange a b c d = ichange-type d c b a

  same : (a b : Ω2) → (a ∘ b) ≃ (a ⊙ b)
  same a b = (( a         ∘ b)          ≃〈 ap (λ x → x ∘ b) (! (⊙-unit-r a)) 〉 
              ((a ⊙ id) ∘ b)          ≃〈 ap (λ x → (a ⊙ id) ∘ x) (! (⊙-unit-l b)) 〉 
              ((a ⊙ id) ∘ (id ⊙ b)) ≃〈 ! (interchange a id id b) 〉 
              ((a ∘ id) ⊙ (id ∘ b))  ≃〈 ap (λ x → x ⊙ (id ∘ b)) (∘-unit-r a) 〉 
              (a ⊙ (id ∘ b))           ≃〈 ap (λ x → a ⊙ x) (∘-unit-l b) 〉 
              (a ⊙ b) 
              ∎)

  abelian : (a b : Ω2) → (a ∘ b) ≃ (b ∘ a)
  abelian a b = (a ∘ b) ≃〈 ap (λ x → x ∘ b) (! (⊙-unit-l a)) 〉 
                   ((id ⊙ a) ∘ b)          ≃〈 ap (λ x → (id ⊙ a) ∘ x) (! (⊙-unit-r b)) 〉 
                   ((id ⊙ a) ∘ (b ⊙ id)) ≃〈 ! (interchange id b a id) 〉 
                   ((id ∘ b) ⊙ (a ∘ id)) ≃〈 ap (λ x → x ⊙ (a ∘ id)) (∘-unit-l b) 〉 
                   (b         ⊙ (a ∘ id)) ≃〈 ap (λ x → b ⊙ x) (∘-unit-r a) 〉 
                   (b ⊙ a)                   ≃〈 ! (same b a) 〉 
                   (b ∘ a) 
                   ∎
  
  {-
      -- for reference, this is the minimal generalization of the IH that goes through
      -- for proving the interchange law
      ichange : (p q : Ω1) 
               → (a : Path p q) (r : Ω1) (b : Path q r) (p' q' : Ω1) 
                 (c : Path p' q') (r' : Ω1) (d : Path q' r') 
               → Path (aptrans (trans a b) (trans c d)) (trans (aptrans a c) (aptrans b d))
      ichange p q a = jay
                        (λ p' q' a' →
                           (r : Ω1) (b : Path q' r) (p0 q0 : Ω1) (c : Path p0 q0) (r' : Ω1)
                           (d : Path q0 r') →
                           Path (aptrans (trans a' b) (trans c d))
                           (trans (aptrans a' c) (aptrans b d)))
                        a
                        (λ pq r b →
                           jay
                           (λ pq' r' b' →
                              (p' q' : Ω1) (c : Path p' q') (r0 : Ω1) (d : Path q' r0) →
                              Path (aptrans (trans id b') (trans c d))
                              (trans (aptrans id c) (aptrans b' d)))
                           b
                           (λ pqr p' q' c →
                              jay
                              (λ p0 q0 c' →
                                 (r' : Ω1) (d : Path q0 r') →
                                 Path (aptrans id (trans c' d))
                                 (trans (aptrans id c') (aptrans id d)))
                              c
                              (λ p'q' r' d →
                                 jay
                                 (λ p'q0 r0 d' →
                                    Path (aptrans id (trans id d'))
                                    (trans id (aptrans id d')))
                                 d (λ _ → id))))
  -}
      
      -- ENH: can you relax the restriction that the base point is identity?
      -- abelian' : {loop : Path base base} {a b : Path loop loop} → Path (trans a b) (trans b a)

  -- shorter proof by Favonia
  module BifunctorLemma where

    bifunctor-lemma : ∀ {A B C : Set} 
                        (f : A -> B -> C)
                        {a a' : A} {b b' : B}
                        (α : a ≃ a') (β : b ≃ b')
                     -> (ap (\ x -> f a' x) β ∘ ap (\ x -> f x b) α)
                      ≃ (ap (\ x -> f x b') α ∘ ap (\ x -> f a x) β)
    bifunctor-lemma f id id = id 

    bifunctor-lemma-∘ : (α β : Ω2)
                     -> (ap (\ x -> id ∘ x) β ∘ ap (\ x -> x ∘ id) α)
                      ≃ (ap (\ x -> x ∘ id) α ∘ ap (\ x -> id ∘ x) β) 
    bifunctor-lemma-∘ α β = bifunctor-lemma _∘_ {id} {id} {id} {id} α β

    commute : (α β : Ω2) -> (α ∘ β) ≃ (β ∘ α)
    commute α β = α ∘ β                                              ≃〈 ap (λ f → f α ∘ β) (! is-id-ap-2) 〉
                  ap (λ x → x ∘ id) α ∘ β                        ≃〈 ap (λ f → ap (λ x → x ∘ id) α ∘ f β) (! is-id-ap-1) 〉
                  ap (λ x → x ∘ id) α ∘ ap (λ x → id ∘ x) β  ≃〈 ! (bifunctor-lemma-∘ α β) 〉 
                  ap (λ x → id ∘ x) β ∘ ap (\ x -> x ∘ id) α ≃〈 ap (λ f → f β ∘ ap (λ x → x ∘ id) α) is-id-ap-1 〉 
                  β ∘ ap (\ x -> x ∘ id) α                       ≃〈 ap (λ f → β ∘ f α) is-id-ap-2 〉 
                  β ∘ α ∎ where
      is-id-ap-1 : ap (\ (x : Ω1) -> id ∘ x) ≃ (\ (x : Ω2) -> x)
      is-id-ap-1 = λ≃ (\ x → ∘-unit-l x ∘ ap-by-id (\ y → ! (∘-unit-l y)) x) 
  
      is-id-ap-2 : ap (\ (x : Ω1) -> x ∘ id) ≃ (\ (x : Ω2) -> x)
      is-id-ap-2 = λ≃ ap-id -- cancels definitionally on this side

 