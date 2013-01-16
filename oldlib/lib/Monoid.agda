{-# OPTIONS --type-in-type #-}

open import lib.Paths
open Paths
open import lib.Prods
open import lib.Functions

module lib.Monoid where

  record Monoid (A : Set) : Set where
    field
      _⊙_ : A -> A -> A
      `1  : A
      assoc : ∀ {x y z} -> (x ⊙ y) ⊙ z ≃ x ⊙ (y ⊙ z)
      unitl : ∀ {x} -> (`1 ⊙ x) ≃ x
      unitr : ∀ {x} -> (x ⊙ `1) ≃ x

  MonoidB : ∀ {A B} -> (α : Id A B) -> (M : Monoid A) -> Monoid B
  MonoidB {A}{B} α M = 
                 record { _⊙_ = subst (λ A' → A' → A' → A') α (Monoid._⊙_ M); 
                                 `1 = subst (λ A' → A') α (Monoid.`1 M); 
                                 assoc = subst{Σ (λ (A' : Set) → (A' → A' → A') × A')}
                                           (λ (p : Σ (λ (A' : Set) → (A' → A' → A') × A')) →
                                              let A' : Set
                                                  A' = fst p
                                                  _⊙_ : A' -> A' -> A'
                                                  _⊙_ = fst (snd p)
                                                  `1 : A'
                                                  `1 = snd (snd p)
                                              in {x y z : A'} → (x ⊙ y) ⊙ z ≃ x ⊙ (y ⊙ z))
                                           {(A , Monoid._⊙_ M , Monoid.`1 M)}
                                           {(B , subst (λ A' → A' → A' → A') α (Monoid._⊙_ M) , subst (λ A' → A') α (Monoid.`1 M))} 
                                           (pair≃ α (app≃ (NDPair.subst-× α (λ A' → A' → A' → A') (λ A' → A'))))
                                           (Monoid.assoc M); 
                                 unitl = subst {Σ (λ (A' : Set) → (A' → A' → A') × A')}
                                           (λ (p : Σ (λ (A' : Set) → (A' → A' → A') × A')) →
                                              let A' : Set
                                                  A' = fst p
                                                  _⊙_ : A' → A' → A'
                                                  _⊙_ = fst (snd p)
                                                  `1 : A'
                                                  `1 = snd (snd p)
                                              in {x : A'} → `1 ⊙ x ≃ x)
                                           {A , Monoid._⊙_ M , Monoid.`1 M}
                                           {B ,
                                            subst (λ A' → A' → A' → A') α (Monoid._⊙_ M) ,
                                            subst (λ A' → A') α (Monoid.`1 M)}
                                           (pair≃ α
                                            (app≃ (NDPair.subst-× α (λ A' → A' → A' → A') (λ A' → A'))))
                                           (Monoid.unitl M); 
                                 unitr = subst {Σ (λ (A' : Set) → (A' → A' → A') × A')}
                                           (λ (p : Σ (λ (A' : Set) → (A' → A' → A') × A')) →
                                              let A' : Set
                                                  A' = fst p
                                                  _⊙_ : A' → A' → A'
                                                  _⊙_ = fst (snd p)
                                                  `1 : A'
                                                  `1 = snd (snd p)
                                              in {x : A'} → x ⊙ `1 ≃ x)
                                           {A , Monoid._⊙_ M , Monoid.`1 M}
                                           {B ,
                                            subst (λ A' → A' → A' → A') α (Monoid._⊙_ M) ,
                                            subst (λ A' → A') α (Monoid.`1 M)}
                                           (pair≃ α
                                            (app≃ (NDPair.subst-× α (λ A' → A' → A' → A') (λ A' → A'))))
                                           (Monoid.unitr M) }

  subst-Monoid : ∀ {A B} -> (α : Id A B) -> 
                 subst Monoid α
               ≃ MonoidB α
  subst-Monoid Refl = Refl

  -- snd-pair≃⁻-Refl : {A : Set} {B : A -> Set} {x q : Σ B} 
  --       -> (α : x ≃ (fst q)) 
  --       -> respd (snd{A}{B}) (pair≃⁻ α () ≃ {!β!}
  -- snd-pair≃⁻-Refl = {!!}

{-
roughly (modulo adjustments)
  Refl at backmap
∘ resp blah (Monoid.unitl M)
∘ 
respd snd
   (pair≃⁻
    (pair≃ α
     (resp (λ f → f ((λ v v' → Monoid._⊙_ M v v') , Monoid.`1 M))
      (NDPair.subst-× α (λ A' → A' → A' → A') (λ A' → A'))))
    Refl)
   ∘
   resp
   (subst (λ z → fst (fst z))
    (pair≃⁻
     (pair≃ α
      (resp (λ f → f ((λ v v' → Monoid._⊙_ M v v') , Monoid.`1 M))
       (NDPair.subst-× α (λ A' → A' → A' → A') (λ A' → A'))))
     Refl))
   (Monoid.unitl M)
   ∘
   !
   (respd (λ p → fst (snd (fst p)) (snd (snd (fst p))) (snd p))
    (pair≃⁻
     (pair≃ α
      (resp (λ f → f ((λ v v' → Monoid._⊙_ M v v') , Monoid.`1 M))
       (NDPair.subst-× α (λ A' → A' → A' → A') (λ A' → A'))))
     Refl))
-}

{-
  subst-unitl : ∀ {A B} (α : A ≃ B) (M : Monoid A) ->
                Id{ {x : B} -> (Monoid._⊙_ (MonoidB α M) (Monoid.`1 (MonoidB α M)) x) ≃ x }
                  (Monoid.unitl (MonoidB α M))
                  (Monoid.unitl (MonoidB α M))
  subst-unitl {A}{B} α M = {!!} ∘ 
    λ≃i (λ x → subst-Id-d{Σ \ (p : Σ \ (A : Set) -> (A -> A -> A) × A) -> fst p} 
                         (λ p → fst (snd (fst p)) (snd (snd (fst p))) (snd p))
                         snd (pair≃⁻
                                (pair≃ α
                                 (app≃ (NDPair.subst-× α (λ A' → A' → A' → A') (λ A' → A'))))
                                (Refl {_})) (Monoid.unitl M))
    -- (λ≃i (λ x → subst-Id (λ p → fst (snd (fst p)) (snd (snd (fst p))) (snd p)) 
    --                                              snd
    --                                              (pair≃⁻ (pair≃ α (app≃ (NDPair.subst-× α (λ A' → A' → A' → A') (λ A' → A')))) (Refl {_}))
    --                                              (Monoid.unitl M {x})))
    ∘ subst-Πi{Σ \ (A : Set) -> (A -> A -> A) × A}
                     fst 
                     (λ p x → fst (snd p) (snd (snd p)) x ≃ x)
                     (pair≃ α
                        (app≃ (NDPair.subst-× α (λ A' → A' → A' → A') (λ A' → A')))) (Monoid.unitl M)
-}
                 
              