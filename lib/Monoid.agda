{-# OPTIONS --type-in-type #-}

open import lib.First
open import lib.Paths
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
                 record { _⊙_ = transport (λ A' → A' → A' → A') α (Monoid._⊙_ M); 
                                 `1 = transport (λ A' → A') α (Monoid.`1 M); 
                                 assoc = transport{Σ (λ (A' : Set) → (A' → A' → A') × A')}
                                           (λ (p : Σ (λ (A' : Set) → (A' → A' → A') × A')) →
                                              let A' : Set
                                                  A' = fst p
                                                  _⊙_ : A' -> A' -> A'
                                                  _⊙_ = fst (snd p)
                                                  `1 : A'
                                                  `1 = snd (snd p)
                                              in {x y z : A'} → (x ⊙ y) ⊙ z ≃ x ⊙ (y ⊙ z))
                                           {(A , Monoid._⊙_ M , Monoid.`1 M)}
                                           {(B , transport (λ A' → A' → A' → A') α (Monoid._⊙_ M) , transport (λ A' → A') α (Monoid.`1 M))} 
                                           (pair≃ α (ap≃ (transport-× α (λ A' → A' → A' → A') (λ A' → A'))))
                                           (Monoid.assoc M); 
                                 unitl = transport {Σ (λ (A' : Set) → (A' → A' → A') × A')}
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
                                            transport (λ A' → A' → A' → A') α (Monoid._⊙_ M) ,
                                            transport (λ A' → A') α (Monoid.`1 M)}
                                           (pair≃ α
                                            (ap≃ (transport-× α (λ A' → A' → A' → A') (λ A' → A'))))
                                           (Monoid.unitl M); 
                                 unitr = transport {Σ (λ (A' : Set) → (A' → A' → A') × A')}
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
                                            transport (λ A' → A' → A' → A') α (Monoid._⊙_ M) ,
                                            transport (λ A' → A') α (Monoid.`1 M)}
                                           (pair≃ α
                                            (ap≃ (transport-× α (λ A' → A' → A' → A') (λ A' → A'))))
                                           (Monoid.unitr M) }

  transport-Monoid : ∀ {A B} -> (α : Id A B) -> 
                 transport Monoid α
               ≃ MonoidB α
  transport-Monoid id = id

  -- snd-pair≃⁻-id : {A : Set} {B : A -> Set} {x q : Σ B} 
  --       -> (α : x ≃ (fst q)) 
  --       -> respd (snd{A}{B}) (pair≃⁻ α () ≃ {!β!}
  -- snd-pair≃⁻-id = {!!}

{-
roughly (modulo adjustments)
  id at backmap
∘ resp blah (Monoid.unitl M)
∘ 
respd snd
   (pair≃⁻
    (pair≃ α
     (resp (λ f → f ((λ v v' → Monoid._⊙_ M v v') , Monoid.`1 M))
      (NDPair.transport-× α (λ A' → A' → A' → A') (λ A' → A'))))
    id)
   ∘
   resp
   (transport (λ z → fst (fst z))
    (pair≃⁻
     (pair≃ α
      (resp (λ f → f ((λ v v' → Monoid._⊙_ M v v') , Monoid.`1 M))
       (NDPair.transport-× α (λ A' → A' → A' → A') (λ A' → A'))))
     id))
   (Monoid.unitl M)
   ∘
   !
   (respd (λ p → fst (snd (fst p)) (snd (snd (fst p))) (snd p))
    (pair≃⁻
     (pair≃ α
      (resp (λ f → f ((λ v v' → Monoid._⊙_ M v v') , Monoid.`1 M))
       (NDPair.transport-× α (λ A' → A' → A' → A') (λ A' → A'))))
     id))
-}

{-
  transport-unitl : ∀ {A B} (α : A ≃ B) (M : Monoid A) ->
                Id{ {x : B} -> (Monoid._⊙_ (MonoidB α M) (Monoid.`1 (MonoidB α M)) x) ≃ x }
                  (Monoid.unitl (MonoidB α M))
                  (Monoid.unitl (MonoidB α M))
  transport-unitl {A}{B} α M = {!!} ∘ 
    λ≃i (λ x → transport-Id-d{Σ \ (p : Σ \ (A : Set) -> (A -> A -> A) × A) -> fst p} 
                         (λ p → fst (snd (fst p)) (snd (snd (fst p))) (snd p))
                         snd (pair≃⁻
                                (pair≃ α
                                 (ap≃ (NDPair.transport-× α (λ A' → A' → A' → A') (λ A' → A'))))
                                (id {_})) (Monoid.unitl M))
    -- (λ≃i (λ x → transport-Id (λ p → fst (snd (fst p)) (snd (snd (fst p))) (snd p)) 
    --                                              snd
    --                                              (pair≃⁻ (pair≃ α (ap≃ (NDPair.transport-× α (λ A' → A' → A' → A') (λ A' → A')))) (id {_}))
    --                                              (Monoid.unitl M {x})))
    ∘ transport-Πi{Σ \ (A : Set) -> (A -> A -> A) × A}
                     fst 
                     (λ p x → fst (snd p) (snd (snd p)) x ≃ x)
                     (pair≃ α
                        (ap≃ (NDPair.transport-× α (λ A' → A' → A' → A') (λ A' → A')))) (Monoid.unitl M)
-}
                 
              