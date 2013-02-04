
{-# OPTIONS --type-in-type --without-K #-}

open import lib.Paths

open import lib.Prods 
open import lib.AdjointEquiv 

module lib.ProdPaths where

  Σ≃Iso : {A : Set} {B : A -> Set} {M N : Σ B}
        -> Iso (Σ \ (α : Id (fst M) (fst N)) -> 
                    Id (subst B α (snd M)) (snd N))
               (Id M N) 
  Σ≃Iso {A}{B}{M}{N} = (λ x → pair≃ (fst x) (snd x)) , isiso (λ α → fst≃ α , snd≃ α) 
          (λ y → pair≃ (resp fst y) (snd≃ y) 
                       ≃〈 Refl 〉
                 pair≃ (fst≃ y) (snd≃ y)
                       ≃〈 Σ≃η y 〉
                 (y ∎)) 
          (λ x → (resp fst (pair≃ (fst x) (snd x)) , snd≃{A}{B} (pair≃ (fst x) (snd x)))
                 ≃〈 pair≃ (Σ≃β1 (fst x) (snd x)) 
                          (subst (λ α → Id (subst B α (snd M)) (snd N))
                             (Σ≃β1 (fst x) (snd x)) (snd≃{A}{B} (pair≃ (fst x) (snd x)))
                               ≃〈 subst-Id (λ x' → subst B x' (snd M)) (λ _ → snd N) 
                                          (Σ≃β1 (fst x) (snd x)) (snd≃ {A} {B} (pair≃ (fst x) (snd x))) 〉 
                          (resp (λ x → (snd N)) (Σ≃β1{A}{B} (fst x) (snd x))) ∘ 
                          (snd≃{A}{B} (pair≃ (fst x) (snd x))) ∘
                          (! (resp (λ x → subst B x (snd M)) (Σ≃β1 (fst x) (snd x))))
                               ≃〈 resp
                                     (λ p →
                                        resp (λ x' → snd N) (Σ≃β1 {A} {B} (fst x) (snd x)) ∘
                                        p ∘ ! (resp (λ x' → subst B x' (snd M)) (Σ≃β1 (fst x) (snd x))))
                                     (Σ≃β2{A}{B} (fst x) (snd x)) 〉
                          (resp (λ x → (snd N)) (Σ≃β1{A}{B} (fst x) (snd x))) ∘
                          ((snd x) ∘ (resp (λ x' → subst B x' (snd M)) (Σ≃β1 {B = B} (fst x) (snd x)))) ∘
                          (! (resp (λ x → subst B x (snd M)) (Σ≃β1 (fst x) (snd x))))
                               ≃〈 resp (λ p → resp (λ x' → snd N) (Σ≃β1 {A} {B} (fst x) (snd x)) ∘ p)
                                     (sym (∘-assoc (snd x) 
                                             (resp (λ x' → subst B x' (snd M)) (Σ≃β1 {B = B} (fst x) (snd x))) 
                                             (! (resp (λ x' → subst B x' (snd M)) (Σ≃β1 (fst x) (snd x)))))) 〉
                          (resp (λ x → (snd N)) (Σ≃β1{A}{B} (fst x) (snd x))) ∘
                          (snd x) ∘ (resp (λ x' → subst B x' (snd M)) (Σ≃β1 {B = B} (fst x) (snd x))) ∘
                          (! (resp (λ x → subst B x (snd M)) (Σ≃β1 (fst x) (snd x))))
                               ≃〈 resp
                                     (λ p →
                                        resp (λ x' → snd N) (Σ≃β1 {A} {B} (fst x) (snd x)) ∘ snd x ∘ p)
                                     (!-inv-r (resp (λ x' → subst B x' (snd M)) (Σ≃β1 (fst x) (snd x)))) 〉
                          (resp (λ x → (snd N)) (Σ≃β1{A}{B} (fst x) (snd x))) ∘ (snd x) ∘ Refl
                               ≃〈 resp (λ p → resp (λ x' → snd N) (Σ≃β1 {A} {B} (fst x) (snd x)) ∘ p)
                                     (∘-unit-r (snd x)) 〉
                          (resp (λ x → (snd N)) (Σ≃β1{A}{B} (fst x) (snd x))) ∘ (snd x)
                               ≃〈 resp (λ p → p ∘ snd x) (resp-constant (snd N) (Σ≃β1 {A} {B} (fst x) (snd x))) 〉
                          Refl ∘ (snd x)
                               ≃〈 ∘-unit-l (snd x) 〉
                          (snd x ∎)) 〉 
                 (fst x , snd x) ∎)

{-
          (λ x → (resp fst (pair≃ (fst x) (snd x)) , snd≃ (pair≃ (fst x) (snd x)))
                       ≃〈 resp (λ p → p , snd≃ (pair≃ (fst x) (snd x))) 
                               (Σ≃β1 (fst x) (snd x)) 〉
                 (fst x , snd≃ (pair≃ (fst x) (snd x)))
                       ≃〈 resp (λ p → fst x , p) 
                               (Σ≃β2 (fst x) (snd x)) 〉
                 (x ∎))
-}

