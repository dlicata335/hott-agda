  module ConstantFunction (A B : Type) (a : A) where
    l : (Σ \(f : A → B) → (a a' : A) → f a ≃ f a') -> B
    l (f , _ ) = f a

    r : B → (Σ \(f : A → B) → (a a' : A) → f a ≃ f a')
    r b = ((\ _ -> b) , \ _ _ -> id)
    
    lr : l o r == (\ x -> x)
    lr = id

    rl : r o l == (\ x -> x)
    rl = λ≃ (λ { (f , p) → pair≃ (λ≃ (λ a' → p a a')) 
                                 (transport (λ v → (a₁ a' : A) → Id (v a₁) (v a')) (λ≃ (λ a' → p a a')) (λ _ _ → id) ≃〈 transport-Π2 A (λ v a₁ → (a' : A) → v a₁ ≃ v a') (λ≃ (λ a' → p a a')) (λ _ _ → id) 〉
                                  (λ a₁ → transport (λ z → (x : A) → Id (z a₁) (z x)) (λ≃ (p a)) (λ x → id)) ≃〈 (λ≃ \a1 -> transport-Π2 A (\ v a' -> v a1 ≃ v a') (λ≃ (λ a' → p a a')) (λ _ → id)) 〉 
                                  (λ a₁ x → transport (λ z → Id (z a₁) (z x)) (λ≃ (p a)) id) ≃〈 λ≃ (λ a1 → λ≃ (λ a2 → transport-Path (λ z → z a1) (λ z → z a2) (λ≃ (p a)) id)) 〉 
                                  (λ a₁ x → ap (λ z → z x) (λ≃ (p a)) ∘ id ∘ ! (ap (λ z → z a₁) (λ≃ (p a)))) ≃〈 {!!} 〉 
                                  (λ a₁ x → p a x ∘ ! (p a a₁)) ≃〈 id 〉 
                                  (λ a1 a2 → p a a2 ∘ ! (p a a1)) ≃〈 λ≃ (λ a1 → λ≃ (λ a2 → {!(p a1 a2)!})) 〉 
                                  (\ a1 a2 → p a1 a2) ∎)})
