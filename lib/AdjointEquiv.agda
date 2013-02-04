{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths 
open import lib.Prods
open import lib.NType
open import lib.WEq
open import lib.Functions

module lib.AdjointEquiv where

 id-equiv : ∀ {A} -> Equiv A A
 id-equiv = ( (\ x -> x) , isequiv (λ x → x) (\ _ -> id) (\ _ -> id) (\ _ -> id))

 !equiv : ∀ {A B} → Equiv A B → Equiv B A
 !equiv (f , isequiv g α β γ) = 
   equiv g f β α 
    (λ y → α (g y)                                                                       ≃〈 ! (∘-assoc (α (g y)) (ap (λ x → g (f x)) (α (g y))) (! (α (g (f (g y)))))) ∘ move-right-right-! (α (g y)) (! (α (g (f (g y))))) _ (move-right-! (α (g y)) (α (g y) ∘ ! (! (α (g (f (g y)))))) _ (! (ap-by-id (λ x → ! (α x)) (α (g y))))) 〉 
           α (g y) ∘ ap (g o f) (α (g y)) ∘ ! (α (g (f (g y))))                          ≃〈 ap (λ a → α (g y) ∘ a ∘ ! (α (g (f (g y))))) (ap (ap g) (! (γ (g y))) ∘ ap-o g f (α (g y))) 〉 
           α (g y) ∘ ap g (β (f (g y))) ∘ ! (α (g (f (g y))))                            ≃〈 ap (λ a → α (g y) ∘ ap g a ∘ ! (α (g (f (g y))))) (inverses-natural g f β) 〉 
           α (g y) ∘ ap g (ap (f o g) (β y)) ∘ ! (α (g (f (g y))))                      ≃〈 ap (λ a → α (g y) ∘ a ∘ ! (α (g (f (g y))))) (ap-o (g o f) g (β y) ∘ ! (ap-o g (f o g) (β y))) 〉 
           α (g y) ∘ ap (g o f) (ap g (β y)) ∘ ! (α (g (f (g y))))                      ≃〈 ap (λ a → α (g y) ∘ a ∘ ! (α (g (f (g y))))) (ap (λ a → ! (α (g y)) ∘ ap g (β y) ∘ a) (!-invol (α (g (f (g y))))) ∘ ap-by-id (λ x → ! (α x)) (ap g (β y))) 〉 
           α (g y) ∘ (! (α (g y)) ∘ (ap g (β y)) ∘ α (g (f (g y)))) ∘ ! (α (g (f (g y)))) ≃〈 rassoc-1-3-1 (α (g y)) (! (α (g y))) (ap g (β y)) (α (g (f (g y)))) (! (α (g (f (g y)))))〉 
           α (g y) ∘ ! (α (g y)) ∘ (ap g (β y)) ∘ α (g (f (g y))) ∘ ! (α (g (f (g y))))   ≃〈 !-inv-r-front _ _ 〉 
           (ap g (β y)) ∘ α (g (f (g y))) ∘ ! (α (g (f (g y))))                          ≃〈 !-inv-r-back (ap g (β y)) (α (g (f (g y)))) 〉 
           (ap g (β y) ∎))

 -- ENH: can probably do this one without changing α or β too
 _∘equiv_ : ∀ {A B C} -> Equiv B C → Equiv A B -> Equiv A C
 _∘equiv_ (f , isequiv g α β γ) (f' , isequiv g' α' β' γ') = 
    improve (hequiv (f o f') (g' o g) (λ x → α' x ∘ ap g' (α (f' x))) (λ y → β y ∘ ap f (β' (g y))))

 infixr 10 _∘equiv_
 
 IsEquiv-as-tuple≃ : ∀ {A B} (f : A → B)
                  -> IsEquiv f ≃ 
                     (Σe (Σe (B → A) (λ g → (x : B) → Id (f (g x)) x))
                          (λ gβ → Σe ((x : A) → Id (fst gβ (f x)) x)
                                     (λ α → (x : A) → Id (snd gβ (f x)) (ap f (α x)))))
 IsEquiv-as-tuple≃ f = ua (improve (hequiv (λ {(isequiv g α β γ) → (g , β) , α , γ}) (\ {((g , β) , αγ) → isequiv g (fst αγ) β (snd αγ)}) (λ _ → id) (λ _ → id)))

 IsWeq≃IsEquiv : {A B : Type} (f : A → B)
              -> IsWEq f ≃ IsEquiv f
 IsWeq≃IsEquiv{A}{B} f = IsWEq f ≃〈 id 〉 
                  ((y : B) → Contractible (Σ \x -> Path (f x) y)) ≃〈 id 〉 
                  ((y : B) → Σ (\ (p : (Σ \x -> Path (f x) y)) → ((q : (Σ \x -> Path (f x) y)) → Path p q))) ≃〈 ΠΣcommute _ _ _ 〉 
                  Σ (λ (f' : (x : B) → Σ (λ x' → Path (f x') x)) → (x : B) (q : Σ (λ x' → Path (f x') x)) → Path (f' x) q) ≃〈 apΣ' (ΠΣcommuteEquiv _ _ _) (λ x' → id) 〉 
                  Σ (λ (f' : Σ (λ (g : B → A) → (x : B) → Path (f (g x)) x)) 
                     → (y : B) (q : Σ (λ (x : A) → Path (f x) y)) → Path (fst f' y , snd f' y) q) ≃〈 ap (λ t → Σ {A = Σ (λ (g : B → A) → (x : B) → Path (f (g x)) x)} t) (λ≃ STS) 〉 
                  Σ (λ x → Σ (λ α → (x' : A) → snd x (f x') ≃ ap f (α x'))) ≃〈 ! (IsEquiv-as-tuple≃ f) 〉 
                  IsEquiv f ∎ where
   STS : (f' : Σ (λ (g : B → A) → (x : B) → Path (f (g x)) x)) → 
        ((y : B) (q : Σ (λ (x : A) → Path (f x) y)) → Path (fst f' y , snd f' y) q) 
       ≃ Σ (λ α → (x : A) → snd f' (f x) ≃ ap f (α x)) 
   STS f' = ((y : B) (q : Σ (λ (x : A) → Path (f x) y)) → Path (fst f' y , snd f' y) q) ≃〈 ap (λ C → (y : B) → C y) (λ≃ (λ y → uncurry≃ A (λ x → Path (f x) y) _)) 〉
            ((y : B) (x : A) (y' : Path (f x) y) → Path{Σ (λ v → Path (f v) y)} (fst f' y , snd f' y) (x , y')) ≃〈 exchange≃ 〉
            ((x : A) (y : B) (y' : Path (f x) y) → Path{Σ (λ v → Path (f v) y)} (fst f' y , snd f' y) (x , y')) ≃〈 ap (λ B' → (x : A) → B' x) (λ≃ (λ x → path-induction≃)) 〉
            ((x : A) → Path{Σ (λ v → Path (f v) (f x))} (fst f' (f x) , snd f' (f x)) (x , id)) ≃〈 ap (λ C → (x : A) → C x) (λ≃ (λ x → ! ΣPath.path)) 〉
            ((x : A) → Σ (λ α → Path (transport (λ v → Path (f v) (f x)) α (snd f' (f x))) id)) ≃〈 ΠΣcommute _ _ _ 〉 
            Σ (λ (α : (x : A) → Id (fst f' (f x)) x) → (x : A) → Path (transport (λ v → Path (f v) (f x)) (α x) (snd f' (f x))) id) ≃〈 ap (λ C → Σ (λ (α : (x : A) → Id (fst f' (f x)) x) → C α)) (λ≃ (λ α → ap (λ C → (x : A) → C x) (λ≃ (λ x → STS' α x)))) 〉 
            Σ (λ α → (x : A) → snd f' (f x) ≃ ap f (α x)) ∎ where
       STS' : (α : (x : A) → Id (fst f' (f x)) x) → 
              (x : A) 
            → Path (transport (λ v → Path (f v) (f x)) (α x) (snd f' (f x))) id
            ≃ (snd f' (f x) ≃ ap f (α x)) 
       STS' α x = transport (λ v → Path (f v) (f x)) (α x) (snd f' (f x)) ≃ id ≃〈 ap (BackPath _) (transport-Path-pre' f (α x) (snd f' (f x))) 〉
                  (snd f' (f x) ∘ ! (ap f (α x))) ≃ id ≃〈 cancels-inverse-is≃ (snd f' (f x)) (ap f (α x)) 〉 
                  (snd f' (f x)) ≃ (ap f (α x)) ∎

 abstract
   IsEquiv-HProp : {A B : Type} (f : A → B) → HProp (IsEquiv f)
   IsEquiv-HProp f = transport HProp (IsWeq≃IsEquiv f) (IsWEq-HProp f)



   
               
 