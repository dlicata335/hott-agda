{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths 
open import lib.Prods
open import lib.NTypes
open Paths

module lib.AdjointEquiv where

 record IsEquiv {A B : Type} (f : A → B) : Type where
  constructor isequiv
  field
     g : B → A
     α : (x : A) → Path (g (f x)) x
     β : (y : B) → Path (f (g y)) y
     γ : (x : A) →  Path (β (f x)) (ap f (α x)) -- coherence condition necessary for higher spaces
     -- also satifies:
     -- (y : B) →  Path (α (g y)) (ap g (β y));
     -- this is just γ with f<→g and α<→β, so we'll prove this in
     -- the process of defining !-equiv below

 Equiv : Type -> Type -> Type
 Equiv A B = Σ (IsEquiv{A}{B})

 equiv : {A B : Type}
     (f : A → B)
     (g : B → A)
     (α : (x : A) → Path (g (f x)) x)
     (β : (y : B) → Path (f (g y)) y)
     (γ : (x : A) →  Path (β (f x)) (ap f (α x)))
   → Equiv A B
 equiv f g α β γ = f , isequiv g α β γ

 record IsHEquiv {A B : Type} (f : A → B) : Type where
   constructor ishequiv
   field
     g : B → A
     α : (x : A) → Path (g (f x)) x
     β : (y : B) → Path (f (g y)) y

 HEquiv : Type → Type → Type
 HEquiv A B = Σ (IsHEquiv{A}{B})

 hequiv : {A B : Type}
     (f : A → B)
     (g : B → A)
     (α : (x : A) → Path (g (f x)) x)
     (β : (y : B) → Path (f (g y)) y)
     → HEquiv A B
 hequiv f g α β = f , ishequiv g α β

 inverses-natural : ∀ {A B} (f : A → B) (g : B → A) (η : (x : A) → Path (g (f x)) x)
                      {x : A} 
                   → Path (η (g (f x))) (ap (g o f) (η x))
 inverses-natural f g η {x} = 
   (∘-unit-l _ ∘ ap (λ y → y ∘ ap (λ x' → g (f x')) (η x)) (!-inv-l (η x))) ∘ 
   ap (λ a → (! a ∘ η x) ∘ ap (g o f) (η x)) (ap-id (η x)) ∘
   move-right-right-! (η (g (f x))) (ap (λ x' → g (f x')) (η x)) _
     (move-right (ap (λ x' → x') (η x)) (η (g (f x)) ∘ ! (ap (λ x' → g (f x')) (η x))) _
       (apd η (η x) ∘ ! (transport-Path (g o f) (λ x' → x') (η x) (η (g (f x)))))) 

 improve : {A B : Type} → HEquiv A B → Equiv A B
 improve (f , ishequiv g η ξ) = 
   equiv f g 
         η 
         (λ x → ξ x ∘ ap f (η (g x)) ∘ ap (f o g) (! (ξ x)))
         coh where
   abstract -- we might someday need to know this, but for now it's slowing things down too much
            -- at call sites to normalize it
     coh : (x : _) -> ξ (f x) ∘ ap f (η (g (f x))) ∘ ap (f o g) (! (ξ (f x))) ≃ ap f (η x)
     coh =
         (λ x → ξ (f x) ∘ ap f (η (g (f x))) ∘ ap (f o g) (! (ξ (f x)))                            ≃〈 ap (λ a → ξ (f x) ∘ ap f a ∘ ap (f o g) (! (ξ (f x)))) (inverses-natural f g η) 〉 
                ξ (f x) ∘ ap f (ap (g o f) (η x)) ∘ ap (f o g) (! (ξ (f x)))                      ≃〈 ap (λ a → ξ (f x) ∘ a ∘ ap (f o g) (! (ξ (f x)))) (ap-o (f o g) f (η x) ∘ ! (ap-o f (g o f) (η x))) 〉 
                ξ (f x) ∘ ap (f o g) (ap f (η x)) ∘ ap (f o g) (! (ξ (f x)))                      ≃〈 ap (λ a → ξ (f x) ∘ a ∘ ap (f o g) (! (ξ (f x)))) (ap (λ a → ! (ξ (f x)) ∘ ap f (η x) ∘ a) (!-invol (ξ (f (g (f x))))) ∘ ap-by-id (λ x' → ! (ξ x')) (ap f (η x))) 〉 
                ξ (f x) ∘ (! (ξ (f x)) ∘ (ap f (η x)) ∘ ξ (f (g (f x)))) ∘ ap (f o g) (! (ξ (f x))) ≃〈 rassoc-1-3-1 (ξ (f x)) (! (ξ (f x))) (ap f (η x)) (ξ (f (g (f x)))) (ap (f o g) (! (ξ (f x)))) 〉 
                ξ (f x) ∘ ! (ξ (f x)) ∘ (ap f (η x)) ∘ ξ (f (g (f x))) ∘ ap (f o g) (! (ξ (f x)))   ≃〈 !-inv-r-front (ξ (f x)) (ap f (η x) ∘ ξ (f (g (f x))) ∘ ap (f o g) (! (ξ (f x)))) 〉 
                (ap f (η x)) ∘ ξ (f (g (f x))) ∘ ap (f o g) (! (ξ (f x)))                          ≃〈 ap (λ a → ap f (η x) ∘ a ∘ ap (f o g) (! (ξ (f x)))) (inverses-natural g f ξ) 〉 
                (ap f (η x)) ∘ ap (f o g) (ξ ((f x))) ∘ ap (f o g) (! (ξ (f x)))                  ≃〈 ap (λ a → ap f (η x) ∘ ap (f o g) (ξ (f x)) ∘ a) (ap-! (f o g) (ξ (f x))) 〉 
                (ap f (η x)) ∘ ap (f o g) (ξ ((f x))) ∘ ! (ap (f o g) (ξ (f x)))                  ≃〈 ap (λ a → ap f (η x) ∘ a) (!-inv-r (ap (f o g) (ξ (f x)))) 〉 
                (ap f (η x) ∎)) 

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
 
{- 
 -- FIXME move somewhere else

 -- might want to know what coercing by this does... 
 apΣ : {A A' : Type} {B : A → Type} {B' : A' → Type}
       (a : A ≃ A')
       (b : (\ (x : A) → B x) ≃ (\ (x : A) → B' (coe a x)))
     → Σ B ≃ Σ B'
 apΣ id id = id

 -- build in some β reduction
 apΣ' : {A A' : Type} {B : A → Type} {B' : A' → Type}
        (a : Equiv A A')
        (b : (x' : A') → B (IsEquiv.g (snd a) x') ≃ B' x')
      → Σ B ≃ Σ B'
 apΣ' {A = A} {B = B} {B' = B'}  a b = apΣ (ua a) (λ≃ (λ x' → ap B' (! (ap≃ (type≃β a))) ∘ b (fst a x') ∘ ap B (! (IsEquiv.α (snd a) _)))) -- (λ≃ (λ x → ap B' (! (ap≃ (type≃β a))) ∘ b x))

 uncurry≃ : (A : Type) (B : A -> Type) (C : Σ B -> Type)
          -> ((p : Σ B) → C p)
          ≃  ((x : A) (y : B x) -> C (x , y))
 uncurry≃ _ _ _ = ua (equiv (λ f x y → f (x , y)) (λ f p → f (fst p) (snd p)) (λ _ → id) (λ _ → id) (λ _ → id))

 exchange≃ : {A : Type} {B : Type} {C : A → B → Type}
           -> ((x : A) (y : B) → C x y)
            ≃ ((y : B) (x : A) → C x y)
 exchange≃ = ua (equiv (λ f x y → f y x) (λ f x y → f y x) (λ _ → id) (λ _ → id) (λ _ → id))

 path-induction≃ : {B : Type} {b : B} {C : (y : B) -> Path b y → Type}
                   → ((y : B) (p : Path b y) → C y p)
                   ≃ C b id
 path-induction≃ {b = b} {C = C} = ua (improve (hequiv (λ f → f b id) (λ b' y p → path-induction C b' p) (λ f → λ≃ (λ x → λ≃ (λ p → path-induction (λ x' x0 → Id (path-induction C (f b id) x0) (f x' x0)) id p))) (λ _ → id)))

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
-}

 postulate
   IsEquiv-HProp : {A B : Type} (f : A → B) → HProp (IsEquiv f)



   
               
 