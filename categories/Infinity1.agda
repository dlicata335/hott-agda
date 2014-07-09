{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude

module categories.Infinity1 where
  
  postulate 
    parametricity : {A B : Type} (f : (X : Type) → (B → X) → (A → X)) 
                  → (X : _) (k : B → X) → f X k == \ a -> k (f B (\ x -> x) a)

    parametricity-comp : {A B : Type} (f : (X : Type) → (B → X) → (A → X)) 
                       → parametricity f B (\ x -> x) == id 

  yoneda : {A B : Type} → (Equiv ((X : Type) → (B → X) → (A → X)) (A → B))
  yoneda {A} {B} = (equiv (λ f → f _ (λ x → x)) 
                          (λ f X k a → k (f a))
                          (λ f → λ≃ (λ X → λ≃ (λ k → ! (parametricity f X k))))
                          (λ X → id) 
                          (λ f → !
                                   (ap-o (λ g → g (λ x → x)) (λ f₁ → f₁ B)
                                    (λ≃ (λ X → λ≃ (λ k → ! (parametricity f X k)))))
                                   ∘ !
                                       (ap (ap (λ g → g (λ x → x)))
                                        (Π≃β (λ X → λ≃ (λ k → ! (parametricity f X k)))))
                                       ∘ ! (Π≃β (λ k → ! (parametricity f B k))) ∘ ! (ap ! (parametricity-comp f))))


  -- doesn't work for all C, but does for Globs defined below

  -- morphism-induction : {A : Type} (C : (B : Type) → ((X : Type) → (B → X) → (A → X)) → Type)
  --                    → C A (λ X k → k) 
  --                    → {B : Type} (f : (X : Type) → (B → X) → A → X)
  --                    → C B f

  data Glob (A B : Type) : Type
  T : {A B : Type} → Glob A B -> Type

  data Glob A B where
    *   : Glob A B
    Hom : (G : Glob A B) -> T G -> T G -> Glob A B

  T {A}{B} (*) = (X : Type) → (B → X) → A → X
  T (Hom G M N) = Path {T G} M N

  Inst : {A B : Type} → Glob A B → Type 
  inst : {A B : Type} → (G : Glob A B) → (T G) == (Inst G)

  Inst {A}{B} * = A → B
  Inst {A}{B} (Hom G x y) = Path {Inst G} (coe (inst G) x) (coe (inst G) y)

  inst {A}{B} * = ua yoneda
  inst (Hom G x y) = apPath≃ (inst G) id id

{-  
  T' : {A B : Type} → Glob A B → (X : Type) (k : B → X) → Type
  inst' : {A B : Type} → (G : Glob A B) → T G == ((X : Type) (k : B → X) → T' G X k )

  T' {A}{B} * X k = A → X
  T' (Hom G x y) X k = Path {T' G X k} (coe (inst' G) x X k) (coe (inst' G) y X k)

  inst' * = id
  inst' (Hom G x x₁) = {!!}
-}


