{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude

module programming.Functor where

  record Functor (F : Type → Type) : Type where
    constructor functor
    field
      map         : ∀ {A B} → (A → B) → F A → F B
      identity    : ∀ {A} (a : F A) → map (\ (x : A) → x) a == a
      composition : ∀ {A B C} {g : B → C} {f : A → B} (a : F A) → map (g o f) a == map g (map f a)

  functor-equality-lemma : {F : Type → Type} 
                           {map : ∀ {A B} → (A → B) → F A → F B}
                           {identity identity'  : ∀ {A} (a : F A) → map (\ (x : A) → x) a == a}
                           {composition composition' : ∀ {A B C} {g : B → C} {f : A → B} (a : F A) → map (g o f) a == map g (map f a)}
                           → ({A : Type} (a : F A) → identity a == identity' a)
                           → ({A B C : Type} {g : B → C} {f : A → B} (a : F A) → composition{A}{B}{C}{g}{f} a == composition' a)
                           → (functor map identity composition) == (functor map identity' composition')
  functor-equality-lemma {F}{map} ident-eq comp-eq = ap2
                                                       (λ (x : {A : _} (a : F A) → map (λ (x₁ : A) → x₁) a == a)
                                                          (y : {A B C : _} {g : B → C} {f : A → B} (a : F A) → map (g o f) a == map g (map f a)) → functor map x y)
                                                       (λ≃i (λ A → λ≃ (λ a → ident-eq a)))
                                                       (λ≃i (λ A → λ≃i (λ B → λ≃i (λ C → λ≃i (λ g → λ≃i (λ f → λ≃ (λ a → comp-eq a)))))))

  transport-Functor-eqv : {F G : Type → Type} (n : (X : Type) → Equiv (F X) (G X)) → Functor F → Functor G
  transport-Functor-eqv {F}{G} n (functor map ident comp) = functor map' identity' composition' where
    map' : ∀ {A B} → (A → B) → G A → G B
    map' {A}{B} f a with n B | n A
    ...              | (fB , _) | (_ , isequiv gA _ _ _) = fB (map f (gA a))

    identity' : ∀ {A} (a : G A) → map' (\ (x : A) → x) a == a
    identity' {A} a with n A
    ...                | (fA , isequiv gA αA βA _) = βA a ∘ ap (λ h → fA h) (ident (gA a))

    composition' : ∀ {A B C} {g : B → C} {f : A → B} (a : G A) → map' (g o f) a == map' g (map' f a)
    composition' {A}{B}{C} {g}{f} a with n A | n B | n C 
    ... | (fA , isequiv gA αA βA _) | (fB , isequiv gB αB βB _) | (fC , isequiv gC αC βC _) = 
      fC (map (λ x₁ → g (f x₁)) (gA a)) =〈 ap fC (comp (gA a)) 〉
      fC (map g (map f (gA a))) =〈 ap (λ h → fC (map g h)) (! (αB (map f (gA a)))) 〉
      fC (map g (gB (fB (map f (gA a))))) ∎

  transport-Functor-eqv-id : {F : Type → Type} (func : Functor F)
                             → transport-Functor-eqv (\ A -> id-equiv {F A}) func  == func
  transport-Functor-eqv-id {F} (functor map identity comp) = functor-equality-lemma (λ a → ap-id (identity a) ∘ ∘-unit-l (ap (λ x → x) (identity a)))
                                                                                    (λ a → ap-id (comp a) ∘ ∘-unit-l (ap (λ x → x) (comp a)))

  transport-Functor : {F G : Type → Type} (func : Functor F) (α : F ≃ G) 
                   → transport Functor α func == transport-Functor-eqv (λ X → coe-equiv (ap≃ α {X})) func
  transport-Functor func id = ! (transport-Functor-eqv-id func) 
