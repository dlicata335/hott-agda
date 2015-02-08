{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude

module categories.Infinity1-2 where
  
  postulate {- HoTT Axiom -}
  -- well not really HoTT, but it's a reasonable axiom
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


  data Diag : Type 
  data Ty : Diag → Type

  data Diag where
    ⋆ : Diag
    _,_ : (Δ : Diag) → Ty Δ → Diag

  data Ty where
    iX : Ty ⋆
    iY : ∀ {Δ X} → Ty (Δ , X)
    iS : ∀ {Δ X} → (x : Ty Δ) → Ty (Δ , X)

  interp : Diag → Type
  interpt : {Δ : Diag} → Ty Δ → interp Δ → Type

  interp ⋆ = Type
  interp (Δ , A) = Σ (λ (θ : interp Δ) → Σ (λ (Y : Type) → interpt A θ → Y))

  interpt iX X = X
  interpt iY (θ , Y , f) = Y
  interpt (iS A) (θ , _ , _) = interpt A θ

  Mor : (Δ : Diag) (θ1 θ2 : interp Δ) -> Type
  lookup : (Δ : Diag) {θ1 θ2 : interp Δ} (δ : Mor Δ θ1 θ2) → (X : Ty Δ) → interpt X θ1 → interpt X θ2

  Mor ⋆ A B = A → B
  Mor (Δ , X) (θ1 , Y1 , f1) (θ2 , Y2 , f2) = Σ (λ (δ : Mor Δ θ1 θ2) → Σ (λ (f : Y1 → Y2) → f o f1 == f2 o lookup Δ δ X))

  lookup ⋆ δ iX = δ
  lookup (Δ , x) (δ , f , α) iY = f
  lookup (Δ , x) (δ , _ , _) (iS X) = lookup Δ δ X

  has-transport : (Δ : Diag) (A : interp Δ → Type) → Type
  has-transport Δ A = {θ1 θ2 : interp Δ} → Mor Δ θ1 θ2 → A θ1 → A θ2

  has-transport-base : (Δ : Diag) (X Y : Ty Δ) → (f g : (θ : _) → interpt X θ → interpt Y θ)
                     → has-transport Δ (\ θ → Path {interpt X θ → interpt Y θ} (f θ) (g θ))
  has-transport-base .⋆ iX iX f g x x₁ = {!!} -- parametricity must both be id
  has-transport-base ._ iY iY f g {θ1 , Y1 , k1} {θ2 , y2 , k2} δ f1 = {!!} -- parametricity must both be id; other vars are irrelevant because you can't get back to X
  has-transport-base ._ (iS X₁) iY f g {θ1 , Y1 , k1} {θ2 , Y2 , k2} δ f1 = {!!}
  has-transport-base (Δ , X0) X (iS Y₁) f g x x₁ = {!!}

  has-ap : (Δ : Diag) (A : interp Δ → Type) (trA : has-transport Δ A) (M : (θ : _) → A θ) 
           → Type
  has-ap Δ A trA M = {θ1 θ2 : interp Δ} → (δ : Mor Δ θ1 θ2) → trA δ (M θ1) == M θ2

  has-transport-ind : (Δ : Diag) (A : interp Δ → Type) (M N : (θ : _) → A θ)
                    → (trA : has-transport Δ A)
                    → (apM : has-ap Δ A trA M)
                    → (apN : has-ap Δ A trA N)
                    → has-transport Δ (\ θ → Path {A θ} (M θ) (N θ))
  has-transport-ind Δ A M N trA apM apN {θ1} {θ2} δ α = apN δ ∘ ap (trA δ) α ∘ ! (apM δ)
