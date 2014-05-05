{-# OPTIONS --type-in-type --new-without-K #-}

open import lib.Prelude

module categories.Infinity1Diag where
  
  data Diag : Type 
  data Ty : (Δ : Diag) → Type
  data Tm (Δ : Diag) : Ty Δ → Type
  data Var : (Δ : Diag) (A : Ty Δ) → Set 
  data Subst (Δ1 : Diag) : (Δ2 : Diag) → Set

  ⋆' : ∀ {Δ} → Ty Δ
  v' : ∀ {Δ} → {A : Ty Δ} → Var Δ A → Tm Δ A

  data Diag where
    ⋆ : Diag
    _,1_ : (Δ : Diag) → (X : Tm Δ ⋆') → Diag
    _,2_ : (Δ : Diag) → {A : Ty Δ} → Tm Δ A → Diag

  w1-ty : ∀ {Δ X} → Ty Δ → Ty (Δ ,1 X)
  w2-ty : ∀ {Δ A} {M : Tm Δ A} → Ty Δ → Ty (Δ ,2 M)
  w1-tm : ∀ {Δ X A} → Tm Δ A → Tm (Δ ,1 X) (w1-ty A)
  w2-tm : ∀ {Δ A0 A} {M0 : Tm Δ A0} → Tm Δ A → Tm (Δ ,2 M0) (w2-ty A)

  sub-ty : ∀ {Δ Δ'} → Ty Δ' → Subst Δ Δ' → Ty Δ
  sub-tm : ∀ {Δ Δ' A} → Tm Δ' A → (θ : Subst Δ Δ') → Tm Δ (sub-ty A θ)

  data Ty where
    ⋆ : ∀ {Δ} → Ty Δ
    Hom1 : ∀ {Δ} → (X : Tm Δ ⋆) → (Y : Tm Δ ⋆) → Ty Δ
    Hom2 : ∀ {Δ} → (A : Ty Δ) → (M N : Tm Δ A) → Ty Δ  -- oops want this to be morphisms or higher

  ⋆' = ⋆

  sub-ty ⋆ θ = ⋆
  sub-ty (Hom1 X Y) θ = Hom1 (sub-tm X θ) (sub-tm Y θ)
  sub-ty (Hom2 A M N) θ = Hom2 _ (sub-tm M θ) (sub-tm M θ)
  
  w1-ty ⋆ = ⋆
  w1-ty (Hom1 X Y) = Hom1 (w1-tm X) (w1-tm Y)
  w1-ty (Hom2 A M N) = Hom2 (w1-ty A) (w1-tm M) (w1-tm N)

  w2-ty ⋆ = ⋆
  w2-ty (Hom1 X Y) = Hom1 (w2-tm X) (w2-tm Y)
  w2-ty (Hom2 A M N) = Hom2 (w2-ty A) (w2-tm M) (w2-tm N)

  data Var where
    i00 : Var ⋆ ⋆
    i10 : ∀ {Δ X} → Var (Δ ,1 X) ⋆
    i11 : ∀ {Δ X} → Var (Δ ,1 X) (Hom1 (w1-tm X) (v' i10))
    iS1 : ∀ {Δ A X} → Var Δ A → Var (Δ ,1 X) (w1-ty A)
    iS2 : ∀ {Δ A A1} {M1 : Tm Δ A1} → Var Δ A → Var (Δ ,2 M1) (w2-ty A)
    
  data Tm Δ where 
    v : {A : Ty Δ} → Var Δ A → Tm Δ A
    ident : {X : Tm Δ ⋆} → Tm Δ (Hom1 X X)
    comp  : {X Y Z : Tm Δ ⋆} → Tm Δ (Hom1 X Y) → Tm Δ (Hom1 Y Z) → Tm Δ (Hom1 X Z)
    coh   : ∀ {Δ' : Diag} (A : Ty Δ') (M N : Tm Δ' A)
          → (θ : Subst Δ Δ')
          → Tm Δ (sub-ty (Hom2 A M N) θ)

  data Subst Δ1 where
    Single : Tm Δ1 ⋆ → Subst Δ1 ⋆
    _,1_,1_ : ∀ {Δ2 X} → (θ : Subst Δ1 Δ2) → (Y : Tm Δ1 ⋆) → Tm Δ1 (Hom1 (sub-tm X θ) Y) → Subst Δ1 (Δ2 ,1 X)
    _,2_,2_ : ∀ {Δ2 A} {M : Tm Δ2 A}
            → (θ : Subst Δ1 Δ2) → (N : Tm Δ1 (sub-ty A θ)) → Tm Δ1 (Hom2 (sub-ty A θ) (sub-tm M θ) N) 
            → Subst Δ1 (Δ2 ,2 M)

  v' = v

  w1-tm (v x) = v (iS1 x)
  w1-tm ident = ident
  w1-tm (comp M₃ M₄) = comp (w1-tm M₃) (w1-tm M₄)
  w1-tm (coh A M N θ) = {!coh (w1-ty A) (w1-tm M) (w1-tm N) ?!}

  w2-tm (v x) = v (iS2 x)
  w2-tm ident = ident
  w2-tm (comp M₃ M₄) = comp (w2-tm M₃) (w2-tm M₄)
  w2-tm (coh A M N θ) = {!!}

  sub-tm (v i00) (Single x) = x
  sub-tm (v i10) (θ ,1 Y ,1 f) = Y
  sub-tm (v i11) (θ ,1 Y ,1 f) = {!f!}
  sub-tm (v (iS1 x)) (θ ,1 Y ,1 x₁) = {!sub-tm (v x) θ!}
  sub-tm (v (iS2 x)) θ = {!!}
  sub-tm ident θ = ident
  sub-tm (comp M₃ M₄) θ = comp (sub-tm M₃ θ) (sub-tm M₄ θ)
  sub-tm (coh A M M₁ θ) θ₁ = {!coh A M M₁ ?!}

  -- end mutual

  postulate EQ : {A : Type} {M N : A} → M ≃ N


  interp-diag : Diag → Type
  interp-ty : ∀ {Δ} (A : Ty Δ) → interp-diag Δ → Type
  interp-tm : ∀ {Δ} {A : Ty Δ} → (M : Tm Δ A) (θ : interp-diag Δ) → interp-ty A θ
  interp-subst : ∀ {Δ Δ'} (θ : Subst Δ Δ') → interp-diag Δ → interp-diag Δ'
  interp-coh : ∀ {Δ} (A : Ty Δ) (M N : Tm Δ A) (θ : interp-diag Δ) → interp-tm M θ == interp-tm N θ

  interp-ty ⋆ θ = Type
  interp-ty (Hom1 X Y) θ = interp-tm X θ → interp-tm Y θ
  interp-ty (Hom2 A M N) θ = interp-tm M θ == interp-tm N θ

  interp-diag ⋆ = Type
  interp-diag (Δ ,1 X) = Σ (λ (θ : interp-diag Δ) → Σ (λ (Y : Type) → (interp-tm X θ) → Y))
  interp-diag (_,2_ Δ {A} M) = Σ (λ (θ : interp-diag Δ) → Σ (λ (N : interp-ty A θ) → interp-tm M θ == N))

  interp-tm (v i00) A = A
  interp-tm (v i10) (θ , Y , f) = Y
  interp-tm (v i11) (θ , Y , f) = coe EQ f
  interp-tm (v (iS1 x)) (θ , Y , f) = coe EQ (interp-tm (v x) θ)
  interp-tm (v (iS2 x)) (θ , Y , f) = coe EQ (interp-tm (v x) θ)
  interp-tm ident θ = (λ x → x) 
  interp-tm (comp M₃ M₄) θ = (interp-tm M₄ θ) o (interp-tm M₃ θ)
  interp-tm (coh A M N θ) θ₁ = coe EQ (interp-coh A M N (interp-subst θ θ₁))

  interp-subst (Single M) θ1 = interp-tm M θ1
  interp-subst (θ ,1 Y ,1 f) θ1 = interp-subst θ θ1 , interp-tm Y θ1 , coe EQ (interp-tm f θ1)
  interp-subst (θ ,2 N ,2 α) θ1 = interp-subst θ θ1 , coe EQ (interp-tm N θ1) , coe EQ (interp-tm α θ1)

{-
  interp-coh {⋆} ⋆ M N θ = {!!}
  interp-coh {⋆} (Hom1 (v i00) (v i00)) M N θ = {!!} -- M and N both equal to identity function
  interp-coh {⋆} (Hom2 A M N) M₁ N₁ θ = {!!} 
  interp-coh {Δ ,1 X} A M N θ = {!!}
  interp-coh {Δ ,2 x} A₁ M N θ = {!!}
-}

  identity-sub : {Δ : _} → Subst Δ Δ
  identity-sub {⋆} = Single (v i00)
  identity-sub {Δ ,1 X} = {!identity-sub {Δ}!} ,1 {!!} ,1 {!!}
  identity-sub {Δ ,2 M} = {!!}

  interp-coh {⋆} ⋆ M N θ = {!!}
  interp-coh {⋆} (Hom1 (v i00) (v i00)) M N θ = {!!} -- M and N both equal to identity function
  interp-coh {⋆} (Hom2 A M N) M₁ N₁ θ = {!!} 
  interp-coh {Δ ,1 X} A M N θ = {!!}
  interp-coh {Δ ,2 M0} A₁ M N (θ , .(interp-tm M0 θ) , id) = 
    coe {!!} (interp-coh {Δ}
                         (sub-ty A₁ (identity-sub {Δ} ,2 (sub-tm M0 identity-sub) ,2 {!!}))
                         (sub-tm M {!!})
                         (sub-tm N {!!}) θ)

  -- interp-coh ⋆ M N θ = {!!} -- FIXME: this case shouldn't exist
  -- interp-coh (Hom1 X Y) M N θ = {!!} 
  -- interp-coh (Hom2 A M N) M₁ N₁ θ = {!interp-coh A M N θ!} 

{-

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
-}
