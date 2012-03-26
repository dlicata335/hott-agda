{-# OPTIONS --type-in-type --without-K --allow-unsolved-metas #-}

open import lib.Paths 
open import lib.Prods
open Paths

module lib.Functions where 
 
  _o_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
  g o f = \ x -> g (f x)

  -- interchange law for the type theory as a whole:
  -- objects = types
  -- morphisms = functions
  -- 2-cells = identity type
  ichange-theory : {Γ1 Γ2 Γ3 : Set} 
                   {θ1 θ2 θ3 : Γ1 -> Γ2} 
                   {θ1' θ2' θ3' : Γ2 -> Γ3} 
                   (δ1 : θ1 ≃ θ2) (δ2 : θ2 ≃ θ3)
                   (δ1' : θ1' ≃ θ2') (δ2' : θ2' ≃ θ3')
                 -> resp2 _o_ (δ2' ∘ δ1') (δ2 ∘ δ1) ≃ resp2 _o_ δ2' δ2 ∘ resp2 _o_ δ1' δ1 
  ichange-theory Refl Refl Refl Refl = Refl
  

  app≃ : ∀ {A} {B : A -> Set} {f g : (x : A) -> B x} 
       -> Id f g -> ({x : A} -> Id (f x) (g x))
  app≃ α {x} = resp (\ f -> f x) α

  app≃2 : ∀ {A} {B : A -> Set} {f g : (x : A) -> B x} 
       -> Id f g -> ({x y : A} -> (α : Id x y) -> Id (subst B α (f x)) (g y))
  app≃2 {A} {B} {f} {.f} Refl Refl = Refl 

  postulate 
    λ≃ : ∀ {A} {B : A -> Set} {f g : (x : A) -> B x} -> ((x : A) -> Id (f x) (g x)) -> Id f g
    Π≃η : ∀ {A} {B : A -> Set} {f g : (x : A) -> B x} -> (α : Id f g)
         -> α ≃ λ≃ (\ x -> app≃ α {x})
    -- FIXME Π≃β

  subst-→ : ∀ {Γ} (A B : Γ -> Set) {θ1 θ2 : Γ} (δ : θ1 ≃ θ2) (f : (A θ1) -> B θ1) 
         -> subst (\ γ -> (A γ) -> B γ) δ f ≃ (\ y -> subst B δ (f (subst A (! δ) y)))
  subst-→ _ _ Refl f = Refl 

  -- substitution extension for Γ,x:A⁻ in DTT
  pair≃⁻ : {A : Set} {B : A -> Set} {p q : Σ B} 
        -> (α : (fst p) ≃ (fst q)) -> (snd p) ≃ subst B (! α) (snd q) 
        -> p ≃ q
  pair≃⁻ {A}{B}{p}{q} α β = pair≃ α 
                                 (app≃ (resp (λ x → subst B x) (!-inv-r α) ∘ ! (subst-∘ B (! α) α)) ∘ resp (subst B α) β)

  subst-Π : ∀ {Γ} (A : Γ -> Set) (B : (γ : Γ) -> A γ -> Set)
            {θ1 θ2 : Γ} (δ : θ1 ≃ θ2) (f : (x : A θ1) -> B θ1 x) 
         -> subst (\ γ -> (x : A γ) -> B γ x) δ f ≃ 
            (\ γ -> subst (\ (p : Σ \ (γ : Γ) -> A γ) -> B (fst p) (snd p))
                          (pair≃⁻ δ Refl)
                          (f (subst A (! δ) γ)))
  subst-Π _ _ Refl f = Refl

  resp-λ : {Γ : Set} {θ1 θ2 : Γ} {δ : θ1 ≃ θ2}
           {A : Γ -> Set} {B : (γ : Γ) -> A γ -> Set}
           {M : (γ : Γ) -> (x : A γ) -> B γ x}
        -> (respd (\ γ -> (λ x -> M γ x)) δ) 
         ≃ λ≃ (λ γ → respd (λ (p : Σ (λ (γ' : Γ) → A γ')) → M (fst p) (snd p))
                           (pair≃⁻ δ Refl))
           ∘ subst-Π A B δ (M θ1)
  resp-λ {δ = Refl} = Π≃η Refl

  subst-com-for-resp-app : 
    {Γ : Set} {θ1 θ2 : Γ} (δ : θ1 ≃ θ2)
    (A : Γ -> Set) (B : (γ : Γ) -> A γ -> Set)
    (F : (γ : Γ) -> (x : A γ) -> B γ x)
    (M : (γ : Γ) -> A γ)
   -> Id (subst (λ z → B z (M z)) δ (F θ1 (M θ1)))
        (subst (λ z → B θ2 z) (respd M δ)
         (subst (λ z → (x : A z) → B z x) δ (F θ1)
          (subst (λ z → A z) δ (M θ1))))
  subst-com-for-resp-app Refl _ _ _ _ = Refl

  resp-app : {Γ : Set} {θ1 θ2 : Γ} {δ : θ1 ≃ θ2}
             {A : Γ -> Set} {B : (γ : Γ) -> A γ -> Set}
             {F : (γ : Γ) -> (x : A γ) -> B γ x}
             {M : (γ : Γ) -> A γ}
           -> respd (\ γ -> (F γ) (M γ)) δ 
            ≃ app≃2 (respd F δ) (respd M δ) ∘ subst-com-for-resp-app δ A B F M
  resp-app {δ = Refl} = Refl
             