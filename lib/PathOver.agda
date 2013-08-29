
{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open import lib.Functions

module lib.PathOver where

  data PathOver {Δ : Type} (A : Δ → Type) : {θ1 θ2 : Δ} (δ : θ1 == θ2) (M1 : A θ1) (M2 : A θ2) → Type where
    id : ∀ {θ1} {M1 : A θ1} → PathOver A id M1 M1

  _∘o_ : {Δ : Type} {A : Δ → Type} {θ1 θ2 θ3 : Δ} {δ2 : θ2 == θ3} {δ1 : θ1 == θ2} {M1 : A θ1} {M2 : A θ2} {M3 : A θ3}
       → PathOver A δ2 M2 M3 
       → PathOver A δ1 M1 M2
       → PathOver A (δ2 ∘ δ1) M1 M3
  id ∘o id = id

  infixr 10 _∘o_

  !o : {Δ : Type} {A : Δ → Type} {θ1 θ2 : Δ} {δ : θ1 == θ2} {M1 : A θ1} {M2 : A θ2} 
       → PathOver A δ M1 M2 
       → PathOver A (! δ) M2 M1
  !o id = id

  pair= : {Δ : Type} {A : Δ → Type} {θ1 θ2 : Δ} (δ : θ1 == θ2) {M1 : A θ1} {M2 : A θ2} → PathOver A δ M1 M2 → (θ1 , M1) == (θ2 , M2)
  pair= ._ id = id

  apdo : {Δ : Type} {A : Δ → Type} (f : (θ : _) → A θ) {θ1 θ2 : Δ} (δ : θ1 == θ2) → PathOver A δ (f θ1) (f θ2)
  apdo f id = id

  changeover : {Δ : Type} (A : Δ → Type) {θ1 θ2 : Δ} {δ δ' : θ1 == θ2} (_ : δ == δ') {M1 : A θ1} {M2 : A θ2} → 
               PathOver A δ M1 M2
             → PathOver A δ' M1 M2
  changeover A id x = x

  -- funny way of saying functoriality
  PathOver-transport-∘ : {Δ : Type} (A : Δ → Type) {θ1 θ2 θ3 : Δ} (δ1 : θ1 == θ2) (δ2 : θ2 == θ3) {M1 : A θ1}
                       → PathOver A δ2 (transport A δ1 M1) (transport A (δ2 ∘ δ1) M1)
  PathOver-transport-∘ _ id id = id

  PathOver∘-transport : {Δ : Type} (A : Δ → Type) 
                      → ∀ {θ1 θ2 θ3} {δ2 : θ2 == θ3} (δ1 : θ1 == θ2) → ∀ {M1 M3} 
                      →  (PathOver A (δ2 ∘ δ1) M1 M3)
                      == (PathOver A δ2 (transport A δ1 M1) M3) 
  PathOver∘-transport A id = id

  PathOver-transport-right : {Δ : Type} (A : Δ → Type) {θ1 θ2 : Δ} (δ : θ1 == θ2) {M1 : A θ1}
                           → PathOver A δ M1 (transport A δ M1)
  PathOver-transport-right A δ {M1} =
    changeover A (∘-unit-l δ)
      (coe (! (PathOver∘-transport A δ {M1 = M1} {M3 = transport A δ M1}))
           id) 
    -- or PathOver-transport-∘ A id δ

  PathOver-transport-left : {Δ : Type} (A : Δ → Type) {θ1 θ2 : Δ} (δ : θ1 == θ2) {M2 : A θ2}
                          → PathOver A δ (transport A (! δ) M2) M2
  PathOver-transport-left _ id = id

  -- implies het to hom if hom is defined as path over refl!

{-
  path-ind : {Γ : Type} {A : Γ → Type} {M : (θ : Γ) → A θ} 
             (C : {θ : Γ} → (N : A θ) → PathOver A id (M θ) N → Type)
           → ({θ : Γ} → C (M θ) id)
           → ({θ : Γ} (N : A θ) (α : PathOver A id (M θ) N) → C N α)
  path-ind {A = A} {M} C b {θ} N α = transport
                                       (λ (p : Σ \ (θN : Σ A) → PathOver A id (M (fst θN)) (snd θN)) →
                                          C (snd (fst p)) (snd p))
                                       (pair= (pair= id α) {! !}) 
                                       b
-}
  -- need : PathOver (λ θN → PathOver A id (M (fst θN)) (snd θN)) (pair= id α) id α

{-
  Factor! : {Δ : Type} (A : Δ → Type) → Type
  Factor! A = ∀ {θ1 θ2} {δ : θ1 == θ2} → ∀ {M1 M2} 
          → (α : PathOver A (! δ) M2 M1)
          → Σ \ (α' : PathOver A δ M1 M2) → α == (!o α')

  factor!' : ∀ {Δ} (A : Δ → Type) → ∀ {θ1 θ2} {δ : θ1 == θ2} → ∀ {M1 M2} 
          → (α : PathOver A δ M1 M2)
          → α == changeover A (!-invol δ) (!o (!o α))
  factor!' A id = id

  factor! : ∀ {Δ} (A : Δ → Type) → ∀ {θ1 θ2} {δ : θ1 == θ2} → ∀ {M1 M2} 
          → (α : PathOver A (! δ) M2 M1)
          → α == !o (changeover A (!-invol δ) (!o α))
  factor! A {δ = id} α = factor!' A α

  factor∘ : {Δ : Type} (A : Δ → Type) 
         → ∀ {θ1 θ2 θ3} {δ2 : θ2 == θ3} {δ1 : θ1 == θ2} → ∀ {M1 M3} 
         → (α : PathOver A (δ2 ∘ δ1) M1 M3)
         → α == (coe (PathOver∘-transport A δ1) α) ∘o (PathOver-transport-right A δ1)
  factor∘ A {.θ3} {.θ3} {θ3} {.id} {id} id = id 
-}

{-
  factor3a : {Δ : Type} (A : Δ → Type) → ∀ {θ1 θ2 θ3 θ4} {δ3 : θ3 == θ4} (δ2 : θ1 == θ3) (δ1 : θ1 == θ2) → ∀ {M1 M4} 
          → (α : PathOver A ((δ3 ∘ δ2) ∘ ! δ1) M1 M4)
          → _
  factor3a A {δ3 = δ3} δ2 δ1 α = (coe (PathOver∘-transport A (δ2 ∘ ! δ1)) (changeover A (! (∘-assoc δ3 δ2 (! δ1))) α))

  factor3b : {Δ : Type} (A : Δ → Type) → ∀ {θ1 θ2 θ3} (δ2 : θ1 == θ3) (δ1 : θ1 == θ2) → ∀ {M1} 
          → PathOver A δ2 (transport A (! δ1) M1) (transport A (δ2 ∘ ! δ1) M1)
  factor3b A δ2 δ1 = PathOver-transport-∘ A (! δ1) δ2

  factor3c : {Δ : Type} (A : Δ → Type) → ∀ {θ1 θ2} (δ1 : θ1 == θ2) → ∀ {M1} 
          → PathOver A δ1 _ M1
  factor3c A δ1 = (PathOver-transport-left A δ1)
  
  factor3 : {Δ : Type} (A : Δ → Type) → ∀ {θ1 θ2 θ3 θ4} {δ3 : θ3 == θ4} {δ2 : θ1 == θ3} {δ1 : θ1 == θ2} → ∀ {M1 M4} 
          → (α : PathOver A ((δ3 ∘ δ2) ∘ ! δ1) M1 M4)
          → α == (_∘o_ {A = A} {δ2 = δ3} {δ1 = δ2} 
                       (factor3a A δ2 δ1 α)
                       (factor3b A δ2 δ1))
                 ∘o (!o {δ = δ1} (factor3c A δ1))
  factor3 A {δ2 = id} {δ1 = id} id = id
-}
  
  postulate
    PathOverΠ : {Δ : Type} {A : Δ → Type} {B : Σ A → Type}
              → {θ1 θ2 : Δ} {δ : θ1 == θ2} {f : (x : A θ1) → B (θ1 , x)} {g : (x : A θ2) → B (θ2 , x)}
              →  PathOver (\ θ → (x : A θ) → B (θ , x)) δ f g 
              == ((x : A θ1) (y : A θ2) (α : PathOver A δ x y) → PathOver B (pair= δ α) (f x) (g y))

    PathOverType : {Δ : Type} {A B : Type}
              → {θ1 θ2 : Δ} {δ : θ1 == θ2}
              → PathOver (\ θ → Type) δ A B == Equiv A B 

  PathOverType-changeover : {Δ : Type} {θ1 θ2 : Δ} {δ δ' : θ1 == θ2} (eq : δ == δ') {M1 : _} {M2 : _} → 
               (α : PathOver (\ _ -> Type) δ M1 M2)
             → coe PathOverType α == coe PathOverType (changeover (\ _ -> Type) eq α)
  PathOverType-changeover id α = id
    
  -- ----------------------------------------------------------------------
  -- "computation steps"

  Square : ∀{Δ} {θ11 θ12 θ21 θ22 : Δ} → (δ1- : θ11 == θ12) (δ2- : θ21 == θ22) (δ-1 : θ11 == θ21) (δ-2 : θ12 == θ22) → Type
  Square δ1- δ2- δ-1 δ-2 = δ-2 == δ2- ∘ δ-1 ∘ ! δ1-

  natural : {Γ Δ : Type} → ∀ {θ1 θ2 θ1' θ2'} (δ : (θ : Γ) → θ1 θ == θ2 θ) (δ' : θ1' == θ2') → Square {Δ} (ap θ1 δ') (ap θ2 δ') (δ θ1') (δ θ2')
  natural δ id = ! (∘-unit-l (δ _))

  factor∘-type : {Δ : Type} (A : Δ → Type) → Type
  factor∘-type {Δ} A = ∀ {θ1 θ2 θ3} {δ2 : θ2 == θ3} {δ1 : θ1 == θ2} → ∀ {M1 M3} 
          → (α : PathOver A (δ2 ∘ δ1) M1 M3)
          → Σ \ M2 → Σ \ (α1 : PathOver A δ1 M1 M2) → Σ \ (α2 : PathOver A δ2 M2 M3) → α == (α2 ∘o α1)

  factor∘-type'' : {Δ : Type} (A : Δ → Type) → Type
  factor∘-type'' {Δ} A = ∀ {θ1 θ2 θ3} {δ2 : θ2 == θ3} {δ1 : θ1 == θ2} → ∀ {M1 M3} 
          → (α : PathOver A (δ2 ∘ δ1) M1 M3)
          → Σ \ (α1 : PathOver A δ1 M1 (transport A δ1 M1)) → Σ \ (α2 : PathOver A δ2 (transport A δ1 M1) M3) 
          → α == (α2 ∘o α1)

{-
  factor!-Π-def : {Δ : Type} (A : Δ → Type) (B : Σ A → Type) 
                → Factor! A
                → Factor! {!!}
                → Factor! (\ θ → (x : A θ) → B (θ , x))
  factor!-Π-def A B f!A f!B α = 
    coe (! PathOverΠ) (λ x y α₁ → {!coe PathOverΠ α y x (changeover A ? (fst (f!A α₁)))!}) , 
    {!!}
-}
{-
  Transport-PathOver : {Δ : Type} (A : Δ → Type) → Type
  Transport-PathOver {Δ} A = {θ11 θ12 θ21 θ22 : Δ} {δ1- : θ11 == θ12} {δ2- : θ21 == θ22} {δ-1 : θ11 == θ21} 
                             → ∀ {M11 M12 M21 M22}
                             → PathOver A δ1- M11 M12
                             → PathOver A δ2- M21 M22 
                             → PathOver A δ-1 M11 M21
                             → PathOver A ((δ2- ∘ δ-1) ∘ ! δ1-) M12 M22

  transport-PathOver-Π-def : {Δ : Type} (A : Δ → Type) (B : Σ A → Type) 
                       → Transport-PathOver (\ θ → (x : A θ) → B (θ , x))
  transport-PathOver-Π-def A B {δ1- = δ1- } {δ2- = δ2- } {δ-1 = δ-1 } α1- α2- α-1 = 
    coe (! (PathOverΠ {_} {A} {B}))
        (λ x y α → changeover B {!!} ((coe PathOverΠ α2- _ _ (factor3a A δ-1 δ1- α) ∘o 
                                      coe PathOverΠ α-1 _ _ (factor3b A δ-1 δ1-)) ∘o 
                                      !o (coe PathOverΠ α1- _ _ (factor3c A δ1-))))
-}
  -- and it's an equivalence
  PathOver-o : {Γ Δ : Type} (A : Δ → Type) {θ1 : Γ → Δ} 
               {θ1' θ2' : _} {δ' : θ1' == θ2'}  → ∀ {M1 M2}
             → PathOver (A o θ1) δ' M1 M2
             → PathOver A (ap θ1 δ') M1 M2
  PathOver-o _ id = id

  transport-PathOver-by-hand : {Δ : Type} (A : Δ → Type) {θ11 θ12 θ21 θ22 : Δ} {δ1- : θ11 == θ12} {δ2- : θ21 == θ22} {δ-1 : θ11 == θ21} {δ-2 : θ12 == θ22}
                             → Square δ1- δ2- δ-1 δ-2
                             → ∀ {M11 M12 M21 M22}
                             → PathOver A δ1- M11 M12
                             → PathOver A δ2- M21 M22 
                             → PathOver A δ-1 M11 M21
                             → PathOver A δ-2 M12 M22
  transport-PathOver-by-hand A sq α1- α2- α-1 = changeover A (! sq) (α2- ∘o α-1 ∘o !o α1-)

{-
  transport-PathOver : {Γ Δ : Type} (A : Δ → Type) → {θ1 θ2 : Γ → Δ} (δ : (θ : Γ) → θ1 θ == θ2 θ) (M1 : (θ : _) → A (θ1 θ)) (M2 : (θ : _) → A (θ2 θ))
                       {θ1' θ2' : _} (δ' : θ1' == θ2')
                     → transport (\ θ → PathOver A (δ θ) (M1 θ) (M2 θ)) δ' == 
                       transport-PathOver-by-hand A (natural δ δ') (PathOver-o A (apdo M1 δ')) (PathOver-o A (apdo M2 δ'))
  transport-PathOver = {!!}
-}