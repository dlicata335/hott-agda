
{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open import lib.Prods
open import lib.AdjointEquiv
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

  !Σ : {Δ : Type} {A : Δ → Type} {θ1 θ2 : Δ} (δ : θ1 == θ2) {M1 : A θ1} {M2 : A θ2} → (α : PathOver A δ M1 M2) 
      → ! (pair= δ α) == pair= (! δ) (!o α)
  !Σ .id id = id

  ∘Σ : {Δ : Type} {A : Δ → Type} {θ1 θ2 θ3 : Δ} (δ2 : θ2 == θ3) (δ1 : θ1 == θ2)
        {M1 : A θ1} {M2 : A θ2} {M3 : _} → (α2 : PathOver A δ2 M2 M3) (α1 : PathOver A δ1 M1 M2) 
      → (pair= δ2 α2) ∘ (pair= δ1 α1) == pair= (δ2 ∘ δ1) (α2 ∘o α1)
  ∘Σ .id .id id id = id

  Σ=β1 : {A : Type} {B : A -> Type} {p q : Σ B} 
       (α : Path (fst p) (fst q)) 
       (β : PathOver B α (snd p) (snd q))
       -> Path (ap fst (pair= α β)) α
  Σ=β1 {p = x , y} {q = .x , .y} ._ id = id

  apdo : {Δ : Type} {A : Δ → Type} (f : (θ : _) → A θ) {θ1 θ2 : Δ} (δ : θ1 == θ2) → PathOver A δ (f θ1) (f θ2)
  apdo f id = id

  ido-constant : {Δ : Type} {A : Type} {θ1 θ2 : Δ} {M : A} (δ : θ1 == θ2) → PathOver (\ _ -> A) δ M M
  ido-constant id = id

  changeover= : {Δ : Type} (A : Δ → Type) {θ1 θ2 : Δ} {δ δ' : θ1 == θ2} (_ : δ == δ') {M1 : A θ1} {M2 : A θ2} → 
               PathOver A δ M1 M2
              == PathOver A δ' M1 M2
  changeover= A id = id

  changeover : {Δ : Type} (A : Δ → Type) {θ1 θ2 : Δ} {δ δ' : θ1 == θ2} (_ : δ == δ') {M1 : A θ1} {M2 : A θ2} → 
               PathOver A δ M1 M2
             → PathOver A δ' M1 M2
  changeover A α = coe (changeover= A α)

  -- funny way of saying functoriality
  PathOver-transport-∘ : {Δ : Type} (A : Δ → Type) {θ1 θ2 θ3 : Δ} (δ1 : θ1 == θ2) (δ2 : θ2 == θ3) {M1 : A θ1}
                       → PathOver A δ2 (transport A δ1 M1) (transport A (δ2 ∘ δ1) M1)
  PathOver-transport-∘ _ id id = id

  -- need this for factoring, which is necessary for defining ∘ at Π
  PathOver∘-transport : {Δ : Type} (A : Δ → Type) 
                      → ∀ {θ1 θ2 θ3} {δ2 : θ2 == θ3} (δ1 : θ1 == θ2) → ∀ {M1 M3} 
                      →  (PathOver A (δ2 ∘ δ1) M1 M3)
                      == (PathOver A δ2 (transport A δ1 M1) M3) 
  PathOver∘-transport A id = id

  PathOver-transport-right : {Δ : Type} (A : Δ → Type) {θ1 θ2 : Δ} (δ : θ1 == θ2) {M1 : A θ1}
                           → PathOver A δ M1 (transport A δ M1)
  PathOver-transport-right A id {M1} = id
  {- two alternate proofs:
     (1) 
     changeover A (∘-unit-l δ)
      (coe (! (PathOver∘-transport A δ {M1 = M1} {M3 = transport A δ M1}))
           id) 
     (2) 
     PathOver-transport-∘ A id δ 
  -}

  -- implies het to hom if hom is defined as path over refl!
  het=homo : {Δ : Type} (A : Δ → Type) 
            → ∀ {θ1 θ2} (δ : θ1 == θ2) → ∀ {M1 M2} 
            →  (PathOver A δ M1 M2)
            == (PathOver A id (transport A δ M1) M2) 
  het=homo A δ = PathOver∘-transport A {δ2 = id} δ ∘ changeover= A (! (∘-unit-l δ))

{-
  only for constant families

  path-induction-homo' : {Δ : Type} {A : Type} {θ1 θ2 : Δ} {M : A} {δ : θ1 == θ2}
                       (C : (x : A) → PathOver (\ (_ : Δ) -> A) δ M x → Type)
                     → (C M (ido-constant δ))
                     → {N : A} → (P : PathOver (\ _ -> A) δ M N) → C N P
  path-induction-homo' C b id = b

  path-induction-homo : {Δ : Type} {A : Type} {M : A} {θ : Δ}
                       (C : (x : A) → PathOver (\ _ -> A) (id{_}{θ}) M x → Type)
                     → (C M id)
                     → {N : A} → (P : PathOver (\ _ -> A) id M N) → C N P
  path-induction-homo C b α = path-induction-homo' C b α
-}

  path-induction-homo'' : {Δ : Type} {A : Δ → Type} {θ1 θ2 : Δ} {δ : θ1 == θ2} {M : A θ1} 
                       (C : (x : A θ2) → PathOver A δ M x → Type)
                     → (C (transport A δ M) (PathOver-transport-right A δ))
                     → {N : A θ2} → (P : PathOver A δ M N) → C N P
  path-induction-homo'' C b id = b

  path-induction-homo' : {Δ : Type} {A : Δ → Type} {θ1 θ2 : Δ} (δ : θ1 == θ2) {M : A θ1} 
                       (C : (x : A θ2) → PathOver A (id{_}{θ2}) (transport A δ M) x → Type)
                     → (C (transport A δ M) id)
                     → {N : A θ2} → (P : PathOver A id (transport A δ M) N) → C N P
  path-induction-homo' {A = A} δ {M} C b α =
    transport (\ x -> C _ x) (ap≃ (transport-inv-2 (λ x → x) (PathOver∘-transport A δ ∘ changeover= A (! (∘-unit-l δ)))))
              (path-induction-homo'' (λ x p → C x (coe (het=homo A δ) p))
                                      (transport (λ x → C _ x) 
                                                 -- FIXME: exactly what properties of context paths do you need to prove this?
                                                 -- how would you do it in a type theory without path-induction for δ?
                                                 (path-induction
                                                    (λ _ δ₁ →
                                                       id ==
                                                       transport (λ x → x)
                                                       (PathOver∘-transport A δ₁ ∘ changeover= A (! (∘-unit-l δ₁)))
                                                       (PathOver-transport-right A δ₁))
                                                    id δ) 
                                                 b)
                                      (coe (! (het=homo A δ)) α)) 

  path-induction-homo : {Δ : Type} {A : Δ → Type} {θ1 : Δ} {M : A θ1} 
                       (C : (x : A θ1) → PathOver A (id{_}{θ1}) M x → Type)
                     → (C M id)
                     → {N : A θ1} → (P : PathOver A id M N) → C N P
  path-induction-homo C b α = path-induction-homo' id C b α

  PathOver-transport-left : {Δ : Type} (A : Δ → Type) {θ1 θ2 : Δ} (δ : θ1 == θ2) {M2 : A θ2}
                          → PathOver A δ (transport A (! δ) M2) M2
  PathOver-transport-left _ id = id

  apdo1 : {Δ : Type} {A : Δ → Type} {B : Σ A → Type} 
          {θ : Δ} (f : (x : A θ) → B (θ , x)) {M1 : _} {M2 : _}
          (α : PathOver A id M1 M2) 
        → PathOver B (pair= (id{_}{θ}) α) (f M1) (f M2)
  apdo1 {Δ} {A} {B} {θ} f {M1} {M2} α = 
      (path-induction-homo{Δ = Δ}{A = A} 
       (λ M2 α₁ → PathOver B (pair= (id {_} {θ}) α₁) (f M1) (f M2)) id α)

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

  postulate
    PathOverΠ : {Δ : Type} {A : Δ → Type} {B : Σ A → Type}
              → {θ1 θ2 : Δ} {δ : θ1 == θ2} {f : (x : A θ1) → B (θ1 , x)} {g : (x : A θ2) → B (θ2 , x)}
              →  PathOver (\ θ → (x : A θ) → B (θ , x)) δ f g 
              == ((x : A θ1) (y : A θ2) (α : PathOver A δ x y) → PathOver B (pair= δ α) (f x) (g y))

    PathOverΠ-id : {Δ : Type} {A : Δ → Type} {B : Σ A → Type}
                 → {θ1 : Δ} (f : (x : A θ1) → B (θ1 , x)) {x : _}
                 → coe (PathOverΠ {A = A} {B = B}{δ = id} {f = f}) id x x id == id

    PathOverType : {Δ : Type} {A B : Type}
              → {θ1 θ2 : Δ} {δ : θ1 == θ2}
              → PathOver (\ θ → Type) δ A B == Equiv A B 

    PathOverType-id : {Δ : Type} {θ : Δ} {A : Type} → coe (PathOverType{_}{_}{_}{θ}) id == (id-equiv{A})

    PathOverType-!  : {Δ : Type} {θ1 θ2 : Δ} {δ : θ1 == θ2} {A B : Type} {α : PathOver (\ _ -> Type) δ A B}
                    → coe PathOverType (!o α) == (!equiv (coe PathOverType α))

  PathOverType-∘ : {Δ : Type} {A B C : Type}
              → {θ1 θ2 θ3 : Δ} {δ2 : θ2 == θ3} {δ1 : θ1 == θ2}
              → (α2 : PathOver (\ θ → Type) δ2 B C) (α1 : PathOver (\ θ → Type) δ1 A B) 
              → (coe PathOverType α2) ∘equiv (coe PathOverType α1) == coe PathOverType (α2 ∘o α1)
  PathOverType-∘ id id = (! PathOverType-id ∘ pair≃ id (HProp-unique (IsEquiv-HProp (λ x → x)) _ _)) ∘ ap2 _∘equiv_ PathOverType-id PathOverType-id

  PathOverType-changeover : {Δ : Type} {θ1 θ2 : Δ} {δ δ' : θ1 == θ2} (eq : δ == δ') {M1 : _} {M2 : _} → 
               (α : PathOver (\ _ -> Type) δ M1 M2)
             → coe PathOverType α == coe PathOverType (changeover (\ _ -> Type) eq α)
  PathOverType-changeover id α = id
    
  -- and it's an equivalence
  over-o-ap : {Γ Δ : Type} (A : Δ → Type) {θ1 : Γ → Δ} 
               {θ1' θ2' : _} {δ' : θ1' == θ2'}  → ∀ {M1 M2}
             → PathOver (A o θ1) δ' M1 M2
             → PathOver A (ap θ1 δ') M1 M2
  over-o-ap _ id = id

  over-ap-o : {Γ Δ : Type} (A : Δ → Type) {θ1 : Γ → Δ} 
               {θ1' θ2' : _} {δ' : θ1' == θ2'}  → ∀ {M1 M2}
             → PathOver A (ap θ1 δ') M1 M2
             → PathOver (A o θ1) δ' M1 M2
  over-ap-o A {δ' = id} α = path-induction-homo (λ M2 _ → PathOver (A o _) id _ M2) id α

  over-apd : {A : Type} {B : A → Type}  (C : Σ B → Type)
             {a1 a2 : A} (α : a1 == a2)
             (f : (x : A) → B x) {M1 : _} {M2 : _}
           → PathOver C (pair= α (apdo f α)) M1 M2
           -> PathOver (\ a -> C (a , f a)) α M1 M2
  over-apd C id f = over-ap-o C {λ x → x , f x} {_} {_} {id}

  over-apd-inverse : {A : Type} {B : A → Type}  (C : Σ B → Type)
             {a1 a2 : A} (α : a1 == a2)
             (f : (x : A) → B x) {M1 : _} {M2 : _}
           -> PathOver (\ a -> C (a , f a)) α M1 M2
           → PathOver C (pair= α (apdo f α)) M1 M2
  over-apd-inverse C id f = over-o-ap C {λ x → x , f x} {_} {_} {id}

  transport-Πo : ∀ {Γ} (A : Γ -> Set) (B : (γ : Γ) -> A γ -> Set)
            {θ1 θ2 : Γ} (δ : θ1 == θ2) (f : (x : A θ1) -> B θ1 x) 
         -> transport (\ γ -> (x : A γ) -> B γ x) δ f ==
            (\ x -> transport (\ (p : Σ \ (γ : Γ) -> A γ) -> B (fst p) (snd p))
                          (pair= δ (PathOver-transport-left A δ))
                          (f (transport A (! δ) x)))
  transport-Πo _ _ id f = id

  path-to-pathover : {Δ : Type} (A : Δ → Type) {θ : Δ} {M N : A θ} → M == N → PathOver A id M N
  path-to-pathover A id = id

  Square : ∀{Δ} {θ11 θ12 θ21 θ22 : Δ} → (δ1- : θ11 == θ12) (δ2- : θ21 == θ22) (δ-1 : θ11 == θ21) (δ-2 : θ12 == θ22) → Type
  Square δ1- δ2- δ-1 δ-2 = δ-2 == δ2- ∘ δ-1 ∘ ! δ1-

  natural : {Γ Δ : Type} → ∀ {θ1 θ2 θ1' θ2'} (δ : (θ : Γ) → θ1 θ == θ2 θ) (δ' : θ1' == θ2') → Square {Δ} (ap θ1 δ') (ap θ2 δ') (δ θ1') (δ θ2')
  natural δ id = ! (∘-unit-l (δ _))

  transport-PathOver-by-hand : {Δ : Type} (A : Δ → Type) {θ11 θ12 θ21 θ22 : Δ} {δ1- : θ11 == θ12} {δ2- : θ21 == θ22} {δ-1 : θ11 == θ21} {δ-2 : θ12 == θ22}
                             → Square δ1- δ2- δ-1 δ-2
                             → ∀ {M11 M12 M21 M22}
                             → PathOver A δ1- M11 M12
                             → PathOver A δ2- M21 M22 
                             → PathOver A δ-1 M11 M21
                             → PathOver A δ-2 M12 M22
  transport-PathOver-by-hand A sq α1- α2- α-1 = changeover A (! sq) (α2- ∘o α-1 ∘o !o α1-)

  transport-PathOver : {Γ Δ : Type} (A : Δ → Type) → {θ1 θ2 : Γ → Δ} (δ : (θ : Γ) → θ1 θ == θ2 θ) (M1 : (θ : _) → A (θ1 θ)) (M2 : (θ : _) → A (θ2 θ))
                       {θ1' θ2' : _} (δ' : θ1' == θ2')
                     → transport (\ θ → PathOver A (δ θ) (M1 θ) (M2 θ)) δ' == 
                       transport-PathOver-by-hand A (natural δ δ') (over-o-ap A (apdo M1 δ')) (over-o-ap A (apdo M2 δ'))
  transport-PathOver A δ M1 M2 id = λ≃ coh where
    coh : {θ1 : _} {θ2 : _} {δ : θ1 == θ2} {M1 : _} {M2 : _} → (x : PathOver A δ M1 M2) →
      x ==
      (transport (λ x₁ → x₁) (changeover= A (! (! (∘-unit-l δ)))) (id ∘o x ∘o id))
    coh id = id
