
{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Prods
open import lib.Functions
open import lib.AdjointEquiv
open import lib.Paths

module lib.cubical.PathOver where

  module PathOver' where
    PathOver' : {Δ : Type} (A : Δ → Type) {θ1 θ2 : Δ} (δ : θ1 == θ2) (M1 : A θ1) (M2 : A θ2) → Type 
    PathOver' A δ M1 M2 = transport A δ M1 == M2

    hid : {Δ : Type} (A : Δ → Type) {θ1 : Δ} (M1 : A θ1) → PathOver' A id M1 M1
    hid A M1 = id

    elim : {Δ : Type} (A : Δ → Type) {θ1 : Δ} 
         → (C : (θ2 : Δ) (δ : θ1 == θ2) {M1 : A θ1} (M2 : A θ2) → PathOver' A δ M1 M2 → Type)
         → ({M1 : A θ1} → C θ1 id M1 (hid A M1))
         → (θ2 : Δ) (δ : θ1 == θ2) {M1 : A θ1} (M2 : A θ2) (α : PathOver' A δ M1 M2) → C θ2 δ M2 α 
    elim A {θ1} C b .θ1 id {M1} .M1 id = b

    β   : {Δ : Type} (A : Δ → Type) {θ1 : Δ}
         → (C : (θ2 : Δ) (δ : θ1 == θ2)  {M1 : A θ1} (M2 : A θ2) → PathOver' A δ M1 M2 → Type)
         → (b : ∀ {M1} → C θ1 id M1 id)
         →  {M1 : A θ1} → (elim A C b θ1 id M1 (hid A M1)) == b
    β A C b = id
  
  data PathOver {Δ : Type} (A : Δ → Type) : {θ1 θ2 : Δ} (δ : θ1 == θ2) (M1 : A θ1) (M2 : A θ2) → Type where
    id : ∀ {θ1} {M1 : A θ1} → PathOver A id M1 M1

  changeover= : {Δ : Type} (A : Δ → Type) {θ1 θ2 : Δ} {δ δ' : θ1 == θ2} (_ : δ == δ') {M1 : A θ1} {M2 : A θ2} → 
               PathOver A δ M1 M2
              == PathOver A δ' M1 M2
  changeover= A id = id

  changeover : {Δ : Type} (A : Δ → Type) {θ1 θ2 : Δ} {δ δ' : θ1 == θ2} (_ : δ == δ') {M1 : A θ1} {M2 : A θ2} → 
               PathOver A δ M1 M2
             → PathOver A δ' M1 M2
  changeover A α = coe (changeover= A α)


  _∘o_ : {Δ : Type} {A : Δ → Type} {θ1 θ2 θ3 : Δ} {δ2 : θ2 == θ3} {δ1 : θ1 == θ2} {M1 : A θ1} {M2 : A θ2} {M3 : A θ3}
       → PathOver A δ2 M2 M3 
       → PathOver A δ1 M1 M2
       → PathOver A (δ2 ∘ δ1) M1 M3
  p ∘o id = p

  infixr 10 _∘o_

  !o : {Δ : Type} {A : Δ → Type} {θ1 θ2 : Δ} {δ : θ1 == θ2} {M1 : A θ1} {M2 : A θ2} 
       → PathOver A δ M1 M2 
       → PathOver A (! δ) M2 M1
  !o id = id

  ∘o-unit-l : {Δ : Type} {A : Δ → Type} {θ1 θ2 : Δ} {δ1 : θ1 == θ2} {M1 : A θ1} {M2 : A θ2} 
            → (p : PathOver A δ1 M1 M2)
            → (id ∘o p) == changeover A (! (∘-unit-l δ1)) p
  ∘o-unit-l id = id


  apdo : {Δ : Type} {A : Δ → Type} (f : (θ : _) → A θ) {θ1 θ2 : Δ} (δ : θ1 == θ2) → PathOver A δ (f θ1) (f θ2)
  apdo f id = id


  pair= : {Δ : Type} {A : Δ → Type} {θ1 θ2 : Δ} (δ : θ1 == θ2) {M1 : A θ1} {M2 : A θ2} → PathOver A δ M1 M2 → (θ1 , M1) == (θ2 , M2)
  pair= .id id = id

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

  ido-constant : {Δ : Type} {A : Type} {θ1 θ2 : Δ} {M : A} (δ : θ1 == θ2) → PathOver (\ _ -> A) δ M M
  ido-constant id = id

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

  PathOver-transport-right' : {Δ : Type} (A : Δ → Type) {θ1 θ2 : Δ} (δ : θ1 == θ2) {M1 : A θ1} {M1' : A θ1} → M1 == M1'
                           → PathOver A δ M1 (transport A δ M1')
  PathOver-transport-right' A id id = id

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

  path-induction-homo-i : {Δ : Type} {A : Δ → Type} {θ1 : Δ} {M : A θ1} 
                       (C : {x : A θ1} → PathOver A (id{_}{θ1}) M x → Type)
                     → (C {M} id)
                     → {N : A θ1} → (P : PathOver A id M N) → C {N} P
  path-induction-homo-i C b α = path-induction-homo (\ _ → C) b α

  path-induction-homo-e : {Δ : Type} {A : Δ → Type} {θ1 : Δ} {M : A θ1} 
                       (C : (x : A θ1) → PathOver A (id{_}{θ1}) M x → Type)
                     → (C M id)
                     → (N : A θ1) → (P : PathOver A id M N) → C N P
  path-induction-homo-e C b _ α = path-induction-homo C b α

  path-induction-homo-e-eqv : {Δ : Type} {A : Δ → Type} {θ1 : Δ} {M : A θ1} 
                       (C : (x : A θ1) → PathOver A (id{_}{θ1}) M x → Type)
                     → Equiv (C M id) ((N : A θ1) → (P : PathOver A id M N) → C N P)
  path-induction-homo-e-eqv C = improve (hequiv (path-induction-homo-e C) 
                                                (λ f → f _ id) 
                                                (λ _ → id) 
                                                (λ f → λ≃ (λ N → λ≃ (λ α → path-induction-homo-e
                                                                             (λ N₁ α₁ → Path (path-induction-homo-e C (f _ id) N₁ α₁) (f N₁ α₁))
                                                                             id N α))))

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

  out-PathOver-constant : {Δ : Type} {A : Type} {θ1 θ2 : Δ} {δ : θ1 == θ2} {M1 : A} {M2 : A} 
                        → PathOver (\ _ -> A) δ M1 M2
                        → M1 == M2
  out-PathOver-constant id = id

  in-PathOver-constant : {Δ : Type} {A : Type} {θ1 θ2 : Δ} {δ : θ1 == θ2} {M1 : A} {M2 : A} 
                         → M1 == M2
                         → PathOver (\ _ -> A) δ M1 M2
  in-PathOver-constant {δ = id} id = id

  PathOver-constant-eqv-in-out : {Δ : Type} {A : Type} {θ1 θ2 : Δ} {δ : θ1 == θ2} {M1 : A} {M2 : A} 
                                 (α : M1 == M2) →
                                 (out-PathOver-constant {δ = δ} (in-PathOver-constant α)) == α
  PathOver-constant-eqv-in-out {δ = id} id = id

  PathOver-constant-eqv-out-in : {Δ : Type} {A : Type} {θ1 θ2 : Δ} {δ : θ1 == θ2} {M1 : A} {M2 : A} 
                                 (α : PathOver (\ _ -> A) δ M1 M2) →
                                 (in-PathOver-constant {δ = δ} (out-PathOver-constant α)) == α
  PathOver-constant-eqv-out-in id = id

  PathOver-constant-eqv : {Δ : Type} {A : Type} {θ1 θ2 : Δ} {δ : θ1 == θ2} {M1 : A} {M2 : A} 
                        →
                        Equiv (PathOver (\ _ -> A) δ M1 M2)
                              (M1 == M2)
  PathOver-constant-eqv = improve (hequiv out-PathOver-constant in-PathOver-constant PathOver-constant-eqv-out-in PathOver-constant-eqv-in-out) 

  over-to-hom/left : {Δ : Type} {A : Δ → Type}
            → ∀ {θ1 θ2} {δ : θ1 == θ2} → ∀ {M1 M2} 
            →  (PathOver A δ M1 M2)
            → ((transport A δ M1) == M2) 
  over-to-hom/left id = id

  hom-to-over/left : {Δ : Type} {A : Δ → Type}
            → ∀ {θ1 θ2} (δ : θ1 == θ2) → ∀ {M1 M2} 
            → ((transport A δ M1) == M2) 
            → (PathOver A δ M1 M2)
  hom-to-over/left id id = id

  hom-to-over-to-hom/left : {Δ : Type} {A : Δ → Type}
            → ∀ {θ1 θ2} (δ : θ1 == θ2) → ∀ {M1 M2} 
            → ( p : ((transport A δ M1) == M2) )
            → over-to-hom/left (hom-to-over/left δ p) == p
  hom-to-over-to-hom/left id id = id

  over-to-hom-to-over/left : {Δ : Type} {A : Δ → Type}
            → ∀ {θ1 θ2} {δ : θ1 == θ2} → ∀ {M1 M2} 
            → (p : PathOver A δ M1 M2)
            → hom-to-over/left δ (over-to-hom/left p) == p
  over-to-hom-to-over/left id = id

  hom-to-over/left-eqv : {Δ : Type} {A : Δ → Type}
            → ∀ {θ1 θ2} {δ : θ1 == θ2} → ∀ {M1 M2} 
            → Equiv((transport A δ M1) == M2) 
               (PathOver A δ M1 M2)
  hom-to-over/left-eqv {δ = δ} = improve
                                  (hequiv (hom-to-over/left δ) over-to-hom/left
                                   (hom-to-over-to-hom/left δ) over-to-hom-to-over/left)

  over-to-hom/right : {Δ : Type} {A : Δ → Type}
            → ∀ {θ1 θ2} {δ : θ1 == θ2} → ∀ {M1 M2} 
            →  (PathOver A δ M1 M2)
            → (M1 == (transport A (! δ) M2))
  over-to-hom/right id = id

  hom-to-over/right : {Δ : Type} {A : Δ → Type}
            → ∀ {θ1 θ2} (δ : θ1 == θ2) → ∀ {M1 M2} 
            → (M1 == (transport A (! δ) M2))
            → (PathOver A δ M1 M2)
  hom-to-over/right id id = id

  over-to-hom : {Δ : Type} {A : Δ → Type}
            → ∀ {θ1} → ∀ {M1 M2 : A θ1} 
            →  (δ : PathOver A id M1 M2)
            → (M1 == M2) 
  over-to-hom = over-to-hom/left 

  hom-to-over : {Δ : Type} {A : Δ → Type}
            → ∀ {θ1} → ∀ {M1 M2 : A θ1} 
            → (M1 == M2) 
            → (PathOver A id M1 M2)
  hom-to-over = hom-to-over/left id

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

  over-ap-o-ap : {Γ Δ : Type} (A : Δ → Type) {θ1 : Γ → Δ} 
               {θ1' θ2' : _} {δ' : θ1' == θ2'}  → ∀ {M1 M2}
             (p : PathOver A (ap θ1 δ') M1 M2)
             → over-o-ap A (over-ap-o A p) == p
  over-ap-o-ap A {θ1 = θ1} {δ' = id} {M1 = M1} α = path-induction-homo
                                                     (λ M2 α₁ →
                                                        Id
                                                        (over-o-ap A
                                                         (path-induction-homo''
                                                          (λ x p → PathOver (λ x₁ → A (θ1 x₁)) id M1 x) id α₁))
                                                        α₁)
                                                     id α

  over-o-ap-o : {Γ Δ : Type} (A : Δ → Type) {θ1 : Γ → Δ} 
               {θ1' θ2' : _} {δ' : θ1' == θ2'}  → ∀ {M1 M2}
             (p : PathOver (A o θ1) δ' M1 M2)
             → over-ap-o A (over-o-ap A p) == p
  over-o-ap-o A id = id

  over-o-ap-eqv : {Γ Δ : Type} (A : Δ → Type) {θ1 : Γ → Δ} 
               {θ1' θ2' : _} {δ' : θ1' == θ2'}  → ∀ {M1 M2} →
             Equiv (PathOver (A o θ1) δ' M1 M2) (PathOver A (ap θ1 δ') M1 M2)
  over-o-ap-eqv A = improve (hequiv (over-o-ap A) (over-ap-o A) (over-o-ap-o A) (over-ap-o-ap A))

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

  out-PathOverΠ : {Δ : Type} {A : Δ → Type} {B : Σ A → Type}
              → {θ1 θ2 : Δ} {δ : θ1 == θ2} {f : (x : A θ1) → B (θ1 , x)} {g : (x : A θ2) → B (θ2 , x)}
              →  PathOver (\ θ → (x : A θ) → B (θ , x)) δ f g 
              → ((x : A θ1) (y : A θ2) (α : PathOver A δ x y) → PathOver B (pair= δ α) (f x) (g y))
  out-PathOverΠ {B = B} {f = f} id x = path-induction-homo-e _ id

  in-PathOverΠ : {Δ : Type} {A : Δ → Type} {B : Σ A → Type}
                → {θ1 θ2 : Δ} {δ : θ1 == θ2} {f : (x : A θ1) → B (θ1 , x)} {g : (x : A θ2) → B (θ2 , x)}
                → ((x : A θ1) (y : A θ2) (α : PathOver A δ x y) → PathOver B (pair= δ α) (f x) (g y))
                →  PathOver (\ θ → (x : A θ) → B (θ , x)) δ f g 
  in-PathOverΠ {δ = id} h = hom-to-over (λ≃ (λ x → over-to-hom (h x x id)))

  PathOverΠ-out-in : {Δ : Type} {A : Δ → Type} {B : Σ A → Type}
                   → {θ1 θ2 : Δ} {δ : θ1 == θ2} {f : (x : A θ1) → B (θ1 , x)} {g : (x : A θ2) → B (θ2 , x)}
                   → (p :  PathOver (\ θ → (x : A θ) → B (θ , x)) δ f g )
                   → in-PathOverΠ (out-PathOverΠ p) == p
  PathOverΠ-out-in id = ap hom-to-over (! (Π≃η id))

  PathOverΠ-in-out : {Δ : Type} {A : Δ → Type} {B : Σ A → Type}
                → {θ1 θ2 : Δ} {δ : θ1 == θ2} {f : (x : A θ1) → B (θ1 , x)} {g : (x : A θ2) → B (θ2 , x)}
                → (h : (x : A θ1) (y : A θ2) (α : PathOver A δ x y) → PathOver B (pair= δ α) (f x) (g y))
                → out-PathOverΠ (in-PathOverΠ h) == h
  PathOverΠ-in-out { A = A} {B} {θ1 = θ1} {δ = id} h = λ≃ (λ x → λ≃ (λ y → λ≃ (λ α → path-induction-homo-e
                                                                (λ y₁ α₁ →
                                                                   Path
                                                                   (out-PathOverΠ (hom-to-over (λ≃ (λ x₁ → over-to-hom (h x₁ x₁ id))))
                                                                    x y₁ α₁)
                                                                   (h x y₁ α₁))
                                                                ((over-to-hom-to-over/left (h x x id) ∘ ap hom-to-over (Π≃β (λ x₁ → over-to-hom (h x₁ x₁ id)))) ∘ coh (λ≃ (λ x₁ → over-to-hom (h x₁ x₁ id)))) y α))) where
                   coh : ∀ {f g : (x : A θ1) → B (θ1 , x) } {x : A θ1} (α : f == g) →  
                       (out-PathOverΠ {_}{A}{B}{θ1}{θ1} {δ = id} (hom-to-over/left id α) x x id)
                       == hom-to-over (ap≃ α {x})
                   coh id = id

  PathOverΠ-eqv : {Δ : Type} {A : Δ → Type} {B : Σ A → Type}
              → {θ1 θ2 : Δ} {δ : θ1 == θ2} {f : (x : A θ1) → B (θ1 , x)} {g : (x : A θ2) → B (θ2 , x)}
              → Equiv (PathOver (\ θ → (x : A θ) → B (θ , x)) δ f g)
                      (((x : A θ1) (y : A θ2) (α : PathOver A δ x y) → PathOver B (pair= δ α) (f x) (g y)))
  PathOverΠ-eqv = improve (hequiv out-PathOverΠ in-PathOverΠ PathOverΠ-out-in PathOverΠ-in-out) 

  PathOverΠ : {Δ : Type} {A : Δ → Type} {B : Σ A → Type}
              → {θ1 θ2 : Δ} {δ : θ1 == θ2} {f : (x : A θ1) → B (θ1 , x)} {g : (x : A θ2) → B (θ2 , x)}
              →  PathOver (\ θ → (x : A θ) → B (θ , x)) δ f g 
              == ((x : A θ1) (y : A θ2) (α : PathOver A δ x y) → PathOver B (pair= δ α) (f x) (g y))
  PathOverΠ = ua PathOverΠ-eqv

  PathOverΠ-NDdomain : {Δ : Type} {A : Type} {B : Δ → A → Type}
              → {θ1 θ2 : Δ} {δ : θ1 == θ2} {f : (x : A) → B θ1 x} {g : (x : A) → B θ2 x}
              →  PathOver (\ θ → (x : A) → B θ x) δ f g 
              == ( (x : A) → PathOver (\ θ → B θ x) δ (f x) (g x))
  PathOverΠ-NDdomain {A = A} {B = B}{δ = id} {f}{g} = 
    apΠ id (λ≃ (λ x → ua (hom-to-over/left-eqv ∘equiv !equiv (hom-to-over/left-eqv {δ = id})) ∘ ua (!equiv (path-induction-homo-e-eqv (λ y α → PathOver (λ z → B (fst z) (snd z)) (pair= id α) (f x) (g y)))))) ∘ PathOverΠ

  PathOverΠ-NDrange : {Δ : Type} {A : Δ → Type} {B : Type}
              → {θ1 θ2 : Δ} {δ : θ1 == θ2} {f : (x : A θ1) → B} {g : (x : A θ2) → B }
              →  PathOver (\ θ → (x : A θ) → B) δ f g 
              == ((x : A θ1) (y : A θ2) (α : PathOver A δ x y) → Path (f x) (g y))
  PathOverΠ-NDrange = apΠ id (λ≃ (λ x → apΠ id (λ≃ (λ y → apΠ id (λ≃ (λ z → ua PathOver-constant-eqv)))))) ∘ PathOverΠ

  PathOverΠ-id : {Δ : Type} {A : Δ → Type} {B : Σ A → Type}
                 → {θ1 : Δ} (f : (x : A θ1) → B (θ1 , x)) {x : _}
                 → coe (PathOverΠ {A = A} {B = B}{δ = id} {f = f}) id x x id == id
  PathOverΠ-id f {x = x} = ap≃ (ap≃ (ap≃ (ap≃ (type≃β PathOverΠ-eqv) {id}) {x}) {x}) {id}

  postulate -- needed for Blakers-Massey type-theoretic
     ap-uncurryd-NDrange : {A : Type} {B : A → Type} {C : Type}
                   (f : (x : A) → B x → C) {a0 a1 : A} {b0 : B a0} {b1 : B a1} (α : a0 == a1) (β : PathOver B α b0 b1)
                   → ap (uncurryd f) (pair= α β) == coe PathOverΠ-NDrange (apdo f α) _ _ β 
     -- ap-uncurryd-NDrange _ .id id = {!!}

{-
    in-PathOverΠ/1l : {Δ : Type} {A : Δ → Type} {B : Σ A → Type}
                    → {θ1 θ2 : Δ} {δ : θ1 == θ2} {f : (x : A θ1) → B (θ1 , x)} {g : (x : A θ2) → B (θ2 , x)}
                    → ((x : A θ1) → PathOver B (pair= δ (PathOver-transport-right A δ)) (f x) (g (transport A δ x)))
                    →  PathOver (\ θ → (x : A θ) → B (θ , x)) δ f g 
-}

  PathOverType : {Δ : Type} {A B : Type}
              → {θ1 θ2 : Δ} {δ : θ1 == θ2}
              → PathOver (\ θ → Type) δ A B == Equiv A B 
  PathOverType = ua ((coe-equiv , univalence) ∘equiv PathOver-constant-eqv)

  PathOverType-id : {Δ : Type} {θ : Δ} {A : Type} → coe (PathOverType{_}{_}{_}{θ}) id == (id-equiv{A})
  PathOverType-id = ap≃
                      (type≃β ((coe-equiv , univalence) ∘equiv PathOver-constant-eqv))
                      {id}

  PathOverType-!  : {Δ : Type} {θ1 θ2 : Δ} {δ : θ1 == θ2} {A B : Type} {α : PathOver (\ _ -> Type) δ A B}
                    → coe PathOverType (!o α) == (!equiv (coe PathOverType α))
  PathOverType-! {δ = id} {α = α} = path-induction-homo
                                      (λ _ α₁ → coe PathOverType (!o α₁) == !equiv (coe PathOverType α₁))
                                      (! (ap !equiv PathOverType-id) ∘ PathOverType-id) α

  PathOverType-∘ : {Δ : Type} {A B C : Type}
              → {θ1 θ2 θ3 : Δ} {δ2 : θ2 == θ3} {δ1 : θ1 == θ2}
              → (α2 : PathOver (\ θ → Type) δ2 B C) (α1 : PathOver (\ θ → Type) δ1 A B) 
              → (coe PathOverType α2) ∘equiv (coe PathOverType α1) == coe PathOverType (α2 ∘o α1)
  PathOverType-∘ id id = (! PathOverType-id ∘ pair≃ id (HProp-unique (IsEquiv-HProp (λ x → x)) _ _)) ∘ ap2 _∘equiv_ PathOverType-id PathOverType-id

  PathOverType-changeover : {Δ : Type} {θ1 θ2 : Δ} {δ δ' : θ1 == θ2} (eq : δ == δ') {M1 : _} {M2 : _} → 
               (α : PathOver (\ _ -> Type) δ M1 M2)
             → coe PathOverType α == coe PathOverType (changeover (\ _ -> Type) eq α)
  PathOverType-changeover id α = id
    



  transport-Πo : ∀ {Γ} (A : Γ -> Set) (B : (γ : Γ) -> A γ -> Set)
            {θ1 θ2 : Γ} (δ : θ1 == θ2) (f : (x : A θ1) -> B θ1 x) 
         -> transport (\ γ -> (x : A γ) -> B γ x) δ f ==
            (\ x -> transport (\ (p : Σ \ (γ : Γ) -> A γ) -> B (fst p) (snd p))
                          (pair= δ (PathOver-transport-left A δ))
                          (f (transport A (! δ) x)))
  transport-Πo _ _ id f = id

  path-to-pathover : {Δ : Type} (A : Δ → Type) {θ : Δ} {M N : A θ} → M == N → PathOver A id M N
  path-to-pathover A id = id

{-
  apdo-split-def :{Δ : Type} {C : Δ → Unit⁺ → Type} 
               (f : (θ : Δ) → C θ <>⁺)
               (M : Δ → Unit⁺)
               {θ1 θ2 : Δ} (δ : θ1 == θ2) 
               (x y : Unit⁺) (α : PathOver (λ _ → Unit⁺) δ x y) →
               PathOver (λ z → C (fst z) (snd z)) (pair= δ α)
                        (split1⁺ (C θ1) (f θ1) x)
                        (split1⁺ (C θ2) (f θ2) y)
  apdo-split-def {C = C} f M δ = split1⁺ _ (split1⁺ _ (λ α → changeover (λ p → C (fst p) (snd p)) ?  -- need UIP for Unit⁺ and some massaging
                                                                (over-o-ap (λ p → C (fst p) (snd p)) {θ1 = λ θ → θ , <>⁺}
                                                                 (apdo f δ))))
  
  apdo-split : {Δ : Type} {C : Δ → Unit⁺ → Type} 
               (f : (θ : Δ) → C θ <>⁺)
               (M : Δ → Unit⁺)
               {θ1 θ2 : Δ} (δ : θ1 == θ2) 
               → coe PathOverΠ (apdo (\ θ → split1⁺ (\ x → (C θ x)) (f θ)) δ) ==
                 (\ x y α → apdo-split-def {C = C} f M δ x y α) 
    -- apdo-split f M id = λ≃ (split1⁺ _ (λ≃ (split1⁺ _ (λ≃ (λ α → {!!})))))
-}             
  
  apdo-apd : {Δ : Type} {A : Δ → Type} (f : (θ : _) → A θ) {θ1 θ2 : Δ} (δ : θ1 == θ2) 
           → apdo f δ == hom-to-over/left δ (apd f δ)
  apdo-apd f id = id

  ap-bifunctor-pair= : {A C : Type} {B : A → Type} (f : (x : A) → B x → C) → 
              {a00 a01 : A} 
              (la : a00 == a01)
              → ∀ {b00 b01} →  
              (lb : PathOver B la b00 b01)
              → ap (\ {(x , y) → f x y}) (pair= la lb) ==
                out-PathOver-constant (oute PathOverΠ-eqv (apdo f la) b00 b01 lb)
  ap-bifunctor-pair= f .id id = id
  

  {-
    PathOverΣ-eqv : {Δ : Type} {A : Δ → Type} {B : Σ A → Type}
                    → {θ1 θ2 : Δ} {δ : θ1 == θ2} {p : Σ \ (x : A θ1) → B (θ1 , x)} {q : Σ \ (x : A θ2) → B (θ2 , x)}
                    → Equiv (PathOver (\ θ → Σ \ (x : A θ) → B (θ , x)) δ p q)
                             ((Σ \ (α : PathOver A δ (fst p) (fst q)) → PathOver B (pair= δ α) (snd p) (snd q)))
  -}

  pair=o : {Δ : Type} {A : Δ → Type} {B : Σ A → Type}
         → {θ1 θ2 : Δ} {δ : θ1 == θ2} {p : Σ \ (x : A θ1) → B (θ1 , x)} {q : Σ \ (x : A θ2) → B (θ2 , x)}
         → (α : PathOver A δ (fst p) (fst q)) 
         → PathOver B (pair= δ α) (snd p) (snd q)
         → (PathOver (\ θ → Σ \ (x : A θ) → B (θ , x)) δ p q)
  pair=o {B = B} {p = p1 , p2} {.p1 , q2} id β = path-induction-homo (λ q3 _ → PathOver (λ θ → Σ (λ x → B (θ , x))) id (p1 , p2) (p1 , q3)) id β

{-
  fst=o : {Δ : Type} {A : Δ → Type} {B : Σ A → Type}
         → {θ1 θ2 : Δ} {δ : θ1 == θ2} {p : Σ \ (x : A θ1) → B (θ1 , x)} {q : Σ \ (x : A θ2) → B (θ2 , x)}
         → (PathOver (\ θ → Σ \ (x : A θ) → B (θ , x)) δ p q)
         → (PathOver A δ (fst p) (fst q)) 
  fst=o x = fst (fst PathOverΣ-eqv x)

  snd=o : {Δ : Type} {A : Δ → Type} {B : Σ A → Type}
         → {θ1 θ2 : Δ} {δ : θ1 == θ2} {p : Σ \ (x : A θ1) → B (θ1 , x)} {q : Σ \ (x : A θ2) → B (θ2 , x)}
         → (α : PathOver (\ θ → Σ \ (x : A θ) → B (θ , x)) δ p q)
         → PathOver B (pair= δ (fst=o α)) (snd p) (snd q)
  snd=o x = snd (fst PathOverΣ-eqv x)
-}

  ap-nt-over :
    ∀ {A} {B C : A → Type} {a0 a1 : A} {b0 : B a0} {b1 : B a1}
      {p : a0 == a1} 
    → (f : {x : A} → B x → C x)
    → PathOver B p b0 b1
    → PathOver C p (f b0) (f b1)
  ap-nt-over f id = id

  transport-Path-do : {Γ : Type} {A : Γ -> Type} (f g : (x : Γ) -> A x) {M N : Γ} (p : Path M N)
            -> (p' : f M ≃ g M) 
            -> Path (transport (λ x → Path (f x) (g x)) p p')
                    (over-to-hom (changeover A (!-inv-r p ∘ ap (λ x → p ∘ x) (∘-unit-l (! p))) (apdo g p ∘o hom-to-over p' ∘o !o (apdo f p))))
  transport-Path-do _ _ id p' = ! (ap over-to-hom/left (∘o-unit-l (hom-to-over p'))) ∘ ! (hom-to-over-to-hom/left id p')

  apdo-o : {Γ Δ : Type} {A : Δ → Type} (f : (θ : _) → A θ) (h : Γ → Δ) → {θ1 θ2 : Γ} (δ : θ1 == θ2) 
       → apdo (\ x → f(h x)) δ == over-ap-o _ (apdo f (ap h δ))
  apdo-o f h id = id

  Σ=β2-ND : {A B : Type} {p q : A × B} 
            (α : Path (fst p) (fst q)) 
            (β : Path (snd p) (snd q))
            -> Path (ap snd (pair= α (in-PathOver-constant β))) β
  Σ=β2-ND {p = x , y} {q = .x , .y} id id = id

