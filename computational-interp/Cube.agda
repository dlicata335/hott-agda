{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open import lib.PathOver

module computational-interp.Cube where

  Paths : Type → Type
  Paths A = Σ \ (x : A) → Σ \ (y : A) → x == y

  Cube : Nat → Type → Type
  Cube 0 A = A
  Cube (S n) A = Paths (Cube n A) 

  face : {A : Type} (n : Nat) → List (Cube (S n) A → Cube n A)
  face 0 = fst :: (λ x → fst (snd x)) :: []
  face {A} (S n) = fst :: -- pick 0 for last dimension
                   (λ x → fst (snd x)) :: -- pick 1 for last dimension
                   ListM.map (λ fn → λ {(x , y , p) → fn x , fn y , ap fn p}) (face {A} n) -- edit a previous dimension

  degen : {A : Type} (n : Nat) → List (Cube n A → Cube (S n) A)
  degen 0 = (λ x → x , x , id) :: []
  degen {A} (S n) = (λ x → x , x , id) :: -- drop last dimension
                    ListM.map (λ dn → λ {(x , y , p) → dn x , dn y , ap dn p}) (degen {A} n) -- drop previous dimension

  contract-Paths : ∀ {A} → Paths A == A
  contract-Paths = ua (improve (hequiv fst (λ x → x , x , id) (λ {(x , y , p) → path-induction (λ y₁ p₁ → (x , x , id) == (x , y₁ , p₁)) id p}) (λ _ → id)))

  contract-cube : ∀ {A} → (n : Nat) → Cube n A == A
  contract-cube 0 = id
  contract-cube {A} (S n) = contract-cube n ∘ contract-Paths

  refl : (n : Nat) → ∀ {A} (a : A) → Cube n A
  refl n a = coe (! (contract-cube n)) a

  cube-induction : ∀ {A} (n : Nat) (P : Cube n A → Type) → ((a : A) → P (refl n a)) → (c : Cube n A) → P c
  cube-induction n P b c = transport P (ap≃ (transport-inv-1 (λ x → x) (contract-cube n))) (b (coe (contract-cube n) c))

  cube-induction-β : ∀ {A} (n : Nat) (P : Cube n A → Type) → (b : (a : A) → P (refl n a)) 
                   → (a : A) → cube-induction n P b (refl n a) == b a 
  cube-induction-β n P b a = {!!}

  ap-Cube : {A : Type} {B : Type} (n : Nat) (f : A → B) → Cube n A → Cube n B
  ap-Cube n f c = coe (! (contract-cube n)) (f (coe (contract-cube n) c))

  p : {A : Type} {B : A → Type} (n : Nat) → Cube n (Σ B) → Cube n A
  p n = ap-Cube n fst
{-
  -- better definitional behavior?
  p Z x = fst x
  p (S n) (x , y , α) = p n x , p n y , ap (p n) α
-}

  CubeOver : {A : Type} (B : A → Type) (n : Nat) → Cube n A → Type
  CubeOver B n c = HFiber (p {B = B} n) c

  CubeOver-expand : {A : Type} (B : A → Type) (n : Nat) (a : A) → CubeOver B n (refl n a) == B a
  CubeOver-expand B n a = {!!} ∘
                            apΣ
                            {B =
                             λ x →
                               Id
                               (transport (λ x₁ → x₁) (! (contract-cube n))
                                (fst (transport (λ x₁ → x₁) (contract-cube n) x)))
                               (transport (λ x₁ → x₁) (! (contract-cube n)) a)}
                            {B' = λ x →
                               Id
                               (transport (λ x₁ → x₁) (! (contract-cube n))
                                (fst x))
                               (transport (λ x₁ → x₁) (! (contract-cube n)) a)}
                            (contract-cube {Σ B} n) id

  reflo : ∀ n {A} {B : A → Type} {a : A} (b : B a) → CubeOver B n (refl n a)
  reflo n {B = B} {a} b = coe (! (CubeOver-expand B n a)) b

  cubeover-induction : ∀ n {A} {B} (a : A) 
                     → (P : CubeOver B n (refl n a) → Type) 
                     → (b : (b : B a) → P (reflo n b))
                     → (c : CubeOver B n (refl n a)) → P c
  cubeover-induction = {!!}

  apd-Cube : {A : Type} {B : A → Type} (n : Nat) (f : (x : A) → B x) → (a : Cube n A) → CubeOver B n a
  apd-Cube n f c = {!!}
                     

  ctxops : {A : Type} {B : A → Type} (n : Nat) 
         → Cube n (Σ B) == Σ (\ (a : Cube n A) → CubeOver B n a)
  ctxops {A} {B} n = apΣ {B = B} (! (contract-cube {A} n)) (λ≃ (λ x → ! (CubeOver-expand B n x))) ∘ contract-cube n

  ctxops-p : {A : Type} {B : A → Type} (n : Nat) 
         → fst o coe (ctxops {B = B} n) == p n 
  ctxops-p n = λ≃ (λ x → {!!})

  v : {A : Type} {B : A → Type} (n : Nat) → (c : Cube n (Σ B)) → CubeOver B n (p n c)
  v {A} {B} n c = transport (λ f → CubeOver B n (f c)) (ctxops-p {B = B} n) (snd (coe (ctxops n) c))

  pair : {A : Type} {B : A → Type} (n : Nat) → (a : Cube n A) (b : CubeOver B n a) → Cube n (Σ B)
  pair n a b = coe (! (ctxops n)) (a , b)

  sigma : {A : Type} {B1 : A → Type} {B2 : Σ B1 → Type} (n : Nat) → (a : Cube n A) 
     → (Σ \ (b1 : CubeOver B1 n a) → CubeOver B2 n (pair n a b1))
     == CubeOver (\ a -> Σ \ (b1 : B1 a) → B2 (a , b1)) n a 
  sigma 0 = {!!}
  sigma (S 0) = {!!}
  sigma _ = {!!}

  pi : {A : Type} {B1 : A → Type} {B2 : Σ B1 → Type} (n : Nat) → (a : Cube n A) 
     → ((b1 : CubeOver B1 n a) → CubeOver B2 n (pair n a b1))
     == CubeOver (\ a -> (b1 : B1 a) → B2 (a , b1)) n a 
  pi 0 = {!!}
  pi (S n) = {!!}

  exp : {A B : Type} (n : Nat) → Cube n (A → B) == (Cube n A → Cube n B)
  exp n = ! (ap2 (λ x y → x → y) (contract-cube n) (contract-cube n)) ∘
          contract-cube n
{-
  exp 0 = id
  exp {A} {B} (S n) = (! (ap2 (λ x y → x → y) (contract-Paths {Cube n A}) (contract-Paths {Cube n B})) ∘ contract-Paths {Cube n A → Cube n B}) ∘ ap Paths (exp n)
-}

  up : (n : Nat) {A : Type} {M N : A} → Cube n (M == N) → Cube (S n) A
  up Z {_}{M}{N} c = M , N , c
  up (S n) (c1 , c2 , p) = up n c1 , up n c2 , ap (up n) p

  module Test (A : Type) (B : A → Type) where
    Total0 = Σ B
    Total1 = Σ \ (x : Total0) → Σ (\ (y : Total0) → x == y)
    Total2 = Σ \ (x : Total1) → Σ (\ (y : Total1) → x == y)

    test : Total2 == Cube 2 (Σ B)
    test = id

    conjecture : {A : Type} {B : A → Type} (a1 a2 : A) (α : a1 == a2) 
             → HFiber (p {_}{B} 1) (a1 , a2 , α) == 
               Σ (λ (b1 : B a1) → Σ (λ (b2 : B a2) → PathOver B α b1 b2))
    conjecture a1 a2 α = ua (improve (hequiv (λ {(((a1' , b1) , (a2' , b2) , αβ) , eq) → {!(b1 , b2 , ?)!}})
                                           (λ {(b1 , b2 , β) → ((a1 , b1) , (a2 , b2) , pair= α β) , {!!}}) {!!} {!!}))

  test : {Γ : Type} {A : Γ → Type} {M N : (x : Γ) → A x} (θ : Γ) → Type
  test {Γ}{A}{M}{N} θ = CubeOver
                          (λ (p₁ : Σ (λ (θ₁ : Γ) → A θ₁ × A θ₁)) →
                             fst (snd p₁) == snd (snd p₁))
                          0 (θ , (M θ) , (N θ))
  
  up' : ∀ {n} {Γ : Type} {A : Γ → Type} {M N : (x : Γ) → A x} (θ : Cube n Γ) 
      → CubeOver (\ x -> M x == N x) n θ
      → CubeOver A (S n) (θ , θ , id) 
  up' {n} {M = M} {N = N} θ c = (pair n θ (apd-Cube n M θ) , (pair n θ (apd-Cube n M θ) , {!fst c!})) , {!!}

  CubeOver' : {A : Type} (B : A → Type) (n : Nat) → Cube n A → Type
  CubeOver' B Z a = B a
  CubeOver' B (S n) (a1 , a2 , α) = Σ (λ (x : CubeOver' B n a1) → 
                                   Σ (λ (y : CubeOver' B n a2) → 
                                        PathOver (CubeOver' B n) α x y))

  pair' : {A : Type} {B : A → Type} (n : Nat) → (Σ \ (a : Cube n A) →  CubeOver' B n a) → Cube n (Σ B)
  pair' Z p = p
  pair' (S n) ((a1 , a2 , α) , (b1 , b2 , β)) = pair' n (a1 , b1) , pair' n (a2 , b2) , ap (pair' n) (pair= α β)



  module Foo (A : Type) where

    Cube' : Nat → Type 
    Boundary : Nat → Type
    d : (n : Nat) → Cube' n → Boundary n
    Inside : (n : Nat) → Boundary (S n) → Type

    Boundary 0 = Unit
    Boundary (S n) = Σ λ (c1 : Cube' n) → Σ \ (c2 : Cube' n) → d n c1 == d n c2

    Cube' 0 = A
    Cube' (S n) = Σ \ (b : Boundary (S n)) → Inside n b

    d Z c = <>
    d (S n) c = fst c

    -- theorem
    Inside Z (c1 , c2 , b) = c1 == c2
    Inside (S n) ((.b2 , α1) , (b2 , α2) , id) = α1 == α2

    mutual
      expand : (n : Nat) → A → Cube' n 
      expand Z x = x
      expand (S n) x = (expand n x , expand n x , id) , expand-in n x
  
      expand-in : (n : Nat) → (x : A) → Inside n (expand n x , expand n x , id)
      expand-in Z x = id
      expand-in (S n) x = id

    pt : (n : Nat) → Cube' n → A
    pt Z c = c
    pt (S n) c = pt n (fst (fst c))

    pt-expand : (n : Nat) (c : Cube' n) → expand n (pt n c) == c
    pt-expand Z c = id
    pt-expand (S Z) ((.c2 , c2 , b) , id) = {!UIP for Unit!}
    pt-expand (S (S n)) (((.b2 , .i2) , (b2 , i2) , id) , id) = pair= (pair= (pt-expand (S n) (b2 , i2)) {!!}) {!!}  --grungy but should work 

    test' : _
    test' = {!Cube' 2!}


