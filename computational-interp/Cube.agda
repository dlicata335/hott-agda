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

  module Coprod (A : Type) (B : Type) where

    eqv : Paths' (Either A B) == Either (Paths' A) (Paths' B)
    eqv = ap2 Either (! (contract-Paths' {A})) (! (contract-Paths' {B}))  ∘ (contract-Paths' {Either A B})

    C : (x y : Either A B) → Type
    C (Inl a) (Inl a') = a == a'
    C (Inr b) (Inr b') = b == b'
    C _ _ = Void

    step : (a : A) → coe (! eqv) (Inl ((a , a) , id)) == ((Inl a , Inl a) , id)
    step = {!!}

    e' : (p : Either A B × Either A B) → Equiv (Σ \ (q : Paths' (Either A B)) → fst q == p) (C (fst p) (snd p))
    e' p = improve (hequiv l {!!} {!!} {!!}) where
      l : (Σ \ (q : Paths' (Either A B)) → fst q == p) → _
      l = {!!}

    e : (p : Either A B × Either A B) → Equiv (Σ \ (q : Either (Paths' A) (Paths' B)) → fst (coe (! eqv) q) == p) (C (fst p) (snd p)) 
    e p = improve (hequiv l (r p) {!!} {!!}) where
      l : Σ (λ q → fst (coe (! eqv) q) == p) -> _
      l (Inl ((x , .x) , id) , eq) = path-induction (λ p₁ eq₁ → C (fst p₁) (snd p₁)) (transport (λ x₁ → C (fst (fst x₁)) (snd (fst x₁))) (! (step x)) id) eq
      l (Inr ((y , .y) , id) , eq) = {!!}

      r : (p : Either A B × Either A B) → (C (fst p) (snd p)) -> (Σ \ (q : Either (Paths' A) (Paths' B)) → fst (coe (! eqv) q) == p)
      r (Inl x , Inl y) c = (Inl ((x , y) , c)) , {!!}
      r (Inl x , Inr y) ()
      r (Inr x , Inl y) c = {!!}
      r (Inr x , Inr y) c = {!!}
{-
    C : (a a' : A) → Either (Paths' A) (Paths' B) → Type
    C a a' (Inl ((a1 , a1'), p)) = (a == a1) × (a' == a1')
    C a a' (Inr _) = Void 

    coprod2 : (a a' : A) (p : Paths' (Either A B)) → C a a' (coe eqv p) == (fst p == (Inl a , Inl a'))
    coprod2 a a' ((Inl x , .(Inl x)) , id) = {!!}
    coprod2 a a' ((Inr x , .(Inr x)) , id) = {!!}

    coprod3 : (a a' : A) (p : Either (Paths' A) (Paths' B)) → C a a' p == (fst (coe (! eqv) p) == (Inl a , Inl a'))
    coprod3 a a' (Inl ((x , .x) , id)) = (a == x) × (a' == x) ≃〈 {!!} 〉
                                         Path {(Either A B × Either A B)} (Inl x , Inl x) (Inl a , Inl a') ≃〈 {!!} 〉 
                                         (fst (coe (! eqv) (Inl ((x , x) , id))) == (Inl a , Inl a') ∎)
    coprod3 a a' (Inr ((x , .x) , id)) = {!!}
-}

{-


    fiberwise-eqv : {A : Type} {B B' : A → Type} → (f : (a : A) → B a → B' a)
                  → IsEquiv {(Σ B)} {(Σ B')} (fiberwise-to-total f) 
                  → (a : A) → B a == B' a
    fiberwise-eqv f (isequiv g α β _) a = ua (improve (hequiv (f a) (λ b' → coe {!!} (snd (g (a , b')))) {!!} {!!}))

    movearg : ∀ {A B} → Equiv (A → Paths' B) (Σ (λ (p₁ : (A → B) × (A → B)) → (x : A) → fst p₁ x == snd p₁ x)) 
    movearg = improve (hequiv ((λ f →
                                      ((\ x -> fst (fst (f x))) , (λ x₁ → snd (fst (f x₁)))) ,
                                      (λ x₁ → snd (f x₁))))
                               (λ x x₁ → ((fst (fst x) x₁) , (snd (fst x) x₁)) , (snd x x₁))
                               (λ _ → id) (λ _ → id))

    funext : {A B : Type} (f g : A → B) → (f == g) == ((x : A) → f x == g x)
    funext {A} {B} f g = fiberwise-eqv {A = (A → B) × (A → B)} {B = \ p → fst p == snd p} {B' = \ p → (x : A) → fst p x == snd p x}
                                       (λ {(f , g) → λ p₁ x → ap≃ p₁ {x}})
                                       STS
                                       (f , g) where
        tot : (Paths' (A → B)) → Σ (λ (p₁ : (A → B) × (A → B)) → (x : A) → fst p₁ x == snd p₁ x)
        tot = fiberwise-to-total {A = (A → B) × (A → B)} {B = \ p → fst p == snd p} {B' = \ p → (x : A) → fst p x == snd p x} (λ {(f , g) → λ p₁ x → ap≃ p₁ {x}})

        e : Equiv (Paths' (A → B)) (Σ (λ (p₁ : (A → B) × (A → B)) → (x : A) → fst p₁ x == snd p₁ x))
        e = movearg ∘equiv coe-equiv eqv

        STS : IsEquiv {Paths' (A → B)} {Σ (λ (p₁ : (A → B) × (A → B)) → (x : A) → fst p₁ x == snd p₁ x)} 
                      tot
        STS = transport IsEquiv (fst e ≃〈 {!!} 〉 
                                 fst movearg o coe eqv ≃〈 {!!} 〉 
                                 fst movearg o coe (! (ap (\ y -> A → y) (contract-Paths' {B}))) o coe (contract-Paths' {A → B}) ≃〈 {!!} 〉 
                                 fst movearg o coe (ap (\ y -> A → y) (! (contract-Paths' {B}))) o coe (contract-Paths' {A → B}) ≃〈 {!!} 〉 
                                 fst movearg o (\ z -> coe (! (contract-Paths' {B})) o z) o coe (contract-Paths' {A → B}) ≃〈 {!!} 〉 
                                 ((λ f →
                                      ((\ x -> fst (fst (f x))) , (λ x₁ → snd (fst (f x₁)))) ,
                                      (λ x₁ → snd (f x₁)))) o (\ z -> coe (! (contract-Paths' {B})) o z) o coe (contract-Paths' {A → B}) ≃〈 {!!} 〉 
                                 (\ p -> fst p , λ x → ap≃ (snd p) {x}) ≃〈 {!!} 〉 
                                 tot ∎)
                                (snd e) 
-}
