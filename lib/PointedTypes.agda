{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Prods
open import lib.Int
open Int
open import lib.LoopSpace
open import lib.loopspace.Types
open import lib.AdjointEquiv

module lib.PointedTypes where

Type₊ : Type
Type₊ = Σ[ A ∶ Type ] A

∣_∣ : Type₊ → Type
∣_∣ = fst

bp : (A : Type₊) → ∣ A ∣
bp A = snd A

const-map : (A : Type₊) → (B : Type₊) → (∣ A ∣ → ∣ B ∣)
const-map A B = λ a → bp B

Map₊ : Type₊ → Type₊ → Type
Map₊ A B = Σ[ f ∶ (∣ A ∣ → ∣ B ∣) ] (f (bp A) ≃ (bp B))

_₊→_ : Type₊ → Type₊ → Type₊
A ₊→ B = Map₊ A B , const-map A B , id

Ω₀ : Type₊ → Type
Ω₀ (A , x) = Loop One A x

Ω : Type₊ → Type₊
Ω A = (Loop One (fst A) (snd A)) , id

Ω^ : Positive → Type₊ → Type₊
Ω^ n A = Loop n ∣ A ∣ (bp A) , id^ n

Ω-functor : {A B : Type₊} → (f : Map₊ A B) → Map₊ (Ω A) (Ω B)
Ω-functor f = (λ l → snd f ∘ ap (fst f) l ∘ ! (snd f)) , 
  !-inv-r (snd f) ∘ (ap (_∘_ (snd f)) (∘-unit-l (! (snd f) ∘ id)))

Ω^-functor : ∀ {n} → {A B : Type₊} → (f : Map₊ A B) → Map₊ (Ω^ n A) (Ω^ n B)
Ω^-functor {One} f = Ω-functor f
Ω^-functor {S n} f = Ω-functor (Ω^-functor{n} f)

Equiv₊ : Type₊ → Type₊ → Type
Equiv₊ A B = Σ[ f ∶ (Equiv ∣ A ∣ ∣ B ∣) ] (fst f (bp A)) ≃ (bp B)

!equiv₊ : ∀ {A B} → Equiv₊ A B → Equiv₊ B A
!equiv₊ {A} ((f , isequiv g α β γ) , p) =
  (!equiv (f , isequiv g α β γ)) , α (bp A) ∘ ! (ap g p)

_∘equiv₊_ : ∀ {A B C} → Equiv₊ B C → Equiv₊ A B → Equiv₊ A C
_∘equiv₊_ (f , p) (g , q) = f ∘equiv g , p ∘ ap (fst f) q

open LoopΠ 

temp : {A B : Type} → {n : Positive} → {f : A → B} → 
       Equiv (Loop n (A → B) f) ((x : A) → (Loop n B (f x)))
temp {A} {B} {n} {f} = !equiv (eqv {A} {λ a → B} {f} n)

temp2 : {A B : Type} → {n : Positive} → {y : B} →
        Equiv (Loop n (A → B) (λ a → y)) (A → Loop n B y)
temp2 {A} {B} {n} {y} = temp {A} {B} {n} {λ a → y}

temp3 : {A B : Type₊} → {n : Positive} → 
        Equiv (Loop n (Map₊ A B) (const-map A B , id)) (Loop n (fst A → fst B) (λ a → bp B))
temp3 {A} {B} {n} = {!!}

Ω-comm-limit : {A B : Type₊} → Equiv₊ (Ω (A ₊→ B)) (A ₊→ Ω B)
Ω-comm-limit {A} {B} = {!!}

lemma : {A B : Type} → {x : A} → (f : Equiv A B) → Equiv₊ (A , x) (B , fst f x)
lemma {A} {B} {x} f = f , id

lemma2 : {A B : Type₊} → (fst (Ω (A ₊→ B))) → (fst (A ₊→ Ω B))
lemma2 {A , x} {B , y} p = (λ a → ap≃ (fst≃ p) {a}) , {!!} ≃〈 {!!} 〉 snd≃ p

-- Without Σ-types, you can just prove the lemmas about the first loop space by hand.

 -- ∘-equiv-post : {A B C : Type} → Equiv B C → Equiv (A → B) (A → C)
 -- ∘-equiv-post (f , p) = 
 --   let open IsEquiv in 
 --   improve ((λ h → f o h) , 
 --   (ishequiv (λ k → (g p) o k) 
 --             (λ h → λ≃ (λ x → α p (h x))) 
 --             (λ k → λ≃ (λ y → β p (k y)))))

 -- ∘-equiv-pre : {A B C : Type} → Equiv A B → Equiv (B → C) (A → C)
 -- ∘-equiv-pre (f , p) = 
 --   let open IsEquiv in
 --   improve ((λ h → h o f) , 
 --   (ishequiv (λ k → k o (g p)) 
 --             (λ h → λ≃ (λ x → ap h (β p x))) 
 --             (λ k → λ≃ (λ x → ap k (α p x)))))

