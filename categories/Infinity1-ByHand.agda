{-# OPTIONS --type-in-type --new-without-K #-}

open import lib.Prelude

module categories.Infinity1-ByHand where
  
  postulate 
    parametricity : {A B : Type} (f : (X : Type) → (B → X) → (A → X)) 
                  → (X : _) (k : B → X) → f X k == \ a -> k (f B (\ x -> x) a)

    parametricity-comp : {A B : Type} (f : (X : Type) → (B → X) → (A → X)) 
                       → parametricity f B (\ x -> x) == id 

  -- postulate Π≃β2 : {A : Type} {B : A → Type} {C : (a : A) → B a → Type}
  --                (f : (x : A) → (b : B a) → C a b)
  --                → ap f  

  data Glob (A B : Type) : Type
  T : {A B : Type} → Glob A B -> Type

  data Glob A B where
    *   : Glob A B
    Hom : (G : Glob A B) -> T G -> T G -> Glob A B

  T {A}{B} (*) = (X : Type) → (B → X) → A → X
  T (Hom G M N) = Path {T G} M N

  Inst : {A B : Type} → Glob A B → Type 
  inst : {A B : Type} → (G : Glob A B) → T G → Inst G

  Inst {A}{B} * = A → B
  Inst {A}{B} (Hom G x y) = Path {Inst G} (inst G x) (inst G y)

  inst {A}{B} * f = f B (λ x → x)
  inst (Hom G x y) f = ap (inst G) f

  uninst : ∀ {A B} (G : Glob A B) → Inst G → T G
  inv : ∀ {A B} (G : Glob A B) → (x : _) → uninst G (inst G x) == x

  uninst * i X f a = f (i a)
  uninst (Hom G x y) i = inv G y ∘ ap (uninst G) i ∘ ! (inv G x)

  inv * f = λ≃ (λ X → λ≃ (λ k → ! (parametricity f X k)))
  inv (Hom G x .x) id = !-inv-r (inv G x) ∘ ∘-assoc (inv G x) id (! (inv G x))

  inv2 : ∀ {A B} (G : Glob A B) → (x : _) → inst G (uninst G x) == x
  triangle : ∀ {A B} (G : Glob A B) → (y : _) → ap (inst G) (inv G y) == (inv2 G (inst G y))

  inv2 * x = id
  inv2 (Hom G x y) p = ap (inst G) (inv G y ∘ ap (uninst G) p ∘ ! (inv G x)) ≃〈 {!!} 〉 
                       ap (inst G) (inv G y) ∘ ap (inst G) (ap (uninst G) p) ∘ ap (inst G) (! (inv G x)) ≃〈 {!!} 〉 
                       ap (inst G) (inv G y) ∘ ap (inst G o uninst G) p ∘ ap (inst G) (! (inv G x)) ≃〈 {!ap-by-equals (inv2 G)!} 〉 
                       ap (inst G) (inv G y) ∘ (! (inv2 G (inst G y)) ∘ ap (λ z → z) p ∘ inv2 G (inst G x)) ∘ ap (inst G) (! (inv G x)) ≃〈 {!!} 〉 
                       (p ∎)
  triangle * f = {!parametricity-comp f !} 
  triangle (Hom G x .x) id = {!!}
