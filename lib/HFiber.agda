
{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.NType
open import lib.Sums
open import lib.Prods
open import lib.Paths
open import lib.NType
open import lib.cubical.PathOver

module lib.HFiber where

  -- easy because of η for Unit
  HFiber-of-map-to-point : ∀ {A} {y : Unit} → Equiv (HFiber (\ (_ : A) → <>) y) A
  HFiber-of-map-to-point = improve (hequiv fst (λ x → x , id) (λ x → ap (λ y → fst x , y) (HSet-UIP (raise-level (Inl (-2< _)) (ntype Contractible-Unit)) _ _ _ _)) (λ _ → id))

  HFiber-of-map-from-point : ∀ {A} {a b : A} → Equiv (HFiber (\ (_ : Unit) → a) b) (a == b)
  HFiber-of-map-from-point = improve (hequiv snd (λ p → _ , p) (λ _ → id) (λ _ → id))

  transport-HFiber-arg : {A B : Type} -> (f : A -> B) -> {b1 b2 : B}
                             (β : b1 ≃ b2)
                           -> transport (HFiber f) β ≃ \ p → (fst p , β ∘ snd p)
  transport-HFiber-arg f id = λ≃ \ p -> pair≃ id (! (∘-unit-l (snd p)))

  
  hfiber-fst-eqv : ∀ {A} {B : A → Type} (a : A) → Equiv (B a) (HFiber fst a)
  hfiber-fst-eqv {B = B} a = (improve (hequiv (λ b → (a , b) , id) (λ p₁ → transport B (snd p₁) (snd (fst p₁))) (λ _ → id) (λ {((a1 , b) , p) → path-induction-l (λ a2 p₁ → (b₁ : B a2) → Id ((a , transport B p₁ b₁) , id) ((a2 , b₁) , p₁)) (λ _ → id) p b})))

  hfiber-fst : ∀ {A} {B : A → Type} (a : A) → (B a) == (HFiber {Σ B} fst a)
  hfiber-fst {B = B} a = ua (hfiber-fst-eqv a)

  HFiber-fiberwise-to-total-eqv : {A : Type} {B C : A → Type} (f : (x : A) → B x → C x)
                                → {a : A} {c : C a} → Equiv (HFiber (f a) c) (HFiber (fiberwise-to-total f) (a , c))
  HFiber-fiberwise-to-total-eqv {A}{B}{C} f {a}{c} = 
    improve (hequiv mapl
                    mapr
                    (λ x → path-induction (λ c' sndx → Path (mapr (mapl (fst x , sndx))) (fst x , sndx)) 
                           id 
                           (snd x))
                    (λ y → comp2 y)) where
    mapl : ∀ {a} {c : C a} → (HFiber (f a) c) → (HFiber (fiberwise-to-total f) (a , c))
    mapl {a}{c} = (λ p → (a , fst p) , pair= id (hom-to-over (snd p)))

    mapr : ∀ {a} {c : C a} →  (HFiber (fiberwise-to-total f) (a , c)) → (HFiber (f a) c)
    mapr = (λ p → transport B (ap fst (snd p)) (snd (fst p)) ,
                   (over-to-hom/left (over-o-ap C (apdo snd (snd p))) ∘
                   ap (λ Z₁ → transport C Z₁ (f (fst (fst p)) (snd (fst p)))) (Σ=β1 (ap (λ r → fst r) (snd p)) (PathOver-transport-right (λ z → B z) (ap (λ r → fst r) (snd p))))) ∘ 
                   ! (over-to-hom/left (over-o-ap C (out-PathOverΠ (apdo f (ap fst (snd p))) (snd (fst p)) _ (PathOver-transport-right _ _)))))
    
    comp2 : ∀ {ac} (y : HFiber (fiberwise-to-total f) ac) → Path (mapl (mapr y)) y
    comp2 (p , id) = id

  
