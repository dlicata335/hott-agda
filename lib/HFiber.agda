
{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.NType
open import lib.Sums
open import lib.Prods
open import lib.Paths
open import lib.NType
open import lib.AdjointEquiv
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

  in-HFiber : ∀ {A B} {f : A → B} (a : A) → HFiber f (f a)
  in-HFiber a = a , id

  -- FIXME rewrite using equiv-adjunction ?
  HFiber-at-equiv : ∀ {A B B'} (e : Equiv B B') (f : A → B') {b : B}
                  → Equiv (HFiber f (fst e b)) (HFiber (IsEquiv.g (snd e) o f) b)
  HFiber-at-equiv e f {b} = 
    improve (hequiv (λ p → (fst p) , IsEquiv.α (snd e) b ∘ ap (IsEquiv.g (snd e)) (snd p))
                    (λ p → (fst p) , (ap (fst e) (snd p) ∘ ! (IsEquiv.β (snd e) (f (fst p)))))
                    comp1
                    comp2) where
     abstract
       comp1 : (x : _) → Path (fst x , ap (fst e) (IsEquiv.α (snd e) b ∘ ap (IsEquiv.g (snd e)) (snd x)) ∘ ! (IsEquiv.β (snd e) (f (fst x)))) x
       comp1 = (λ hf → ap (λ Z₁ → fst hf , Z₁)
                          (ap (fst e) (IsEquiv.α (snd e) b ∘ ap (IsEquiv.g (snd e)) (snd hf)) ∘ ! (IsEquiv.β (snd e) (f (fst hf))) ≃〈 ap (λ Z₁ → Z₁ ∘ ! (IsEquiv.β (snd e) (f (fst hf)))) (ap-∘ (fst e) (IsEquiv.α (snd e) b) (ap (IsEquiv.g (snd e)) (snd hf))) 〉 
                           (ap (fst e) (IsEquiv.α (snd e) b) ∘ ap (fst e) (ap (IsEquiv.g (snd e)) (snd hf))) ∘ ! (IsEquiv.β (snd e) (f (fst hf))) ≃〈 ! (∘-assoc (ap (fst e) (IsEquiv.α (snd e) b)) (ap (fst e) (ap (IsEquiv.g (snd e)) (snd hf))) (! (IsEquiv.β (snd e) (f (fst hf))))) 〉 
                           ap (fst e) (IsEquiv.α (snd e) b) ∘ ap (fst e) (ap (IsEquiv.g (snd e)) (snd hf)) ∘ ! (IsEquiv.β (snd e) (f (fst hf))) ≃〈 ap (λ Z₁ → Z₁ ∘ ap (fst e) (ap (IsEquiv.g (snd e)) (snd hf)) ∘ ! (IsEquiv.β (snd e) (f (fst hf)))) (! (IsEquiv.γ (snd e) b)) 〉 
                           IsEquiv.β (snd e) (fst e b) ∘ ap (fst e) (ap (IsEquiv.g (snd e)) (snd hf)) ∘ ! (IsEquiv.β (snd e) (f (fst hf))) ≃〈 ap (λ Z₁ → IsEquiv.β (snd e) (fst e b) ∘ Z₁ ∘ ! (IsEquiv.β (snd e) (f (fst hf)))) (! (ap-o (fst e) (IsEquiv.g (snd e)) (snd hf)))  〉
                           IsEquiv.β (snd e) (fst e b) ∘ ap (fst e o IsEquiv.g (snd e)) (snd hf) ∘ ! (IsEquiv.β (snd e) (f (fst hf))) ≃〈 ap (λ Z₁ → IsEquiv.β (snd e) (fst e b) ∘ Z₁ ∘ ! (IsEquiv.β (snd e) (f (fst hf)))) (ap-by-id (λ x → ! (IsEquiv.β (snd e) x)) (snd hf))  〉
                           IsEquiv.β (snd e) (fst e b) ∘ (! (IsEquiv.β (snd e) (fst e b)) ∘ snd hf ∘ ! (! (IsEquiv.β (snd e) (f (fst hf))))) ∘ ! (IsEquiv.β (snd e) (f (fst hf))) ≃〈 assoc-131->right (IsEquiv.β (snd e) (fst e b)) (! (IsEquiv.β (snd e) (fst e b))) (snd hf) (! (! (IsEquiv.β (snd e) (f (fst hf))))) (! (IsEquiv.β (snd e) (f (fst hf))))  〉
                           IsEquiv.β (snd e) (fst e b) ∘ ! (IsEquiv.β (snd e) (fst e b)) ∘ snd hf ∘ ! (! (IsEquiv.β (snd e) (f (fst hf)))) ∘ ! (IsEquiv.β (snd e) (f (fst hf))) ≃〈 !-inv-r-front (IsEquiv.β (snd e) (fst e b)) (snd hf ∘ ! (! (IsEquiv.β (snd e) (f (fst hf)))) ∘ ! (IsEquiv.β (snd e) (f (fst hf))))  〉
                           snd hf ∘ ! (! (IsEquiv.β (snd e) (f (fst hf)))) ∘ ! (IsEquiv.β (snd e) (f (fst hf))) ≃〈 !-inv-l-back (snd hf) (! (IsEquiv.β (snd e) (f (fst hf)))) 〉 
                           snd hf ∎))
       comp2 = (\ hc → ap (λ Z₁ → fst hc , Z₁) 
                               (IsEquiv.α (snd e) b ∘ ap (IsEquiv.g (snd e)) (ap (fst e) (snd hc) ∘ ! (IsEquiv.β (snd e) (f (fst hc)))) ≃〈 ap (λ Z₁ → IsEquiv.α (snd e) b ∘ Z₁) (ap-∘ (IsEquiv.g (snd e)) (ap (fst e) (snd hc)) (! (IsEquiv.β (snd e) (f (fst hc))))) 〉 
                                IsEquiv.α (snd e) b ∘ ap (IsEquiv.g (snd e)) (ap (fst e) (snd hc)) ∘ ap (IsEquiv.g (snd e)) (! (IsEquiv.β (snd e) (f (fst hc)))) ≃〈 ap (λ Z₁ → IsEquiv.α (snd e) b ∘ Z₁ ∘ ap (IsEquiv.g (snd e)) (! (IsEquiv.β (snd e) (f (fst hc))))) (! (ap-o (IsEquiv.g (snd e)) (fst e) (snd hc))) 〉 
                                IsEquiv.α (snd e) b ∘ ap (IsEquiv.g (snd e) o (fst e)) (snd hc) ∘ ap (IsEquiv.g (snd e)) (! (IsEquiv.β (snd e) (f (fst hc)))) ≃〈 ap (λ Z₁ → IsEquiv.α (snd e) b ∘ Z₁ ∘ ap (IsEquiv.g (snd e)) (! (IsEquiv.β (snd e) (f (fst hc))))) (ap-by-id (λ x → ! (IsEquiv.α (snd e) x)) (snd hc)) 〉 
                                IsEquiv.α (snd e) b ∘ (! (IsEquiv.α (snd e) b) ∘ snd hc ∘ ! (! (IsEquiv.α (snd e) (IsEquiv.g (snd e) (f (fst hc)))))) ∘ ap (IsEquiv.g (snd e)) (! (IsEquiv.β (snd e) (f (fst hc))))  ≃〈 assoc-131->right (IsEquiv.α (snd e) b) (! (IsEquiv.α (snd e) b)) (snd hc) (! (! (IsEquiv.α (snd e) (IsEquiv.g (snd e) (f (fst hc)))))) (ap (IsEquiv.g (snd e)) (! (IsEquiv.β (snd e) (f (fst hc))))) 〉 
                                IsEquiv.α (snd e) b ∘ ! (IsEquiv.α (snd e) b) ∘ snd hc ∘ ! (! (IsEquiv.α (snd e) (IsEquiv.g (snd e) (f (fst hc))))) ∘ ap (IsEquiv.g (snd e)) (! (IsEquiv.β (snd e) (f (fst hc)))) ≃〈 !-inv-r-front (IsEquiv.α (snd e) b) (snd hc ∘ ! (! (IsEquiv.α (snd e) (IsEquiv.g (snd e) (f (fst hc))))) ∘ ap (IsEquiv.g (snd e)) (! (IsEquiv.β (snd e) (f (fst hc))))) 〉 
                                snd hc ∘ ! (! (IsEquiv.α (snd e) (IsEquiv.g (snd e) (f (fst hc))))) ∘ ap (IsEquiv.g (snd e)) (! (IsEquiv.β (snd e) (f (fst hc)))) ≃〈 ap (λ Z₁ → snd hc ∘ ! (! (IsEquiv.α (snd e) (IsEquiv.g (snd e) (f (fst hc))))) ∘ Z₁) (ap-! (IsEquiv.g (snd e)) (IsEquiv.β (snd e) (f (fst hc)))) 〉 
                                snd hc ∘ ! (! (IsEquiv.α (snd e) (IsEquiv.g (snd e) (f (fst hc))))) ∘ ! (ap (IsEquiv.g (snd e)) (IsEquiv.β (snd e) (f (fst hc)))) ≃〈 ap (λ Z₁ → snd hc ∘ Z₁ ∘ ! (ap (IsEquiv.g (snd e)) (IsEquiv.β (snd e) (f (fst hc))))) (!-invol (IsEquiv.α (snd e) (IsEquiv.g (snd e) (f (fst hc))))) 〉 
                                snd hc ∘ (IsEquiv.α (snd e) (IsEquiv.g (snd e) (f (fst hc)))) ∘ ! (ap (IsEquiv.g (snd e)) (IsEquiv.β (snd e) (f (fst hc)))) ≃〈  ap (λ Z₁ → snd hc ∘ IsEquiv.α (snd e) (IsEquiv.g (snd e) (f (fst hc))) ∘ ! Z₁) (! (IsEquiv.γ (snd (!equiv e)) _)) 〉 
                                snd hc ∘ IsEquiv.α (snd e) (IsEquiv.g (snd e) (f (fst hc))) ∘ ! (IsEquiv.α (snd e) (IsEquiv.g (snd e) (f (fst hc)))) ≃〈 !-inv-r-back (snd hc) (IsEquiv.α (snd e) (IsEquiv.g (snd e) (f (fst hc)))) 〉 
                                snd hc ∎))

  HFiber-fiberwise-to-total-eqv : {A : Type} {B C : A → Type} (f : (x : A) → B x → C x)
                                  → {a : A} {c : C a} → Equiv (HFiber (f a) c) (HFiber (fiberwise-to-total f) (a , c))
  HFiber-fiberwise-to-total-eqv {A}{B}{C} f {a}{c} = 
      improve (hequiv mapl
                      mapr
                      comp1
                      comp2) where
      mapl : ∀ {a} {c : C a} → (HFiber (f a) c) → (HFiber (fiberwise-to-total f) (a , c))
      mapl {a}{c} = (λ p → (a , fst p) , ap (λ Z₁ → a , Z₁) (snd p))

      abstract 
        mapr : ∀ {a} {c : C a} →  (HFiber (fiberwise-to-total f) (a , c)) → (HFiber (f a) c)
        mapr = (λ p → transport B (ap fst (snd p)) (snd (fst p)) ,
                       (over-to-hom/left (over-o-ap C (apdo snd (snd p))) ∘
                       ap (λ Z₁ → transport C Z₁ (f (fst (fst p)) (snd (fst p)))) (Σ=β1 (ap (λ r → fst r) (snd p)) (PathOver-transport-right (λ z → B z) (ap (λ r → fst r) (snd p))))) ∘ 
                       ! (over-to-hom/left (over-o-ap C (out-PathOverΠ (apdo f (ap fst (snd p))) (snd (fst p)) _ (PathOver-transport-right _ _)))))
        
        comp1 : (x : HFiber (f a) c) → Path (mapr (mapl x)) x
        comp1 = (λ x → path-induction (λ c' sndx → Path (mapr (mapl (fst x , sndx))) (fst x , sndx)) id (snd x))

        comp2 : ∀ {ac} (y : HFiber (fiberwise-to-total f) ac) → Path (mapl (mapr y)) y
        comp2 (p , id) = id

{-
  fst-HFiber-fiberwise-to-total-eqv-on-in : {A : Type} {B C : A → Type} (f : (x : A) → B x → C x) {a : A} {b : B a}
                                           → fst (HFiber-fiberwise-to-total-eqv f) (in-HFiber b)
                                              == in-HFiber (a , b)
  fst-HFiber-fiberwise-to-total-eqv-on-in f = id

  snde-HFiber-fiberwise-to-total-eqv-on-in : {A : Type} {B C : A → Type} (f : (x : A) → B x → C x) {a : A} {b : B a}
                                           → snde (HFiber-fiberwise-to-total-eqv f) (in-HFiber (a , b))
                                              == in-HFiber b
  snde-HFiber-fiberwise-to-total-eqv-on-in f = id
-}

  -- want it to compute
  HFiber-result-equiv : {A B : Type} {f : A → B} {b b' : B} → (p : b == b') 
                      → Equiv (HFiber f b) (HFiber f b') 
  HFiber-result-equiv p = improve (hequiv (λ h → fst h , p ∘ snd h) (λ h → fst h , ! p ∘ snd h) (λ x → ap (λ z → fst x , z) (!-inv-l-front p (snd x))) (λ x → ap (λ z → fst x , z) (!-inv-r-front p (snd x))))
