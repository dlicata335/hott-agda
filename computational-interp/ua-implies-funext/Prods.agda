{-# OPTIONS --without-K --type-in-type #-}

open import NoFunextPrelude

module Prods where

  -- this is written out by hand in NoFunextPrelude, but that requires pair= 
  apΣ-l : {A A' : Type} {B : A → Type} {B' : A' → Type}
        (a : A == A')
        (b : (\ (x : A') → B (coe (! a) x)) == B')
      → Σ B == Σ B'
  apΣ-l id id = id
 
  -- build in some β reduction
  apΣ-l' : {A A' : Type} {B : A → Type} 
        (a : Equiv A A')
      → (Σ B) == (Σ (\ (x : A') → B (IsEquiv.g (snd a) x)))
  apΣ-l' {B = B} e = apΣ-l (ua e) (ap (λ y → λ x → B (y x)) (type=β! e))

  eqv : ∀ {A B} → Paths (A × B) == (Paths A × Paths B)
  eqv {A} {B} = ! (ap2 (λ x y → x × y) (contract-Paths {A}) (contract-Paths {B})) ∘ (contract-Paths {A × B})

  eqv-id : ∀ {A B} (f : A × B) → coe eqv ((f , f) , id) == (((fst f , fst f) , id) , ((snd f , snd f) , id))
  eqv-id = {!!}
{-
  eqv-id {A}{B} f =
              coe (! (ap (λ y → A → y) (contract-Paths {B})) ∘ (contract-Paths {A → B})) ((f , f) , id) =〈 ap (λ h → coe (h ∘ contract-Paths {A → B}) ((f , f) , id)) (! (ap-! (λ y → A → y) (contract-Paths {B}))) 〉
              coe ((ap (λ y → A → y) (! (contract-Paths {B}))) ∘ (contract-Paths {A → B})) ((f , f) , id) =〈 ap= (transport-∘ (λ x → x) (ap (λ y → A → y) (! (contract-Paths {B}))) (contract-Paths {A → B})) 〉
              (coe (ap (λ y → A → y) (! (contract-Paths {B}))) o coe (contract-Paths {A → B})) ((f , f) , id) =〈 id 〉
              (coe (ap (λ y → A → y) (! (contract-Paths {B}))) (coe (contract-Paths {A → B}) ((f , f) , id))) =〈 ap (λ z → coe (ap (λ y → A → y) (! (contract-Paths {B}))) z) (ap= (type=β contract-Paths-eqv)) 〉
              (coe (ap (λ y → A → y) (! (contract-Paths {B}))) f) =〈 ap= (! (transport-ap-assoc' (λ x → x) (λ y → A → y) (! contract-Paths))) 〉
              (transport (λ y → A → y) (! (contract-Paths {B})) f) =〈 transport-→-post (! contract-Paths) f 〉
              (\ g -> coe (! (contract-Paths {B})) o g) f =〈 id 〉 
              (coe (! (contract-Paths {B})) o f) =〈 ap (λ x → x o f) (type=β! contract-Paths-eqv) 〉 
              (λ x → ((f x) , (f x)) , id) ∎ 
-}

  left : ∀ {A B} → (Paths A × Paths B) → A × B
  left p = fst (fst (fst p)) , fst (fst (snd p))

  right : ∀ {A B} → (Paths A × Paths B) → A × B
  right p = snd (fst (fst p)) , snd (fst (snd p))

  leftright : ∀ {A B} → (Paths A × Paths B) → (A × B) × (A × B)
  leftright p = (left p , right p)

  preserves-fst : ∀ {A B} → (α : Paths (A × B)) 
          → (leftright (coe eqv α)) == fst α
  preserves-fst {A}{B} ((f , .f) , id) = ap2 _,_ (ap left (eqv-id f)) (ap right (eqv-id f))

  -- uses η 
  laststep : ∀ {A B} (f g : A × B) → Equiv (Σ (λ (p₁ : Paths A × Paths B) → leftright p₁ == (f , g))) ((fst f == fst g) × (snd f == snd g))
  laststep {A}{B} f g = improve (hequiv (λ x → transport (λ (p : (A × B) × A × B) →
                                                              (fst (fst p) == fst (snd p)) × (snd (fst p) == snd (snd p))) (snd x) (snd (fst (fst x)) , snd (snd (fst x)))) 
                                        (λ pq → ((_ , (fst pq)) , (_ , snd pq)) , id) -- uses η
                                        {!!}
                                        (λ _ → id)) -- uses η 
           where
           α : {fg : (A × B) × (A × B)} → (x : (Σ (λ (p₁ : Paths A × Paths B) → leftright p₁ == fg))) → 
               ((((fst (fst fg) , fst (snd fg)) ,
                    fst
                    (transport
                     (λ p →
                        Σe (Id (fst (fst p)) (fst (snd p)))
                        (λ _ → Id (snd (fst p)) (snd (snd p))))
                     (snd x) (snd (fst (fst x)) , snd (snd (fst x)))))
                   ,
                   (snd (fst fg) , snd (snd fg)) ,
                   snd
                   (transport
                    (λ p →
                       Σe (Id (fst (fst p)) (fst (snd p)))
                       (λ _ → Id (snd (fst p)) (snd (snd p))))
                    (snd x) (snd (fst (fst x)) , snd (snd (fst x)))))
                  , id) == x
           α {fg} (h , α) = path-induction
                              (λ fg α →
                                 ((((fst (fst fg) , fst (snd fg)) ,
                                      fst
                                      (transport
                                       (λ p →
                                          Σe (Id (fst (fst p)) (fst (snd p)))
                                          (λ _ → Id (snd (fst p)) (snd (snd p))))
                                       α (snd (fst h) , snd (snd h))))
                                     ,
                                     (snd (fst fg) , snd (snd fg)) ,
                                     snd
                                     (transport
                                      (λ p →
                                         Σe (Id (fst (fst p)) (fst (snd p)))
                                         (λ _ → Id (snd (fst p)) (snd (snd p))))
                                      α (snd (fst h) , snd (snd h))))
                                    , id)
                                 == (h , α))
                              id -- uses η for → and Σ
                              α

  pairext : {A B : Type} (f g : A × B) → (f == g) == ((fst f == fst g) × (snd f == snd g))
  pairext {A}{B} f g = f == g =〈 hfiber-fst {B = λ fg → fst fg == snd fg} (f , g) 〉 
                       Σ (λ (p : Paths (A × B)) → fst p == (f , g)) =〈 apΣ-l eqv id 〉 
                       Σ (λ (q : Paths A × Paths B) → fst (coe (! eqv) q) == (f , g)) =〈 fiberwise-equiv-to-total {! (λ p1 → ua (pre∘-equiv (preserves-fst (coe (! eqv) p1) ∘ ! (ap leftright (ap= (transport-inv-2 (λ x → x) eqv)))))) !} 〉 
                       Σ (λ (q : Paths A × Paths B) → (left q , right q) == (f , g)) =〈 ua (laststep f g) 〉 
                       (((fst f == fst g) × (snd f == snd g)) ∎)

