{-# OPTIONS --without-K --type-in-type #-}

open import NoFunextPrelude

module Funext where

  eqv : ∀ {A B} → Paths (A → B) == (A → Paths B)
  eqv {A} {B} = ! (ap (λ y → A → y) (contract-Paths {B})) ∘ (contract-Paths {A → B})


  eqv-id : ∀ {A B} (f : A → B) → coe eqv ((f , f) , id) == (λ x → ((f x) , (f x)) , id)
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

  left : ∀ {A B} → (A → Paths B) → A → B
  left f x = (fst (fst (f x)))

  right : ∀ {A B} → (A → Paths B) → A → B
  right f x = (snd (fst (f x)))

  leftright : ∀ {A B} → (A → Paths B) → (A → B) × (A → B)
  leftright f = (left f , right f)

  preserves-fst : ∀ {A B} → (α : Paths (A → B)) 
          → (leftright (coe eqv α)) == fst α
  preserves-fst {A}{B} ((f , .f) , id) = ap2 _,_ (ap left (eqv-id f)) (ap right (eqv-id f))

  -- uses η 
  laststep : ∀ {A B} (f g : A → B) → Equiv (Σ (λ (p₁ : A → Paths B) → leftright p₁ == (f , g))) ((x : A) → f x == g x)
  laststep {A}{B} f g = improve (hequiv (λ z → transport (λ (fg : (A → B) × (A → B)) → (x : A) → (fst fg) x == (snd fg) x) (snd z) (λ x → snd (fst z x)))
                                        (λ h → (λ x → (f x , g x) , h x) , id)
                                        α 
                                        (λ y → id) -- uses η for → 
                                ) where 
           α : {fg : (A → B) × (A → B)} → (x : (Σ (λ (p₁ : A → Paths B) → leftright p₁ == fg))) → 
               ((λ x₁ → (fst fg x₁ , snd fg x₁) , transport (λ fg' → (x₂ : A) → fst fg' x₂ == snd fg' x₂) (snd x) (λ x₂ → snd (fst x x₂)) x₁) , id) == x
           α {fg} (h , α) = path-induction
                              (λ fg₁ α₁ →
                                 ((λ x₁ →
                                     (fst fg₁ x₁ , snd fg₁ x₁) ,
                                     transport (λ fg' → (x₂ : A) → Id (fst fg' x₂) (snd fg' x₂)) α₁
                                     (λ x₂ → snd (h x₂)) x₁)
                                  , id)
                                 == (h , α₁))
                              id -- uses η for → and Σ
                              α

  funext : {A B : Type} (f g : A → B) → (f == g) == ((x : A) → f x == g x)
  funext {A}{B} f g = f == g =〈 hfiber-fst {B = λ fg → fst fg == snd fg} (f , g) 〉 
                      Σ (λ (p : Paths (A → B)) → fst p == (f , g)) =〈 apΣ-l eqv id 〉 
                      Σ (λ (q : A → Paths B) → fst (coe (! eqv) q) == (f , g)) =〈 fiberwise-equiv-to-total (λ p1 → ua (pre∘-equiv (preserves-fst (coe (! eqv) p1) ∘ ! (ap leftright (ap= (transport-inv-2 (λ x → x) eqv)))))) 〉 
                      Σ (λ (q : A → Paths B) → (left q , right q) == (f , g)) =〈 ua (laststep f g) 〉 
                      (((x : A) → f x == g x) ∎)

  funext-comp : {A B : Type} (f : A → B) → coe (funext f f) id == (λ x → id)
  funext-comp f = coe (funext f f) id =〈 {!coe (apΣ-l eqv id)!} 〉 
                  -- after step 1:  (((f , f) , id) , id)
                  -- after step 2: ((λ x → ((f x) , (f x)) , id) , ?)
                  ((λ x → id) ∎)

