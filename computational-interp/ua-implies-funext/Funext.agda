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
              (coe (ap (λ y → A → y) (! (contract-Paths {B}))) (coe (contract-Paths {A → B}) ((f , f) , id))) =〈 ap (λ z → coe (ap (λ y → A → y) (! (contract-Paths {B}))) z) (ap= (type=β contract-Paths≃)) 〉
              (coe (ap (λ y → A → y) (! (contract-Paths {B}))) f) =〈 ap= (! (transport-ap-assoc' (λ x → x) (λ y → A → y) (! contract-Paths))) 〉
              (transport (λ y → A → y) (! (contract-Paths {B})) f) =〈 transport-→-post (! contract-Paths) f 〉
              (\ g -> coe (! (contract-Paths {B})) o g) f =〈 id 〉 
              (coe (! (contract-Paths {B})) o f) =〈 ap (λ x → x o f) (type=β! contract-Paths≃) 〉 
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

  -- uses η for records
  commute : ∀ {A B} → Equiv (A → Paths B) (Σ \ (fg : (A -> B) × (A → B)) → (x : A) → fst fg x == snd fg x)
  commute {A}{B} = (improve (hequiv (λ h →
                                            ((λ x → fst (fst (h x))) , (λ x → snd (fst (h x)))) ,
                                            (λ x → snd (h x))) 
                                       (λ i → λ x → ((fst (fst i) x) , (snd (fst i) x)) , snd i x) (λ _ → id) (λ _ → id)))
    -- this can be written with AC, but it's too annoying to do the beta reduction if you write it this way
    -- (apΣ-l' (AC {A = A} {B = λ _ → B} {C = λ _ _ → B})) ∘ ua (AC {A = A} {B = λ _ → B × B} {C = λ _ b1b2 → fst b1b2 == snd b1b2})

  commuteβ : {A B : Type} → (leftright o (coe (! (ua (commute{A}{B}))))) == fst 
  commuteβ = ap (\ x -> leftright o x) (type=β! commute)

  funext : {A B : Type} (f g : A → B) → (f == g) == ((x : A) → f x == g x)
  funext {A}{B} f g = f == g =〈 hfiber-fst {B = λ fg → fst fg == snd fg} (f , g) 〉 
                      Σ (λ (p : Paths (A → B)) → fst p == (f , g)) =〈 apΣ-l eqv id 〉 
                      Σ (λ (q : A → Paths B) → fst (coe (! eqv) q) == (f , g)) =〈 fiberwise-equiv-to-total (λ p1 → ua (pre∘-equiv (preserves-fst (coe (! eqv) p1) ∘ ! (ap leftright (ap= (transport-inv-2 (λ x → x) eqv)))))) 〉 
                      Σ (λ (q : A → Paths B) → leftright q == (f , g)) =〈 apΣ-l (ua commute) id 〉 
                      Σ (λ (r : Σ \ (fg : (A → B) × (A → B)) → ((x : A) → fst fg x == snd fg x)) → (leftright (coe (! (ua commute)) r)) == (f , g)) =〈 ap (λ z → Σ (λ (r : Σ (λ (fg : (A → B) × (A → B)) → (x : A) → fst fg x == snd fg x)) → z r == (f , g))) commuteβ 〉 
                      Σ (λ (r : Σ \ (fg : (A → B) × (A → B)) → ((x : A) → fst fg x == snd fg x)) → (fst r) == (f , g)) =〈 ! (hfiber-fst (f , g)) 〉 
                      (((x : A) → f x == g x) ∎)

  funext-comp : {A B : Type} (f : A → B) → coe (funext f f) id == (λ x → id)
  funext-comp f = coe (funext f f) id =〈 {!coe (apΣ-l eqv id)!} 〉 
                  -- after step 1:  (((f , f) , id) , id)
                  -- after step 2: ((λ x → ((f x) , (f x)) , id) , ?)
                  ((λ x → id) ∎)

