{-# OPTIONS --without-K --type-in-type #-}

open import NoFunextPrelude
open import Funext2 using (funext) 

module FunextDep where

  Homotopies : (A : Type) → (A → Type) → Type
  Homotopies A B = (Σ \ (fg : ((x : A) -> B x) × ((x : A) → B x)) → (x : A) → fst fg x == snd fg x)

  -- uses η for Σ
  swap : ∀ {A B} → Equiv ((x : A) → Paths (B x)) (Homotopies A B)
  swap = (improve (hequiv (λ h → ((λ x → fst (fst (h x))) , (λ x → snd (fst (h x)))) , (λ x → snd (h x))) 
                          (λ i → λ x → ((fst (fst i) x) , (snd (fst i) x)) , snd i x)
                          (λ _ → id) (λ _ → id)))
    -- this can be written with AC, but it's too annoying to do the beta reduction if you write it this way
    -- (apΣ-l' (AC {A = A} {B = λ _ → B} {C = λ _ _ → B})) ∘ ua (AC {A = A} {B = λ _ → B × B} {C = λ _ b1b2 → fst b1b2 == snd b1b2})

  abstract
    funextt : ∀ {A B} → Equiv (Paths ((x : A) → B x)) (Homotopies A B)
    funextt {A} {B} = Paths ((x : A) → B x) ≃〈 contract-Paths-eqv 〉 
                      ((x : A) → B x) ≃〈 coe-equiv (ap {M = B} {N = Paths o B} (λ y → (x : A) → y x) (coe (! (funext _ _)) (λ x → ua (!equiv contract-Paths-eqv)))) 〉 
                      ((x : A) → Paths (B x)) ≃〈 swap 〉 
                      Homotopies A B ∎∎
  
    funextt-id : ∀ {A} {B : A → Type} (f : (x : A) → B x) → fst funextt ((f , f) , id) == ((f , f) , λ x → id)
    funextt-id = {!!}
{-
  funextt-id {A} f = fst funextt ((f , f) , id) =〈 id 〉 
                     fst swap (coe (ap (λ y → A → y) (ua (!equiv (contract-Paths-eqv)))) f) =〈 ap (fst swap) (ap= (! (transport-ap-assoc' (λ x → x) (λ y → A → y) (ua (!equiv contract-Paths-eqv))))) 〉 
                     fst swap (transport (λ y → A → y) (ua (!equiv (contract-Paths-eqv))) f) =〈 ap (fst swap) (transport-→-post (ua (!equiv contract-Paths-eqv)) f) 〉 
                     fst swap (coe (ua (!equiv (contract-Paths-eqv))) o f) =〈 ap (λ z → fst swap (z o f)) (type=β (!equiv contract-Paths-eqv)) 〉 
                     fst swap (fst (!equiv (contract-Paths-eqv)) o f) =〈 id 〉 
                     ((f , f) , (λ x → id)) ∎
-}

  preserves-fst : ∀ {A} {B : A → Type} → (α : Paths ((x : A) → B x)) 
          → (fst (fst funextt α)) == fst α
  preserves-fst {A}{B} ((f , .f) , id) = ap fst (funextt-id f)

  funextd : {A : Type} {B : A → Type} (f g : (x : A) → B x) → (f == g) == ((x : A) → f x == g x)
  funextd {A}{B} f g = fiberwise-equiv-from-total' funextt preserves-fst (f , g)

{-
  funext-comp : {A B : Type} (f : A → B) → coe (funext f f) id == (λ x → id)
  funext-comp f = coe (funext f f) id =〈 {!coe (apΣ-l eqv id)!} 〉 
                  -- after step 1:  (((f , f) , id) , id)
                  -- after step 2: ((λ x → ((f x) , (f x)) , id) , ?)
                  ((λ x → id) ∎)

-}

