
{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude hiding (_×_ ; fst ; snd; _,_; fst≃; snd≃; pair≃ ; transport-×; ×≃η; ×≃β1; ×≃β2; ∘-×)
 

module computational-interp.ProdHigherBetaEta where

    -- derived form 
    record _×_ (A : Set) (B : Set) : Set where
      constructor _,_
      field 
        fst : A
        snd : B
    open _×_

    transport-× : {Γ : Set} {θ1 θ2 : Γ} (δ : θ1 ≃ θ2)
            (A : Γ -> Set) (B : (γ : Γ) -> Set)
          -> transport (\ γ -> A γ × B γ) δ 
           ≃ (\ p -> (transport A δ (fst p) , transport B δ (snd p)))
    transport-× id A B = id

    fst≃ : {A B : Set} {p q : A × B} -> p ≃ q -> (fst p) ≃ (fst q)
    fst≃ = ap fst

    snd≃ : {A B : Set} {p q : A × B} -> p ≃ q -> (snd p) ≃ (snd q)
    snd≃ = ap snd

    pair≃ : {A B : Set} {p q : A × B} -> (fst p) ≃ (fst q) -> (snd p) ≃ (snd q) -> p ≃ q
    pair≃ a b = ap2 _,_ a b

    ap-ap2-o : {A B C D : Set} (g : C -> D) (f : A -> B -> C)
            {M N : A} (α : M ≃ N)
            {M' N' : B} (β : M' ≃ N')
          -> ap2 (\ x y -> g (f x y)) α β ≃ ap g (ap2 f α β)
    ap-ap2-o _ _ id id = id

    ap2-ap-o : {A B C A' : Set} (f : A -> B -> C) (g1 : A' -> A) (g2 : A' -> B) 
            {M N : A'} (α : M ≃ N)
          -> ap (\ x -> f (g1 x) (g2 x)) α ≃ ap2 f (ap g1 α) (ap g2 α)
    ap2-ap-o  _ _ _ id = id

    ×≃η : {A B : Set} {p q : A × B} -> (α : p ≃ q) -> (pair≃ (fst≃ α) (snd≃ α)) ≃ α
    ×≃η α = ap-id _ ∘ ! (ap2-ap-o _,_ fst snd α)
  
    ×≃β1 : {A B : Set} {p q : A × B} 
          (α : Id (fst p) (fst q)) 
          (β : Id (snd p) (snd q))
          -> Id (fst≃ (pair≃ α β)) α
    ×≃β1 α β = ap2-β1 α β ∘ ! (ap-ap2-o fst _,_ α β)
  
    ×≃β2 : {A B : Set} {p q : A × B} 
          (α : Id (fst p) (fst q)) 
          (β : Id (snd p) (snd q))
        -> (snd≃ (pair≃ α β)) ≃ 
           β
    ×≃β2 {p = x , y} {q = .x , .y} id id = id
 
    ∘-× : {A : Set} {M N P Q R S : A} (a : N ≃ P) (b : R ≃ S) (c : M ≃ N) (d : Q ≃ R)
        -> pair≃ a b ∘ pair≃ c d ≃ pair≃ (a ∘ c) (b ∘ d)
    ∘-× id id id id = id
    
    -- ap-×-fst : {A B : Set} {N M : A} -> (f : A -> B) -> (y : B) -> (α : M ≃ N) ->
    --              ap (λ x → f (x) , y) α ≃ 
    --              nondep-pair≃ (ap (λ x → f x) α) (ap (λ _ → y) α)
    -- ap-×-fst _ _ id = id

    -- ap-×-snd : {A B : Set} {N M : A} -> (f : A -> B) -> (y : B) -> (α : M ≃ N) ->
    --              ap (λ x → y , f (x)) α ≃
    --              nondep-pair≃ (ap (λ _ → y) α) (ap (λ x → f (x)) α)
    -- ap-×-snd _ _ id = id

    module ThreeCells where

      pair≃3 : {A B : Set} {p q : A × B} 
                      {α1 α2 : Id (fst p) (fst q)} 
                      {β1 β2 : Id (snd p) (snd q)}
                    -> α1 ≃ α2
                    -> β1 ≃ β2
                    -> (pair≃ α1 β1) ≃ (pair≃ α2 β2)
      pair≃3 a b = ap2 pair≃ a b

      fst≃3 : {A B : Set} {p q : A × B} {α β : p ≃ q}
                    -> α ≃ β
                    -> fst≃ α ≃ fst≃ β
      fst≃3 a = ap fst≃ a

      snd≃3 : {A B : Set} {p q : A × B} {α β : p ≃ q}
                    -> α ≃ β
                    -> snd≃ α ≃ snd≃ β
      snd≃3 a = ap snd≃ a

      ×β3-1 : {A B : Set} {p q : A × B} 
                      {α1 α2 : Id (fst p) (fst q)} 
                      {β1 β2 : Id (snd p) (snd q)}
              (γ  : α1 ≃ α2)
              (γ' : β1 ≃ β2)
            -> fst≃3 (pair≃3 γ γ') ≃ ! (×≃β1 α2 β2) ∘ γ ∘ ×≃β1 α1 β1
      ×β3-1 γ γ' = {!ap2-ap (λ≃ \ x -> λ≃ \ y -> ×≃β1 x y) γ γ'  !} ∘ ! (ap-ap2-o fst≃ pair≃ γ γ')
