
{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude hiding (_×_ ; fst ; snd; _,_; fst≃; snd≃; pair≃)
open Paths 

module applications.ProdHigherBetaEta where

    -- derived form 
    record _×_ (A : Set) (B : Set) : Set where
      constructor _,_
      field 
        fst : A
        snd : B
    open _×_

    subst-× : {Γ : Set} {θ1 θ2 : Γ} (δ : θ1 ≃ θ2)
            (A : Γ -> Set) (B : (γ : Γ) -> Set)
          -> subst (\ γ -> A γ × B γ) δ 
           ≃ (\ p -> (subst A δ (fst p) , subst B δ (snd p)))
    subst-× Refl A B = Refl

    fst≃ : {A B : Set} {p q : A × B} -> p ≃ q -> (fst p) ≃ (fst q)
    fst≃ = resp fst

    snd≃ : {A B : Set} {p q : A × B} -> p ≃ q -> (snd p) ≃ (snd q)
    snd≃ = resp snd

    pair≃ : {A B : Set} {p q : A × B} -> (fst p) ≃ (fst q) -> (snd p) ≃ (snd q) -> p ≃ q
    pair≃ a b = resp2 _,_ a b

    resp-resp2-o : {A B C D : Set} (g : C -> D) (f : A -> B -> C)
            {M N : A} (α : M ≃ N)
            {M' N' : B} (β : M' ≃ N')
          -> resp2 (\ x y -> g (f x y)) α β ≃ resp g (resp2 f α β)
    resp-resp2-o _ _ Refl Refl = Refl

    resp2-resp-o : {A B C A' : Set} (f : A -> B -> C) (g1 : A' -> A) (g2 : A' -> B) 
            {M N : A'} (α : M ≃ N)
          -> resp (\ x -> f (g1 x) (g2 x)) α ≃ resp2 f (resp g1 α) (resp g2 α)
    resp2-resp-o  _ _ _ Refl = Refl

    ×≃η : {A B : Set} {p q : A × B} -> (α : p ≃ q) -> (pair≃ (fst≃ α) (snd≃ α)) ≃ α
    ×≃η α = resp-id _ ∘ ! (resp2-resp-o _,_ fst snd α)
  
    ×≃β1 : {A B : Set} {p q : A × B} 
          (α : Id (fst p) (fst q)) 
          (β : Id (snd p) (snd q))
          -> Id (fst≃ (pair≃ α β)) α
    ×≃β1 α β = resp2-β1 α β ∘ ! (resp-resp2-o fst _,_ α β)
  
    ×≃β2 : {A B : Set} {p q : A × B} 
          (α : Id (fst p) (fst q)) 
          (β : Id (snd p) (snd q))
        -> (snd≃ (pair≃ α β)) ≃ 
           β
    ×≃β2 {p = x , y} {q = .x , .y} Refl Refl = Refl
 
    ∘-× : {A : Set} {M N P Q R S : A} (a : N ≃ P) (b : R ≃ S) (c : M ≃ N) (d : Q ≃ R)
        -> pair≃ a b ∘ pair≃ c d ≃ pair≃ (a ∘ c) (b ∘ d)
    ∘-× Refl Refl Refl Refl = Refl
    
    -- resp-×-fst : {A B : Set} {N M : A} -> (f : A -> B) -> (y : B) -> (α : M ≃ N) ->
    --              resp (λ x → f (x) , y) α ≃ 
    --              nondep-pair≃ (resp (λ x → f x) α) (resp (λ _ → y) α)
    -- resp-×-fst _ _ Refl = Refl

    -- resp-×-snd : {A B : Set} {N M : A} -> (f : A -> B) -> (y : B) -> (α : M ≃ N) ->
    --              resp (λ x → y , f (x)) α ≃
    --              nondep-pair≃ (resp (λ _ → y) α) (resp (λ x → f (x)) α)
    -- resp-×-snd _ _ Refl = Refl

    module ThreeCells where

      pair≃3 : {A B : Set} {p q : A × B} 
                      {α1 α2 : Id (fst p) (fst q)} 
                      {β1 β2 : Id (snd p) (snd q)}
                    -> α1 ≃ α2
                    -> β1 ≃ β2
                    -> (pair≃ α1 β1) ≃ (pair≃ α2 β2)
      pair≃3 a b = resp2 pair≃ a b

      fst≃3 : {A B : Set} {p q : A × B} {α β : p ≃ q}
                    -> α ≃ β
                    -> fst≃ α ≃ fst≃ β
      fst≃3 a = resp fst≃ a

      snd≃3 : {A B : Set} {p q : A × B} {α β : p ≃ q}
                    -> α ≃ β
                    -> snd≃ α ≃ snd≃ β
      snd≃3 a = resp snd≃ a

      ×β3-1 : {A B : Set} {p q : A × B} 
                      {α1 α2 : Id (fst p) (fst q)} 
                      {β1 β2 : Id (snd p) (snd q)}
              (γ  : α1 ≃ α2)
              (γ' : β1 ≃ β2)
            -> fst≃3 (pair≃3 γ γ') ≃ ! (×≃β1 α2 β2) ∘ γ ∘ ×≃β1 α1 β1
      ×β3-1 γ γ' = {!resp2-resp (λ≃ \ x -> λ≃ \ y -> ×≃β1 x y) γ γ'  !} ∘ ! (resp-resp2-o fst≃ pair≃ γ γ')
