{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open Paths

module lib.Prods where

  record Unit : Type where
    constructor <> 
  
  record Σe (A : Type) (B : A -> Type) : Type where
     constructor _,_
     field
       fst : A
       snd : B fst
  open Σe public

  Σ : {A : Type} -> (B : A -> Type) -> Type
  Σ {A} B = Σe A B

  infixr 0 _,_
  
  _×_ : Type -> Type -> Type
  a × b = Σ (\ (_ : a) -> b)

  infixr 10 _×_

  syntax Σe A (\ x  -> B) = Σ[ x ∶ A ] B

  fst≃ : {A : Type} {B : A -> Type} {p q : Σ[ x ∶ A ] B x} -> p ≃ q -> (fst p) ≃ (fst q)
  fst≃ = ap fst
  
  snd≃ : {A : Type} {B : A -> Type} {p q : Σ B} -> (c : p ≃ q) -> (transport B (fst≃ c) (snd p)) ≃ (snd q)
  snd≃ id = id

  pair≃ : {A : Type} {B : A -> Type} {p q : Σ B} -> (α : (fst p) ≃ (fst q)) -> (transport B α (snd p)) ≃ (snd q) -> p ≃ q
  pair≃ {p = x , y} {q = .x , .y} id id = id

  Σ≃η : {A : Type} {B : A -> Type} {p q : Σ B} -> (α : p ≃ q) -> (pair≃ (fst≃ α) (snd≃ α)) ≃ α
  Σ≃η {p = x , y} {q = .x , .y} id = id

  Σ≃β1 : {A : Type} {B : A -> Type} {p q : Σ B} 
       (α : Path (fst p) (fst q)) 
       (β : Path (transport B α (snd p)) (snd q))
       -> Path (fst≃{B = B} (pair≃ α β)) α
  Σ≃β1 {p = x , y} {q = .x , .y} id id = id

  Σ≃β2 : {A : Type} {B : A -> Type} {p q : Σ B} 
         (α : (fst p) ≃ (fst q))
         (β : (transport B α (snd p)) ≃ (snd q))
      -> (snd≃{B = B} (pair≃ α β)) ≃ 
         (β ∘ (ap (λ x → transport B x (snd p)) (Σ≃β1 {B = B} α β)))
  Σ≃β2 {p = x , y} {q = .x , .y} id id = id

  transport-Σ : {Γ : Type} {θ1 θ2 : Γ} (δ : θ1 ≃ θ2)
            (A : Γ -> Type) (B : (γ : Γ) -> A γ -> Type)
            (p : Σ \(x : A θ1) -> B θ1 x)
          -> transport (\ γ -> Σ (B γ)) δ p 
           ≃ (transport A δ (fst p) , 
              transport (λ (γ' : Σ A) → B (fst γ') (snd γ')) 
                    (pair≃ δ id) 
                    (snd p))
  transport-Σ id A B p = id

  transport-com-for-ap-pair :
    {Γ : Type} {θ1 θ2 : Γ} (δ : θ1 ≃ θ2)
    (A : Γ -> Type) (B : (γ : Γ) -> A γ -> Type)
    (p1 : (γ : Γ) -> A γ)
    (p2 : (γ : Γ) -> B γ (p1 γ))
   -> (transport (B θ2) (apd p1 δ)
             (transport (λ γ' → B (fst γ') (snd γ'))
                    (pair≃ {Γ}{A} δ id)
                    (p2 θ1)))
      ≃ 
      (transport (λ z → B z (p1 z)) δ (p2 θ1))
  transport-com-for-ap-pair id _ _ _ _ = id

  ap-pair : {Γ : Type} {θ1 θ2 : Γ} {δ : θ1 ≃ θ2}
              {A : Γ -> Type} {B : (γ : Γ) -> A γ -> Type} 
              {p1 : (γ : Γ) -> A γ} 
              {p2 : (γ : Γ) -> B γ (p1 γ)} 
           -> (apd (\ γ -> (_,_ {A γ} {B γ} (p1 γ) (p2 γ))) δ)
            ≃ pair≃ (apd p1 δ) (apd p2 δ ∘ (transport-com-for-ap-pair δ A B p1 p2))
              ∘ transport-Σ δ A B (p1 θ1 , p2 θ1)
  ap-pair {δ = id} = id

  ap-fst : {Γ : Type} {θ1 θ2 : Γ} {δ : θ1 ≃ θ2}
             {A : Γ -> Type} {B : (γ : Γ) -> A γ -> Type} 
             {p : (γ : Γ) -> Σ (B γ)} 
           -> apd (\ γ -> fst (p γ)) δ
            ≃ fst≃ ((apd p δ) ∘ ! (transport-Σ δ A B (p θ1)))
  ap-fst {δ = id} = id

  transport-com-for-ap-snd : 
             {Γ : Type} {θ1 θ2 : Γ} (δ : θ1 ≃ θ2)
             (A : Γ -> Type) (B : (γ : Γ) -> A γ -> Type)
             (p : (γ : Γ) -> Σ (B γ))
       -> Path (transport (λ z → B z (fst (p z))) δ (snd (p θ1)))
             (transport (B θ2) (fst≃ (apd p δ))
                    (snd (transport (λ z → Σe (A z) (B z)) δ (p θ1))))
  transport-com-for-ap-snd id _ _ _ = id

  ap-snd : {Γ : Type} {θ1 θ2 : Γ} {δ : θ1 ≃ θ2}
             {A : Γ -> Type} {B : (γ : Γ) -> A γ -> Type} 
             {p : (γ : Γ) -> Σ (B γ)} 
           -> apd (\ γ -> snd (p γ)) δ
            ≃ snd≃ (apd p δ) ∘ transport-com-for-ap-snd δ A B p
  ap-snd {δ = id} = id


  -- non-dependent pairs

  transport-× : {Γ : Type} {θ1 θ2 : Γ} (δ : θ1 ≃ θ2)
          (A : Γ -> Type) (B : (γ : Γ) -> Type)
        -> transport (\ γ -> A γ × B γ) δ 
         ≃ (\ p -> (transport A δ (fst p) , transport B δ (snd p)))
  transport-× id A B = id

  snd×≃ : {A B : Type} {p q : A × B} -> p ≃ q -> (snd p) ≃ (snd q)
  snd×≃ id = id    

  pair×≃ : {A B : Type} {p q : A × B} -> (fst p) ≃ (fst q) -> (snd p) ≃ (snd q) -> p ≃ q
  pair×≃ a b = ap2 _,_ a b

  ×≃η : {A B : Type} {p q : A × B} -> (α : p ≃ q) -> (pair×≃ (fst≃ α) (snd×≃ α)) ≃ α
  ×≃η id = id

  ×≃β1 : {A B : Type} {p q : A × B} 
        (α : Path (fst p) (fst q)) 
        (β : Path (snd p) (snd q))
        -> Path (fst≃{B = \ _ -> B} (pair×≃ α β)) α
  ×≃β1 {p = x , y} {q = .x , .y} id id = id

  ×≃β2 : {A B : Type} {p q : A × B} 
        (α : Path (fst p) (fst q)) 
        (β : Path (snd p) (snd q))
      -> (snd×≃ (pair×≃ α β)) ≃ 
         β
  ×≃β2 {p = x , y} {q = .x , .y} id id = id

  ∘-× : {A : Type} {M N P Q R S : A} (a : N ≃ P) (b : R ≃ S) (c : M ≃ N) (d : Q ≃ R)
      -> pair×≃ a b ∘ pair×≃ c d ≃ pair×≃ (a ∘ c) (b ∘ d)
  ∘-× id id id id = id
  
  ap-×-fst : {A B : Type} {N M : A} -> (f : A -> B) -> (y : B) -> (α : M ≃ N) ->
               ap (λ x → f (x) , y) α ≃ 
               pair×≃ (ap (λ x → f x) α) (ap (λ _ → y) α)
  ap-×-fst _ _ id = id

  ap-×-snd : {A B : Type} {N M : A} -> (f : A -> B) -> (y : B) -> (α : M ≃ N) ->
               ap (λ x → y , f (x)) α ≃
               pair×≃ (ap (λ _ → y) α) (ap (λ x → f (x)) α)
  ap-×-snd _ _ id = id


      