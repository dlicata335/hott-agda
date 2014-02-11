module misc.TTinTT where

  -- some preliminaries

  record Σe (A : Set0) (B : A -> Set0) : Set0 where
    constructor _,_
    field
      fst : A
      snd : B fst
  open Σe public

  Σ : {A : Set0} -> (B : A -> Set0) -> Set0
  Σ {A} B = Σe A B

  infixr 0 _,_

  data _==_ {A : Set0} (M : A) : A → Set0 where
   refl : M == M

  transport :  {B : Set0} (E : B → Set0) 
              {b1 b2 : B} → b1 == b2 → (E b1 → E b2)
  transport C refl = λ x → x

  -- funext
  postulate
    λ=  : ∀ {A} {B : A -> Set} {f g : (x : A) -> B x} -> ((x : A) -> (f x) == (g x)) -> f == g



  {-
    Syntax of type theory and interpretation a la
      Outrageous but Meaningful Coindcidences.  
      Conor McBride
  -}


  -- syntax and its interpretation

  -- Ty Γ A represents a type of the object language which is well-formed
  -- in context Γ (think of this as ⟦ Γ' ⟧ where is the object language context)
  -- and denotes the type A
  data Ty : ∀ (Γ : Set0) (A : Γ → Set0) → Set1


  -- Ty Γ A represents a term of the object language which is well-formed
  -- in context Γ (think of this as ⟦ Γ' ⟧ where is the object language context)
  -- and *has* the type A.  
  -- the interpretation of terms is given by the function 'interp' below,
  -- inductive-recursively.  
  data Tm : ∀ (Γ : Set0) (A :  Γ -> Set0) → Set1

  interp  : ∀ {Γ} {A : Γ -> Set0} → Tm Γ A → (θ : Γ) → (A θ)

  data Ty where
    b : ∀ {Γ A} → Ty Γ A -- base type
    Π : ∀ {Γ A} {B : Σ A → Set0} → (Ty Γ A) → (Ty (Σ A) B) → Ty Γ (\ θ → (x : A θ) → (B (θ , x)))
    id : ∀ {Γ A} (M1 M2 : Tm Γ A) → Ty Γ (\ x -> interp M1 x == interp M2 x)

  data Tm where
    -- the last variable in the context
    v    : ∀ {Γ} {A : Γ -> Set0} 
         → Tm (Σ A) (\ p -> A (fst p))
    -- weakening will let you access other variables
    w    : ∀ {Γ} {A : Γ -> Set0} {B : Σ A → Set0} → Tm (Σ A) B → Tm (Σ B) (\ x -> B (fst x))
    lam  : ∀ {Γ A B} 
         → Ty Γ A → Tm (Σ A) B 
         → Tm Γ (\ x -> (y : A x) → B (x , y))
    app  : ∀ {Γ A} {B : Σ A → Set0} 
         → Tm Γ (\ x -> (y : A x) → B (x , y)) 
         → (M : Tm Γ A) 
         → Tm Γ (\ x -> B (x , interp M x))
    ref : ∀ {Γ A} (M : Tm Γ A) → Tm Γ (\ x -> interp M x == interp M x) 
    trnpt : ∀ {Γ A} {C : Σ A → Set0} 
         → (Ty (Σ A) C) → (M1 M2 : Tm Γ A) (P : Tm Γ (\ x -> interp M1 x == interp M2 x))
         → Tm Γ (\ x -> C(x , interp M1 x))
         → Tm Γ (\ x -> C(x , interp M2 x))
    lam=  : ∀ {Γ A B} → Ty Γ A → Ty (Σ A) B →
           (f g : Tm Γ (\ x -> (y : A x) → B (x , y)))
           (α : Tm (Σ A) (\ p -> interp f (fst p) (snd p) == interp g (fst p) (snd p)))
           → Tm Γ (\ x -> interp f x == interp g x)

  interp v θ = snd θ
  interp (w M) θ = interp M (fst θ)
  interp (lam A M) θ = λ x → interp M (θ , x)
  interp (app M N) θ = (interp M θ) (interp N θ)
  interp (ref M) θ = refl
  interp (trnpt {_}{_}{C} _ _ _ P N) θ = transport (\ y -> C (θ , y)) (interp P θ) (interp N θ) 
  interp (lam= _ _ f g α) θ = λ= (λ y → interp α (θ , y))

