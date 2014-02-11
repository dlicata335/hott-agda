module misc.TTinTT2 (SomeType : Set0) where

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


  -- technical wrinkle: we first define a universe of *types we will interpret into*
  -- in order to avoid using an inductive family indexed by Sets
  -- if you wanted to do the same construction in U1, you would
  -- need an inductive family indexed by a datatype that *contains* Sets,
  -- but I don't think you would be non-uniform in the Set part?
  -- FIXME: think through whether this works

  data U : Set0 
  El : U → Set0

  data U where
     `b : U
     `Π : (A : U) → (El A -> U) -> U
     `Σ : (A : U) → (El A -> U) -> U 
     `Id : (A : U) → El A → El A -> U

  El `b = SomeType
  El (`Π A B) = (x : El A) → El (B x)
  El (`Σ A B) = Σ \ (x :  El A) → El (B x)
  El (`Id A M N) = M == N
    


  {-
    Syntax of type theory and interpretation a la
      Outrageous but Meaningful Coindcidences.  
      Conor McBride
  -}


  -- syntax and its interpretation

  -- Ty Γ A represents a type of the object language which is well-formed
  -- in context Γ (think of this as ⟦ Γ' ⟧ where is the object language context)
  -- and denotes the type A
  data Ty : ∀ (Γ : U) (A : El Γ → U) → Set0


  -- Ty Γ A represents a term of the object language which is well-formed
  -- in context Γ (think of this as ⟦ Γ' ⟧ where is the object language context)
  -- and *has* the type A.  
  -- the interpretation of terms is given by the function 'interp' below,
  -- inductive-recursively.  
  data Tm : ∀ (Γ : U) (A :  El Γ -> U) → Set0

  interp  : ∀ {Γ} {A : El Γ -> U} → Tm Γ A → (θ : El Γ) → El (A θ)

  data Ty where
    b : ∀ {Γ} → Ty Γ (\ _ -> `b) -- base type
    Π : ∀ {Γ A} {B : El (`Σ Γ A) → U} → (Ty Γ A) → (Ty (`Σ Γ A) B) → Ty Γ (\ θ → `Π (A θ) (\ x -> B (θ , x)))
    id : ∀ {Γ A} (M1 M2 : Tm Γ A) → Ty Γ (\ x -> `Id (A x) (interp M1 x) (interp M2 x))

  data Tm where
    -- the last variable in the context
    v    : ∀ {Γ} {A : El Γ -> U} 
         → Tm (`Σ Γ A) (\ p -> A (fst p))
    -- weakening will let you access other variables
    w    : ∀ {Γ} {A : El Γ -> U} {B : El (`Σ Γ A) → U} → Tm (`Σ Γ A) B → Tm (`Σ (`Σ Γ A) B) (\ x -> B (fst x))
    lam  : ∀ {Γ A B} 
         → Ty Γ A → Tm (`Σ Γ A) B 
         → Tm Γ (\ x -> `Π (A x) (\ y → B (x , y)))
    app  : ∀ {Γ A} {B : El (`Σ Γ A) → U} 
         → Tm Γ (\ x -> `Π (A x) (\ y → B (x , y)))
         → (M : Tm Γ A) 
         → Tm Γ (\ x -> B (x , interp M x))
    ref : ∀ {Γ A} (M : Tm Γ A) → Tm Γ (\ x -> `Id (A x) (interp M x) (interp M x))
    trnpt : ∀ {Γ A} {C : El (`Σ Γ A) → U} 
         → (Ty (`Σ Γ A) C) → (M1 M2 : Tm Γ A) (P : Tm Γ (\ x -> `Id (A x) (interp M1 x) (interp M2 x)))
         → Tm Γ (\ x -> C(x , interp M1 x))
         → Tm Γ (\ x -> C(x , interp M2 x))
    lam=  : ∀ {Γ A B} → Ty Γ A → Ty (`Σ Γ A) B →
           (f g : Tm Γ (\ x -> `Π (A x) (\ y → B (x , y))))
           (α : Tm (`Σ Γ A) (\ p -> `Id (B _) (interp f (fst p) (snd p)) (interp g (fst p) (snd p))))
           → Tm Γ (\ x -> `Id (`Π (A x) (\y -> B (x , y))) (interp f x) (interp g x))

  interp v θ = snd θ
  interp (w M) θ = interp M (fst θ)
  interp (lam A M) θ = λ x → interp M (θ , x)
  interp (app M N) θ = (interp M θ) (interp N θ)
  interp (ref M) θ = refl
  interp (trnpt {_}{_}{C} _ _ _ P N) θ = transport (\ y -> El (C (θ , y))) (interp P θ) (interp N θ) 
  interp (lam= _ _ f g α) θ = λ= (λ y → interp α (θ , y))

