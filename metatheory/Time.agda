{-# OPTIONS --type-in-type #-}

open import lib.Prelude

module metatheory.Time where

  data Tp : Set where
    nat : Tp
    _⇒_ : Tp → Tp → Tp

  Ctx = List Tp

  data _∈_ {A : Set} : A -> List A -> Type where
      i0 : {x : A}   {xs : List A} -> x ∈ (x :: xs )
      iS : {x y : A} {xs : List A} -> y ∈ xs -> y ∈ (x :: xs)
  infix 10 _∈_

  data Tm (Γ : Ctx) : Tp → Type where
    const : Nat → Tm Γ nat
    1+    : Tm Γ nat → Tm Γ nat
    iter  : {C : Tp} → Tm Γ nat → Tm Γ C → Tm (C :: nat :: Γ) C → Tm Γ C 
    v   : {A : Tp} → A ∈ Γ → Tm Γ A
    lam : ∀ {A B} → Tm (A :: Γ) B → Tm Γ (A ⇒ B)
    app : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B

  record Monad (T : Type → Type) : Type where
   field
    return : ∀ {A} → A → T A
    bind   : ∀ {A B} → T A → (A → T B) → T B
    lid    : ∀ {A B} → (x : A) (f : A → T B) → bind (return x) f == f x
    rid    : ∀ {A} → (x : T A) → bind x (\ y -> return y) == x
    assoc  : ∀ {A B C} → (x : T A) (f : A → T B) (g : B → T C)
           → bind (bind x f) g == bind x (\ y -> bind (f y) g)

  -- just for reference, here is a 
  -- standard call-by-value monadic interpretation.
  -- this is not used below.
  module Interp (T : Type → Type) (M : Monad T) where
    open Monad M

    <<_>> : Tp → Type
    << nat >> = Nat
    << A ⇒ B >> = << A >> → T << B >>

    <<_>>c : Ctx → Type
    << Γ >>c = {A : Tp} → A ∈ Γ → << A >>

    extend : ∀ {Γ A} → << Γ >>c → << A >> → << A :: Γ >>c
    extend env x i0 = x
    extend env x (iS y) = env y

    miter : ∀ {C} → 
                  Nat
                → (T C)
                → (Nat → C → T C)
                → T C
    miter Z c0 c1 = c0 
    miter (S n) c0 c1 = bind (miter n c0 c1) (λ r → c1 n r)

    interp : ∀ {Γ A} → Tm Γ A → << Γ >>c → T << A >>
    interp (const n) env = return n
    interp (1+ n) env = bind (interp n env) (\ x -> return (S x))
    interp (iter e e0 e1) env =
      bind (interp e env) (\ x ->
      miter x (interp e0 env)
              (\ p r → interp e1 (extend (extend env p) r)))
    interp (v x) env = return (env x)
    interp (lam e) env = return (λ x → interp e (extend env x))
    interp (app e1 e2) env = 
                bind (interp e1 env) (λ f → 
                bind (interp e2 env) (λ a → 
                f a))
  

  -- some operations, including application, have time effects
  module InterpTime (T : Type → Type) (M : Monad T) (step : T Unit) where
    open Monad M

    <<_>> : Tp → Type
    << nat >> = Nat
    << A ⇒ B >> = << A >> → T << B >>

    <<_>>c : Ctx → Type
    << Γ >>c = {A : Tp} → A ∈ Γ → << A >>

    extend : ∀ {Γ A} → << Γ >>c → << A >> → << A :: Γ >>c
    extend env x i0 = x
    extend env x (iS y) = env y

    -- monadic iteration, charging one step in each case
    miter : ∀ {C} → Nat → (T C) → (Nat → C → T C) → T C
    miter Z c0 c1 = bind step (\ _ -> c0)
    miter (S n) c0 c1 = bind step (\ _ -> bind (miter n c0 c1) (λ r → c1 n r))

    -- application has the effect of taking a step 
    interp : ∀ {Γ A} → Tm Γ A → << Γ >>c → T << A >>
    interp (const n) env = bind step (\ _ -> return n)
    interp (1+ n) env = bind (interp n env) (\ x -> 
                        bind step (\ y -> 
                        return (S x)))
    interp (iter e e0 e1) env = 
      bind (interp e env) (\ x ->
      miter x (interp e0 env)
              (\ p r → interp e1 (extend (extend env p) r)))
    interp (v x) env = return (env x)
    interp (lam e) env = return (λ x → interp e (extend env x))
    interp (app e1 e2) env = 
                bind (interp e1 env) (λ f → 
                bind (interp e2 env) (λ a → 
                bind step (λ _ ->
                f a)))

  
  module MonoidMonad (M : Type) (Mon : Monoid M) where
    open Monoid Mon renaming (`1 to `0 ; _⊙_ to _+_) 

    M× : Monad (\ B -> M × B)
    M× = record { return = λ x → `0 , x; 
                  bind = λ {(m1 , x1) f → m1 + fst (f x1) , snd (f x1)}; 
                  lid = λ x f → ap (λ z → z , snd (f x)) unitl; 
                  rid = λ x → ap (λ z → z , snd x) unitr; 
                  assoc = λ x f g → ap (λ z → z , snd (g (snd (f (snd x))))) assoc }

  Nat+ : Monoid Nat
  Nat+ = record { _⊙_ = NatM._+_; `1 = 0; assoc = λ {x} {y} {z} → ! (NatM.+-assoc x y z); unitl = id; unitr = λ {x} → ! (NatM.+-rh-Z x) }

  TimeMonad : Monad (\ A → Nat × A) 
  TimeMonad = MonoidMonad.M× _ Nat+

  step : Nat × Unit
  step = (1 , <>)

  module Time = InterpTime _ TimeMonad step

  module Recurrence where
    open NatM using (_+_)

    for-zero : ∀ {B : Type} {n0 : Nat} {b0 : B} {n1 : Nat → B → Nat} {b1 : Nat → B → B}
         → fst (Time.miter 0 (n0 , b0) (\ p r → n1 p r , b1 p r)) == S n0
    for-zero = id

    for-S : ∀ {B : Type} {x : Nat} {n0 : Nat} {b0 : B} {n1 : Nat → B → Nat} {b1 : Nat → B → B}
         → fst (Time.miter (S x) (n0 , b0) (\ p r → n1 p r , b1 p r)) == 
           let r = (Time.miter x (n0 , b0) (\ p r → n1 p r , b1 p r)) in
             1 + ((fst r) + (n1 x (snd r)))
    for-S {b1 = b1} = id

    {- so Time.miter x (n0 , b0) (\ p r → n1 p r , b1 p r) 
       defines a function 

       T(x) by
       T(x) = (Tc(x) , Tp(x))

       Tp(x) by
       Tp(0) = b0
       Tp(x+1) = b1 x Tp(x)

       Tc(x) by
       Tc(0) = 1 + n0
       Tc(x+1) = 1 + Tc(x) + n1 x Tp(x)
    -}

  idfunc : Tm [] (nat ⇒ nat) 
  idfunc = lam (v i0)

  example : Tm [] nat
  example = (app idfunc (const 4))

  example' : Tm [] nat
  example' = (app idfunc (1+ (1+ (1+ (1+ (const 0))))))

  plus : ∀ {Γ} → Tm Γ (nat ⇒ (nat ⇒ nat))
  plus = lam (lam (iter (v (iS i0)) (v i0) (1+ (v i0))))

  mult : Tm [] (nat ⇒ (nat ⇒ nat))
  mult = lam (lam (iter (v (iS i0)) (const 0) (app (app plus (v (iS (iS i0)))) (v i0))))

  appplus : Tm [] nat
  appplus = app (app plus (const 2)) (const 3)

  appmult : Tm [] nat
  appmult = app (app mult (const 3)) (const 7)

  -- summorial x + (1+ x)
  -- same recursion structure as insertion sort
  summorial1 : Tm [] (nat ⇒ nat)
  summorial1 = lam (iter (v i0) (const 0) (app (app plus (v i0)) (1+ (v (iS i0)))))

  -- 1+ x + summorial x
  -- complexity refers to the size of the predecessor
  summorial2 : Tm [] (nat ⇒ nat)
  summorial2 = lam (iter (v i0) (const 0) (app (app plus (1+ (v (iS i0)))) (v i0)))

  test : Time.interp example == (\ _ -> (2 , 4))
  test = id
  
  test2 : Nat → _
  test2 x = Time.miter (S x) (0 , 0) (\ p r -> (1 , 1))

{-
plus

λ env →
  0 ,
  (λ x →
     0 ,
     (λ x₁ →
        fst
        (InterpTime.miter x (0 , x₁) (λ p r → 1 , S r))
        ,
        snd
        (InterpTime.miter x (0 , x₁) (λ p r → 1 , S r))))

so

Tc(x) where x is the size of the first number is defined by
Tc(0) = 1
Tc(1+x) = 2 + Tc(x)
Note that this is independent of x₁, the size of the second number.
-}  

{-
mult

λ env →
  0 ,
  (λ x →
     0 ,
     (λ x₁ →
        fst
        (InterpTime.miter x (1 , 0)
         (λ p r →
            S
            (S
             (fst
              (InterpTime.miter x₁ (0 , r) (λ p₁ r₁ → 1 , S r₁))))
            ,
            snd
            (InterpTime.miter x₁ (0 , r) (λ p₁ r₁ → 1 , S r₁))))
        ,
        snd
        (InterpTime.miter x (1 , 0)
         (λ p r →
            S
            (S
             (fst
              (InterpTime.miter x₁ (0 , r) (λ p₁ r₁ → 1 , S r₁))))
            ,
            snd
            (InterpTime.miter x₁ (0 , r) (λ p₁ r₁ → 1 , S r₁))))))

So 

-- recurrence for plus
Sc(x₁)
Sc(0) = 1 
Sc(1+x) = 1 + Sc(x) + 1

Tc(x,x₁) 
Tc(0,x₁) = 2
Tc(1+x,x₁) = 3 + Tc(x) + Sc(x₁)

-}

{- summorial 1: depends on the potential of the recursive call

λ env →
  0 ,
  (λ x →
     fst
     (InterpTime.miter x (1 , 0)
      (λ p r →
         S
         (S
          (S
           (fst
            (InterpTime.miter r (0 , S p) (λ p₁ r₁ → 1 , S r₁)))))
         ,
         snd
         (InterpTime.miter r (0 , S p) (λ p₁ r₁ → 1 , S r₁))))
     ,
     snd
     (InterpTime.miter x (1 , 0)
      (λ p r →
         S
         (S
          (S
           (fst
            (InterpTime.miter r (0 , S p) (λ p₁ r₁ → 1 , S r₁)))))
         ,
         snd
         (InterpTime.miter r (0 , S p) (λ p₁ r₁ → 1 , S r₁)))))

-- recurrence for plus
Sc(y)
Sc(0) = 1
Sc(1+y) = 2 + Sc(y)

Tp(x)
Tp(0) = 0
Tp(1+x) = TODO

Tc(x)
Tc(0) = 2
Tc(1+x) = 1 + Tc(x) + Sc(Tp(x))

-}

{- summorial 2

λ env →
  0 ,
  (λ x →
     fst
     (InterpTime.miter x (1 , 0)
      (λ p r →
         S
         (S
          (S
           (S
            (fst
             (InterpTime.miter p (0 , r) (λ p₁ r₁ → 1 , S r₁))
             NatM.+ 1))))
         ,
         S
         (snd
          (InterpTime.miter p (0 , r) (λ p₁ r₁ → 1 , S r₁)))))
     ,
     snd
     (InterpTime.miter x (1 , 0)
      (λ p r →
         S
         (S
          (S
           (S
            (fst
             (InterpTime.miter p (0 , r) (λ p₁ r₁ → 1 , S r₁))
             NatM.+ 1))))
         ,
         S
         (snd
          (InterpTime.miter p (0 , r) (λ p₁ r₁ → 1 , S r₁))))))

-}
