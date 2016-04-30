{-# OPTIONS --type-in-type #-}

open import lib.Prelude

module misc.Retraction where

 record Retraction (A B : Type) : Type where
   constructor retraction
   field
     f : A → B
     g : B → A
     β : (y : B) → Path (f (g y)) y

 record Functor (T : Type → Type) : Type where
   constructor functor
   field
     arr    : ∀ {A B} → (A → B) → T A → T B
     ident  : ∀ {A} → arr{A} (\ x → x) == \ x → x
     comp   : ∀ {A B C f g} → arr{B}{C} g o arr{A}{B} f  == arr (g o f)

 record Monad (T : Type → Type) (FT : Functor T) : Type where
   constructor monad
   field
     return : ∀ {A} → A → T A
     _>>=_  : ∀ {A B} → T A → (A → T B) → T B
     -- laws


 r→ : ∀ {A A' B B'} → Retraction A A' → Retraction B B' → Retraction (A → B) (A' → B')
 r→ (retraction fa ga βa) (retraction fb gb βb) = 
   retraction (λ f a' → fb (f (ga a'))) 
              (λ f' a → gb (f' (fa a)))
              (λ f' → λ≃ (λ a' → ap f' (βa a') ∘ βb _))

 r× : ∀ {A A' B B'} → Retraction A A' → Retraction B B' → Retraction (A × B) (A' × B')
 r× (retraction fa ga βa) (retraction fb gb βb) = 
   retraction (λ p → fa (fst p) , fb (snd p)) (λ p → ga (fst p) , gb (snd p)) (λ p → pair×≃ (βa (fst p)) (βb (snd p)))

 rid : ∀ {A} → Retraction A A
 rid = retraction (λ x → x) (λ x → x) (λ _ → id)

 r· : ∀ {A B C} → Retraction A B → Retraction B C → Retraction A C
 r· (retraction fa ga βa) (retraction fb gb βb) = 
   retraction (fb o fa) (ga o gb) (λ y → βb _ ∘ ap fb (βa (gb y)))

 rfunc : ∀ {A B T} → Functor T → Retraction A B → Retraction (T A) (T B)
 rfunc (functor farr fid fcomp) (retraction f g β) = 
   retraction (farr f) (farr g) (λ y → (ap≃ fid ∘ ap (λ h → farr h y) (λ≃ β)) ∘ ap≃ fcomp {y})

 module C× (C : Type) (c0 : C) (c1 : C) (mc : C → C → C) where

  T : Type → Type
  T A = C × A

  TF : Functor T
  TF = functor (λ f p → fst p , f (snd p)) id id

  TM : Monad T TF
  TM = monad (λ x → c0 , x) (λ a f → mc (fst a) (fst (f (snd a))) , snd (f (snd a)))

  rT : ∀ {A} → Retraction (T A) A
  rT = retraction snd (λ x → c0 , x) (λ _ → id)

  addc : T Unit
  addc = (c1 , <>)


 module Monadic (B : Type) (b0 : B)

                -- FIXME: should be true in more generality, but 
                --       special casing the proof of the main theorem for now
                --       
                -- (T : Type → Type)
                -- (TF : Functor T)
                -- (TM : Monad T TF)
                -- (rT : ∀ {A} → Retraction (T A) A) 
                -- -- FIXME nt laws?
                (C : Type) (c0 : C) (c1 : C) (mc : C → C → C)

                where

  open C× C c0 c1 mc

  open Monad TM

  {- de Bruijn indices are representd as proofs that 
     an element is in a list -}
  data _∈_ {A : Set} : (x : A) (l : List A) → Set where -- type \in
    i0 : {x : A} {xs : List A} → x ∈ x :: xs
    iS : {x y : A} {xs : List A} → x ∈ xs → x ∈ y :: xs

  {- types of the STLC -}
  data Tp : Set where
    b : Tp             -- uninterpreted base type
    _⇒_ : Tp → Tp → Tp -- type \=>

  {- contexts are lists of Tp's -}
  Ctx = List Tp
  _,,_ : Ctx → Tp → Ctx
  Γ ,, τ = τ :: Γ

  infixr 10 _⇒_
  infixr 9 _,,_
  infixr 8 _⊢_ -- type \entails

  {- Γ ⊢ τ represents a term of type τ in context Γ -}
  data _⊢_ (Γ : Ctx) : Tp → Set where
    c   : Γ ⊢ b -- some constant of the base type
    v   : {τ : Tp} 
        → τ ∈ Γ
        → Γ ⊢ τ 
    lam : {τ1 τ2 : Tp} 
        → Γ ,, τ1 ⊢ τ2
        → Γ ⊢ τ1 ⇒ τ2
    app : {τ1 τ2 : Tp} 
        → Γ ⊢ τ1 ⇒ τ2 
        → Γ ⊢ τ1 
        → Γ ⊢ τ2


  -- direct semantics

  [[_]] : Tp → Type
  [[ b ]] = B
  [[ τ1 ⇒ τ2 ]] = [[ τ1 ]] → [[ τ2 ]]

  [[_]]c : Ctx → Type
  [[ [] ]]c = Unit
  [[ τ :: Γ ]]c = [[ Γ ]]c × [[ τ ]]

  [[_]]e : ∀ {Γ τ} → Γ ⊢ τ → [[ Γ ]]c → [[ τ ]]
  [[_]]e c θ = b0
  [[_]]e (v i0) θ = snd θ
  [[_]]e (v (iS x)) θ = [[ v x ]]e (fst θ)
  [[_]]e (lam e) θ = λ x → [[ e ]]e (θ , x)
  [[_]]e (app e1 e2) θ = [[ e1 ]]e θ ([[ e2 ]]e θ)


  -- monadic semantics

  <<_>> : Tp → Type
  << b >> = B
  << τ1 ⇒ τ2 >> = << τ1 >> → T << τ2 >>

  <<_>>c : Ctx → Type
  << [] >>c = Unit
  << τ :: Γ >>c = << Γ >>c × << τ >>

  <<_>>e : ∀ {Γ τ} → Γ ⊢ τ → << Γ >>c → T << τ >>
  <<_>>e c θ = return b0
  <<_>>e (v i0) θ = return (snd θ)
  <<_>>e (v (iS x)) θ = << v x >>e (fst θ)
  <<_>>e (lam e) θ = return (λ x → << e >>e (θ , x))
  <<_>>e (app e1 e2) θ = addc >>= (\ _ → (<< e1 >>e θ) >>= (λ f →(<< e2 >>e θ) >>= (λ x → f x)))

  -- retraction between the two

  -- there are two ways to do this -- same by naturality?
  retTpost : ∀ {A B} → Retraction A B → Retraction (T A) B
  retTpost r = r· (rfunc TF r) rT

  retTpre : ∀ {A B} → Retraction A B → Retraction (T A) B
  retTpre r = r· rT r

  ret : ∀ τ → Retraction << τ >> [[ τ ]]
  ret b = rid
  ret (τ ⇒ τ₁) = r→ (ret τ) (retTpre (ret τ₁))

  retc : ∀ Γ → Retraction << Γ >>c [[ Γ ]]c
  retc [] = rid
  retc (τ :: Γ) = r× (retc Γ) (ret τ)

  -- up to here works for any T with any retraction T A → A


  Irrel : (τ : Tp) → << τ >> → Set
  Irrel b _ = Unit
  Irrel (τ1 ⇒ τ2) f = (x : << τ1 >>) → Irrel τ1 x → Irrel τ2 (snd (f x)) × 
                        (Retraction.f (retTpost (ret τ2)) (f (Retraction.g (ret τ1) (Retraction.f (ret τ1) x)))
                          == Retraction.f (retTpost (ret τ2)) (f x))

  Irrelc : (Γ : Ctx) → << Γ >>c → Set
  Irrelc [] θ = Unit
  Irrelc (τ :: Γ) θ = Irrelc Γ (fst θ) × Irrel τ (snd θ)

  IrrelMapC : (Γ : Ctx) (τ : Tp) → (<< Γ >>c → T << τ >>) → Set
  IrrelMapC Γ τ f = 
    (θ : << Γ >>c) → Irrelc Γ θ → Irrel τ (snd (f θ)) × 
      (Retraction.f (retTpost (ret τ)) (f (Retraction.g (retc Γ) (Retraction.f (retc Γ) θ))) == Retraction.f (retTpost (ret τ)) (f θ))

  irrelg : ∀ τ x → Irrel τ (Retraction.g (ret τ) x)
  irrelg b x = <>
  irrelg (τ1 ⇒ τ2) f x ix = (irrelg τ2 _) , (ap (λ h → Retraction.f (ret τ2) (Retraction.g (ret τ2) (f h))) (Retraction.β (ret τ1) _))

  irrelgc : ∀ Γ θ → Irrelc Γ (Retraction.g (retc Γ) θ)
  irrelgc [] θ = <>
  irrelgc (τ :: Γ) θ = (irrelgc Γ (fst θ)) , irrelg τ (snd θ)

  irrel :  ∀ {Γ τ} (e : Γ ⊢ τ) → IrrelMapC Γ τ (<< e >>e)
  irrel c θ _ = <> , id
  irrel {τ = τ} (v i0) θ iθ = snd iθ , Retraction.β (ret τ) _ 
  irrel (v (iS x)) θ iθ = irrel (v x) (fst θ) (fst iθ) 
  irrel {Γ} {τ = τ1 ⇒ τ2} (lam e) θ iθ =
    (λ x ix → (fst (irrel e (θ , x) (iθ , ix))) , 
                snd (irrel e (θ , x) (iθ , ix)) ∘ 
                ap (λ h → Retraction.f (ret τ2) (snd (<< e >>e (Retraction.g (retc Γ) (Retraction.f (retc Γ) θ) , Retraction.g (ret τ1) h)))) (Retraction.β (ret τ1) _) ∘
                ! (snd (irrel e (θ , Retraction.g (ret τ1) (Retraction.f (ret τ1) x)) (iθ , irrelg τ1 _)))) , 
    λ≃ (λ x → snd (irrel e (θ , Retraction.g (ret τ1) x) (iθ , irrelg τ1 x)) ∘
          ap (λ h → Retraction.f (ret τ2) (snd (<< e >>e (Retraction.g (retc Γ) (Retraction.f (retc Γ) θ) , Retraction.g (ret τ1) h))))
             (! (Retraction.β (ret τ1) _))) 
  irrel {Γ = Γ} (app {τ1}{τ2} e1 e2) θ iθ with (irrel e1 θ iθ) | irrel e2 θ iθ | (irrel e1 (Retraction.g (retc Γ) (Retraction.f (retc Γ) θ)) (irrelgc Γ _)) | (irrel e2 (Retraction.g (retc Γ) (Retraction.f (retc Γ) θ)) (irrelgc Γ _))
  ... | p | q | p' | q'  = (fst (fst p _ (fst q))) , 
                 snd (fst p _ (fst q)) ∘ 
                 ap≃ (snd p) ∘ 
                 ap (λ h → Retraction.f (ret τ2) (snd (snd (<< e1 >>e (Retraction.g (retc Γ) (Retraction.f (retc Γ) θ))) (Retraction.g (ret τ1) h))))
                    (snd q) ∘
                 ! (snd (fst p' _ (fst q'))) 

  thm : ∀ {Γ τ} (e : Γ ⊢ τ) (θ : _) → (Retraction.f (r→ (retc Γ) (retTpre (ret τ))) << e >>e) θ == [[ e ]]e θ
  thm c θ = id
  thm {τ = τ} (v i0) θ = Retraction.β (ret τ) (snd θ)
  thm (v (iS x)) θ = thm (v x) (fst θ)
  thm (lam e) θ = λ≃ (λ x → thm e (θ , x))
  thm {Γ = Γ} (app{τ1}{τ2} e1 e2) θ = 
    ap2 (λ f x → f x) (thm e1 θ) (thm e2 θ) ∘ 
    ! (snd (fst (irrel e1 (Retraction.g (retc Γ) θ) (irrelgc Γ θ)) (snd (<< e2 >>e (Retraction.g (retc Γ) θ))) (fst (irrel e2 (Retraction.g (retc Γ) θ) (irrelgc Γ θ)))))  

