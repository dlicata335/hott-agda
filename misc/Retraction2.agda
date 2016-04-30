{-# OPTIONS --type-in-type #-}

open import lib.Prelude

module misc.Retraction2 where

 record Retraction (A B : Type) : Type where
   constructor retraction
   field
     f : A → B
     g : B → A
     β : (y : B) → Path (f (g y)) y
   gf : A → A
   gf = g o f
   

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
                --       special casing T for now
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


  -- monadic semantics with independence: like retraction bet glued together 

  retTpost : ∀ {A B} → Retraction A B → Retraction (T A) B
  retTpost r = r· (rfunc TF r) rT

  Sem : Tp → Type
  Sem τ = Σ \ (A : Type) → Retraction A [[ τ ]]

  Map : ∀ (τ1 τ2 : Tp) → Sem τ1 → Sem τ2 → Type
  Map _ _ (A , rA) (B , rB) = 
    Σ (λ (f : A → T B) → 
         (a : A) → Retraction.f (retTpost rB) (f a) == Retraction.f (retTpost rB) (f (Retraction.gf rA a)))

  <<_>> : (τ : Tp) → Sem τ
  << b >> = B , rid
  << τ1 ⇒ τ2 >> = 
    (Map τ1 τ2 << τ1 >> << τ2 >>) , 
    retraction (λ m → Retraction.f (r→ (snd << τ1 >>) (retTpost (snd << τ2 >>))) (fst m)) 
               (λ f → Retraction.g (r→ (snd << τ1 >>) (retTpost (snd << τ2 >>))) f , 
                      (λ a → ap (λ h → Retraction.f (snd << τ2 >>) (Retraction.g (snd << τ2 >>) (f h))) 
                                (! (Retraction.β (snd << τ1 >>) _))))
               (λ _ → Retraction.β (r→ (snd << τ1 >>) (retTpost (snd << τ2 >>))) _)

  SemC : Ctx → Type
  SemC Γ = Σ \ (A : Type) → Retraction A [[ Γ ]]c

  <<_>>c : (Γ : Ctx) → SemC Γ
  << [] >>c = Unit , rid
  << τ :: Γ >>c = (fst << Γ >>c × fst << τ >>) , r× (snd << Γ >>c) (snd << τ >>) 

  MapC : ∀ (Γ : Ctx) (τ : Tp) → SemC Γ → Sem τ → Type
  MapC _ _ (SΓ , rΓ) (Sτ , rτ) = Σ (λ (f : SΓ → T Sτ) → (θ : SΓ) → Retraction.f (retTpost rτ) (f θ) == Retraction.f (retTpost rτ) (f (Retraction.gf rΓ θ)))
  
  <<_>>e : ∀ {Γ τ} → Γ ⊢ τ → MapC Γ τ (<< Γ >>c) (<< τ >>)
  <<_>>e c = (λ _ → return b0) , (λ _ → id) 
  <<_>>e {τ = τ} (v i0) = (λ θ → return (snd θ)) , (λ θ → ! (Retraction.β (snd << τ >>) _)) 
  <<_>>e (v (iS x)) = (λ θ → fst << v x >>e (fst θ)) , (λ θ → snd << v x >>e (fst θ)) 
  <<_>>e {Γ = Γ} (lam{τ1}{τ2} e) = 
    (λ θ → return ((λ x → fst << e >>e (θ , x)) , 
                   (λ x → ! (snd << e >>e (θ , Retraction.g (snd << τ1 >>) (Retraction.f (snd << τ1 >>) x))) ∘ 
                           ap (λ h → Retraction.f (snd << τ2 >>) (snd (fst << e >>e (Retraction.g (snd << Γ >>c) (Retraction.f (snd << Γ >>c) θ) , Retraction.g (snd << τ1 >>) h))))
                              (! (Retraction.β (snd << τ1 >>) _)) 
                           ∘ snd << e >>e (θ , x)))) , 
                       (λ θ → λ≃ (λ x → ap (λ h → Retraction.f (snd << τ2 >>) (snd (fst << e >>e (Retraction.g (snd << Γ >>c) (Retraction.f (snd << Γ >>c) θ) , Retraction.g (snd << τ1 >>) h))))
                                            (Retraction.β (snd << τ1 >>) x)
                                         ∘ snd << e >>e (θ , Retraction.g (snd << τ1 >>) x))) 
  <<_>>e {Γ = Γ} (app{τ1}{τ2} e1 e2) = 
    (\ θ → addc >>= (\ _ → (fst << e1 >>e θ) >>= (λ f →(fst << e2 >>e θ) >>= (λ x → fst f x)))) 
    , (λ θ →  ! (snd (snd (fst << e1 >>e (Retraction.g (snd << Γ >>c) (Retraction.f (snd << Γ >>c) θ)))) _) ∘
                 ap (λ h → Retraction.f (snd << τ2 >>) (snd (fst (snd (fst << e1 >>e (Retraction.g (snd << Γ >>c) (Retraction.f (snd << Γ >>c) θ)))) (Retraction.g (snd << τ1 >>) h))))
                    (snd << e2 >>e θ)
                ∘ ap≃ (snd << e1 >>e θ) 
                ∘ snd (snd (fst << e1 >>e θ)) (snd (fst << e2 >>e θ))) 


  thm2 : ∀ {Γ τ} (e : Γ ⊢ τ) (θ : _) 
       → (Retraction.f (r→ (snd << Γ >>c) (retTpost (snd << τ >>))) (fst << e >>e)) θ == [[ e ]]e θ
  thm2 c θ = id
  thm2 {τ = τ} (v i0) θ = Retraction.β (snd << τ >>) (snd θ)
  thm2 (v (iS x)) θ = thm2 (v x) (fst θ)
  thm2 (lam e) θ = λ≃ (λ x → thm2 e (θ , x))
  thm2 {Γ = Γ} (app e1 e2) θ = ap2 (λ f x → f x) (thm2 e1 θ) (thm2 e2 θ) ∘ snd (snd (fst << e1 >>e (Retraction.g (snd << Γ >>c) θ))) _ 
