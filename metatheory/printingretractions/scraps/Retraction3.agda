{-# OPTIONS --type-in-type #-}

open import lib.Prelude hiding (wrap)

module misc.Retraction3 where

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

 module C× (C : Type) (c0 : C) (c1 : C) (mc : C → C → C) where

  T : Type → Type
  T A = C × A

  TF : Functor T
  TF = functor (λ f p → fst p , f (snd p)) id id

  TM : Monad T TF
  TM = monad (λ x → c0 , x) (λ a f → mc (fst a) (fst (f (snd a))) , snd (f (snd a)))

  -- rT : ∀ {A} → Retraction (T A) A
  -- rT = retraction snd (λ x → c0 , x) (λ _ → id)

  addc : T Unit
  addc = (c1 , <>)

 module Monadic (B : Type) (b0 : B)
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


  -- just the cost part

  <<_>>cst : Tp → Type
  << b >>cst = Unit
  << τ1 ⇒ τ2 >>cst = ([[ τ1 ]] → << τ1 >>cst → C × << τ2 >>cst)

  <<_>>cstc : Ctx → Type
  << [] >>cstc = Unit
  << τ :: Γ >>cstc = << Γ >>cstc × << τ >>cst

  <<_>>split : ∀ {Γ τ} → Γ ⊢ τ → ([[ Γ ]]c × << Γ >>cstc) → C × << τ >>cst
  <<_>>split c (θ , θc) = return <>
  <<_>>split (v i0) (θ , θc) = return (snd θc)
  <<_>>split (v (iS x)) (θ , θc) = << v x >>split ((fst θ) , (fst θc))
  <<_>>split (lam e) (θ , θc) = return (λ x cx → << e >>split ((θ , x) , (θc , cx)))
  <<_>>split (app e1 e2) (θ , θc) = 
    addc >>= (\ _ →  
    (<< e1 >>split (θ , θc)) >>= (λ ce1 → 
    (<< e2 >>split (θ , θc)) >>= (λ ce2 → 
    ce1 ([[ e2 ]]e θ) ce2)))

  default : ∀ τ → << τ >>cst 
  default b = <>
  default (τ1 ⇒ τ2) = λ _ _ → {!!} , default τ2 -- arbitrary

  -- relationship between the two

  mutual 
    split : ∀ τ → << τ >> → [[ τ ]] × << τ >>cst
    split b cpot = cpot , <>
    split (τ1 ⇒ τ2) cpot = (λ pot → fst (split τ2 (snd (cpot (merged τ1 pot))))) , 
                           (λ pot1 cpot1 → (fst (cpot (merge τ1 pot1 cpot1))) , (snd (split τ2 (snd (cpot (merge τ1 pot1 cpot1))))))

    merged : ∀ τ → [[ τ ]] → << τ >>
    merged τ pot = merge τ pot (default τ)

    merge : ∀ τ → [[ τ ]] → << τ >>cst → << τ >>
    merge b pot cost = pot
    merge (τ1 ⇒ τ2) pot cost = (λ x → fst (cost (fst (split τ1 x)) (snd (split τ1 x))) , 
                                merge τ2 (pot (fst (split τ1 x))) (snd (cost (fst (split τ1 x)) (snd (split τ1 x)))))
 
  merge' : ∀ τ → ([[ τ ]] × << τ >>cst) → << τ >>
  merge' τ p = merge τ (fst p) (snd p)

  splitc : ∀ Γ → << Γ >>c → [[ Γ ]]c × << Γ >>cstc 
  splitc [] θ = <> , <>
  splitc (τ :: Γ) θ = ((fst (splitc Γ (fst θ))) , (fst (split τ (snd θ)))) , 
                      (snd (splitc Γ (fst θ)) , snd (split τ (snd θ)))

  mergec : ∀ Γ → [[ Γ ]]c → << Γ >>cstc → << Γ >>c 
  mergec [] pot cst = <>
  mergec (τ :: Γ) pot cst = mergec Γ (fst pot) (fst cst) , merge τ (snd pot) (snd cst)

  mergec' : ∀ Γ → ([[ Γ ]]c × << Γ >>cstc) → << Γ >>c
  mergec' Γ p = mergec Γ (fst p) (snd p)

  split-merge1 : (τ : Tp) (p : [[ τ ]]) (c : << τ >>cst) → fst (split τ (merge τ p c)) == p
  split-merge1 b p cst = id
  split-merge1 (τ1 ⇒ τ2) p cst = λ≃ (λ pot → 
    split-merge1 τ2 (p pot) _ ∘ 
    ap (λ h → fst (split τ2 (merge τ2 (p h) (snd (cst (fst (split τ1 (merge τ1 pot (default τ1)))) (snd (split τ1 (merge τ1 pot (default τ1)))))))))
       (split-merge1 τ1 pot _))

  mutual
    split-merge2 : (τ : Tp) (p : [[ τ ]]) (c : << τ >>cst) → snd (split τ (merge τ p c)) == c
    split-merge2 b p cst = id
    split-merge2 (τ1 ⇒ τ2) p cst = λ≃ \ pot1 → λ≃ \ cpot1 → 
        ap2 _,_ (ap (λ h → fst (cst (fst h) (snd h))) (split-merge12 τ1 (pot1 , cpot1))) 
                (split-merge2 τ2 (p pot1) (snd (cst pot1 cpot1)) ∘ 
                 ap (λ h → snd (split τ2 (merge τ2 (p (fst h)) (snd (cst (fst h) (snd h))))))
                    (split-merge12 τ1 (pot1 , cpot1)))

    split-merge12 : (τ : Tp) (pc : _) → (split τ (merge' τ pc)) == pc
    split-merge12 τ pc = ap2 _,_ (split-merge1 τ _ _) (split-merge2 τ _ _)

  split-merge12c : (Γ : Ctx) (pc : _) → (splitc Γ (mergec' Γ pc)) == pc
  split-merge12c [] pc = id
  split-merge12c (τ :: Γ) pc = ap2 _,_ (ap2 _,_ (ap fst (split-merge12c Γ (fst (fst pc) , fst (snd pc))))
                                                (split-merge1 τ (snd (fst pc)) (snd (snd pc))))
                                       (ap2 _,_ (ap snd (split-merge12c Γ (fst (fst pc) , fst (snd pc)))) 
                                                (split-merge2 τ (snd (fst pc)) (snd (snd pc))))

  rett : (τ : Tp) → Retraction << τ >> ([[ τ ]] × << τ >>cst)
  rett τ = retraction (split τ) (merge' τ) (split-merge12 τ)

  retc : (Γ : Ctx) → Retraction << Γ >>c ([[ Γ ]]c × << Γ >>cstc)
  retc Γ = retraction (splitc Γ) (mergec' Γ) (split-merge12c Γ)

  -- potential part of the output is independent of the cost part of the input
  IndepMap : (τ1 τ2 : Tp) (r : << τ1 >> → << τ2 >>) →  Set
  IndepMap τ1 τ2 r = (p : [[ τ1 ]]) (c1 c2 : << τ1 >>cst) → 
                    fst (split τ2 (r (merge τ1 p c1))) == fst (split τ2 (r (merge τ1 p c2)))

  Indep : (τ : Tp) → << τ >> → Set
  Indep b p = Unit
  Indep (τ1 ⇒ τ2) f = IndepMap τ1 τ2 (snd o f) ×
                      ((x : << τ1 >>) → Indep τ1 x → Indep τ2 (snd (f x)))

  IndepC : (Γ : Ctx) → << Γ >>c → Set
  IndepC [] θ = Unit
  IndepC (τ :: Γ) θ = IndepC Γ (fst θ) × Indep τ (snd θ)
    
  IndepMapC : (Γ : Ctx) (τ : Tp) (r : << Γ >>c → << τ >>) →  Set
  IndepMapC Γ τ r = (p : [[ Γ ]]c) (c1 c2 : << Γ >>cstc) → 
                   fst (split τ (r (mergec Γ p c1))) == fst (split τ (r (mergec Γ p c2)))
 
  allindep : ∀ {Γ}{τ} (e : Γ ⊢ τ) 
             → IndepMapC Γ τ (snd o << e >>e) × 
               ( (θ : << Γ >>c) → IndepC Γ θ → Indep τ (snd (<< e >>e θ)))
  allindep c = (λ _ _ _ → id) , (λ _ _ → <>)
  allindep {τ = τ} (v i0) = (λ p c2 c3 → ! (split-merge1 τ _ _) ∘ split-merge1 τ _ _) , 
                           (λ _ iθ → snd iθ)
  allindep (v (iS x)) = (λ p c1 c2 → fst (allindep (v x)) (fst p) (fst c1) (fst c2)) ,
                        (λ θ iθ → snd (allindep (v x)) (fst θ) (fst iθ))
  allindep (lam{τ1}{τ2} e) = (λ p c1 c2 → λ≃ (λ px → fst (allindep e) (p , px) (c1 , default τ1) (c2 , default τ1))) , 
                            (λ θ iθ → (λ px c1 c2 → {!fst (allindep e) !}) , 
                                      (λ x ix → snd (allindep e) (θ , x) (iθ , ix)))
  allindep (app e e₁) = {!!}

  -- need LR here
  independent : {τ1 τ2 : Tp} (r : << τ1 >> → T << τ2 >>) (x : << τ1 >>) (c1 : << τ1 >>cst) →
             (fst (split τ2 (snd (r (merge τ1 (fst (split τ1 x)) c1)))))
          == (fst (split τ2 (snd (r x))))
  independent = {!!}

  merge-split : ∀ τ (x : << τ >>) → merge' τ (split τ x) == x
  merge-split b x = id
  merge-split (τ1 ⇒ τ2) r = λ≃ (λ x → ap2 _,_ 
                               (ap (fst o r) (merge-split τ1 x)) 
                               (merge-split τ2 (snd (r x)) ∘ ap2 (merge τ2)
                                                        (independent {τ1} {τ2} r x (default τ1)) 
                                                        (ap (snd o split τ2 o snd o r) (merge-split τ1 x))))

  wrap : ∀ {Γ} {τ} → (e : Γ ⊢ τ) → << Γ >>c → T << τ >>
  wrap {Γ}{τ} e θ = Functor.arr TF (λ ecst → merge τ ([[ e ]]e (fst (splitc Γ θ))) ecst)
                   (<< e >>split (splitc Γ θ)) 

  thm : ∀ {Γ} {τ} (e : Γ ⊢ τ) (θ : _) → << e >>e θ == wrap e θ
  thm c θ = id
  thm {τ = τ} (v i0) θ = ap (λ x → c0 , x) (! (merge-split τ (snd θ)))
  thm (v (iS x)) θ = thm (v x) (fst θ)
  thm (lam e) θ = ap (λ x → c0 , x) (λ≃ (λ x → thm e (θ , x)))
  thm {Γ} (app{τ1}{τ2} e1 e2) θ = 
    ap (\ p → (mc c1 (mc (fst (<< e1 >>split (splitc Γ θ))) (mc (fst (<< e2 >>split (splitc Γ θ))) (fst (snd (<< e1 >>split (splitc Γ θ)) (fst p) (snd p))))) , merge τ2 ([[ e1 ]]e (fst (splitc Γ θ)) (fst p)) (snd (snd (<< e1 >>split (splitc Γ θ)) (fst p) (snd p))))) 
      (split-merge12 τ1 ([[ e2 ]]e (fst (splitc Γ θ)) , snd (<< e2 >>split (splitc Γ θ)))) ∘
    ap2 (λ a b₁ → _>>=_ addc (λ _ → _>>=_ a (λ f → _>>=_ b₁ (λ x → f x))))
        (thm e1 θ) (thm e2 θ) 



