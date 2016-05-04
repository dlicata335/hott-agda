
-- ON PRINTING RETRACTIONS

{-# OPTIONS --type-in-type #-}

open import lib.Prelude hiding (wrap)

module misc.Retraction3g where

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

 RStable : ∀ {A B} → Retraction A B → A → Type
 RStable r a = Retraction.g r (Retraction.f r a) == a

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

  mutual
    <<_>> : Tp → Type
    << b >> = B
    << τ1 ⇒ τ2 >> = τ1 ⇒m τ2

    _⇒m_ : Tp → Tp → Type
    τ1 ⇒m τ2 = << τ1 >> → T << τ2 >>

  <<_>>c : Ctx → Type
  << [] >>c = Unit
  << τ :: Γ >>c = << Γ >>c × << τ >>

  _⊢m_ : Ctx → Tp → Set
  Γ ⊢m τ = << Γ >>c → T << τ >>

  <<_>>e : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊢m τ
  <<_>>e c θ = return b0
  <<_>>e (v i0) θ = return (snd θ)
  <<_>>e (v (iS x)) θ = << v x >>e (fst θ)
  <<_>>e (lam e) θ = return (λ x → << e >>e (θ , x))
  <<_>>e (app e1 e2) θ = addc >>= (\ _ → (<< e1 >>e θ) >>= (λ f →(<< e2 >>e θ) >>= (λ x → f x)))


  -- just the cost part

  <<_>>cst : Tp → Type
  << b >>cst = Unit
  << τ1 ⇒ τ2 >>cst = (([[ τ1 ]] × << τ1 >>cst) → T << τ2 >>cst)

  <<_>>cstc : Ctx → Type
  << [] >>cstc = Unit
  << τ :: Γ >>cstc = << Γ >>cstc × << τ >>cst

  <<_>>cste : ∀ {Γ τ} → Γ ⊢ τ → ([[ Γ ]]c × << Γ >>cstc) → T << τ >>cst
  <<_>>cste c (θ , θc) = return <>
  <<_>>cste (v i0) (θ , θc) = return (snd θc)
  <<_>>cste (v (iS x)) (θ , θc) = << v x >>cste ((fst θ) , (fst θc))
  <<_>>cste (lam e) (θ , θc) = return (λ x → << e >>cste ((θ , fst x) , (θc , snd x)))
  <<_>>cste (app e1 e2) (θ , θc) = 
    addc >>= (\ _ →  
    (<< e1 >>cste (θ , θc)) >>= (λ ce1 → 
    (<< e2 >>cste (θ , θc)) >>= (λ ce2 → 
    ce1 ([[ e2 ]]e θ , ce2))))


  _⇒split_ : Tp → Tp → Set
  τ1 ⇒split τ2 = ([[ τ1 ]] → [[ τ2 ]]) × (([[ τ1 ]] × << τ1 >>cst) → T << τ2 >>cst)

  _⊢split_ : Ctx → Tp → Set
  Γ ⊢split τ = ([[ Γ ]]c → [[ τ ]]) × (([[ Γ ]]c × << Γ >>cstc) → T << τ >>cst)
  

  default : ∀ τ → << τ >>cst 
  default b = <>
  default (τ1 ⇒ τ2) = λ _ → {!!} , default τ2 -- arbitrary

  -- relationship between the two

  -- FIXME: there's probably a nicer way to write these retractions
  -- using the combinators for retractions for →, ×, swapping iso, etc.

  mutual 
    split : ∀ τ → << τ >> → [[ τ ]] × << τ >>cst
    split b cpot = cpot , <>
    split (τ1 ⇒ τ2) cpot = split⇒ τ1 τ2 cpot

    merge : ∀ τ → [[ τ ]] × << τ >>cst → << τ >>
    merge b pc = fst pc
    merge (τ1 ⇒ τ2) pc = merge⇒ τ1 τ2 pc

    merged : ∀ τ → [[ τ ]] → << τ >>
    merged τ pot = merge τ (pot , default τ)

    split⇒ : (τ1 τ2 : Tp) → τ1 ⇒m τ2 → τ1 ⇒split τ2
    split⇒ τ1 τ2 cpot = 
      (λ pot → fst (split τ2 (snd (cpot (merged τ1 pot))))) , 
      (λ pc1 → (fst (cpot (merge τ1 pc1))) , (snd (split τ2 (snd (cpot (merge τ1 pc1))))))
 
    merge⇒ : (τ1 τ2 : Tp) → τ1 ⇒split τ2 → τ1 ⇒m τ2 
    merge⇒ τ1 τ2 (pot , cost) = 
        (λ x → fst (cost (split τ1 x)) , 
               merge τ2 (pot (fst (split τ1 x)) , (snd (cost (split τ1 x)))))


  mutual
    split-merge : (τ : Tp) (pc : [[ τ ]] × << τ >>cst) → (split τ (merge τ pc)) == pc
    split-merge b _ = id
    split-merge (τ1 ⇒ τ2) pc = split-merge⇒ _ _ pc

    split-merge⇒ : (τ1 τ2 : Tp) (pc : _) → split⇒ τ1 τ2 (merge⇒ τ1 τ2 pc) == pc
    split-merge⇒ τ1 τ2 (pot , cst) = ap2 _,_ 
      (λ≃ (λ pot1 → ap (pot o fst) 
                       (split-merge τ1 (pot1 , default τ1)) ∘
                     ap fst
                      (split-merge τ2 (pot (fst (split τ1 (merge τ1 (pot1 , default τ1)))) , snd (cst (split τ1 (merge τ1 (pot1 , default τ1)))))))) 
      (λ≃ (λ pc1 → ap2 _,_ 
                   (ap (λ h → fst (cst h)) (split-merge τ1 pc1)) 
                   (ap snd (split-merge τ2 (pot (fst pc1) , snd (cst pc1))) ∘ 
                    ap (λ h → snd (split τ2 (merge τ2 (pot (fst h) , snd (cst h))))) 
                       (split-merge τ1 pc1))))

  rett : (τ : Tp) → Retraction << τ >> ([[ τ ]] × << τ >>cst)
  rett τ = retraction (split τ) (merge τ) (split-merge τ)

  ret⇒ : (τ1 τ2 : Tp) → Retraction (τ1 ⇒m τ2) (τ1 ⇒split τ2)
  ret⇒ τ1 τ2 = retraction (split⇒ τ1 τ2) (merge⇒ τ1 τ2) (split-merge⇒ τ1 τ2)

  splitc : ∀ Γ → << Γ >>c → [[ Γ ]]c × << Γ >>cstc 
  splitc [] θ = <> , <>
  splitc (τ :: Γ) θ = ((fst (splitc Γ (fst θ))) , (fst (split τ (snd θ)))) , 
                      (snd (splitc Γ (fst θ)) , snd (split τ (snd θ)))

  mergec : ∀ Γ → [[ Γ ]]c × << Γ >>cstc → << Γ >>c 
  mergec [] _ = <>
  mergec (τ :: Γ) (pot , cst) = mergec Γ (fst pot , fst cst) , merge τ (snd pot , snd cst)

  defaultc : ∀ Γ → << Γ >>cstc
  defaultc [] = <>
  defaultc (τ :: Γ) = defaultc Γ , default τ

  mergedc : ∀ Γ → [[ Γ ]]c  → << Γ >>c 
  mergedc Γ p = mergec Γ (p , defaultc Γ)

  split-mergec : (Γ : Ctx) (pc : _) → (splitc Γ (mergec Γ pc)) == pc
  split-mergec [] pc = id
  split-mergec (τ :: Γ) pc = ap2 _,_ (ap2 _,_ (ap fst (split-mergec Γ (fst (fst pc) , fst (snd pc))))
                                              (ap fst (split-merge τ (snd (fst pc) , snd (snd pc)))))
                                     (ap2 _,_ (ap snd (split-mergec Γ (fst (fst pc) , fst (snd pc)))) 
                                              (ap snd (split-merge τ (snd (fst pc), snd (snd pc)))))

  retc : (Γ : Ctx) → Retraction << Γ >>c ([[ Γ ]]c × << Γ >>cstc)
  retc Γ = retraction (splitc Γ) (mergec Γ) (split-mergec Γ)


  -- FIXME: avoid the copy and paste

  split⊢ : (Γ : Ctx) (τ : Tp) → Γ ⊢m τ → Γ ⊢split τ
  split⊢ Γ τ cpot = 
    (λ pot → fst (split τ (snd (cpot (mergedc Γ pot))))) , 
    (λ pc1 → (fst (cpot (mergec Γ pc1))) , (snd (split τ (snd (cpot (mergec Γ pc1))))))

  merge⊢ : (Γ : Ctx) (τ : Tp) → Γ ⊢split τ → Γ ⊢m τ
  merge⊢ Γ τ (pot , cost) = 
      (λ x → fst (cost (splitc Γ x)) , 
             merge τ (pot (fst (splitc Γ x)) , (snd (cost (splitc Γ x)))))

  split-merge⊢ : (Γ : Ctx) (τ : Tp) (y : Γ ⊢split τ) → (split⊢ Γ τ (merge⊢ Γ τ y)) == y
  split-merge⊢ Γ τ (pot , cst) = ap2 _,_ 
      (λ≃ (λ pot1 → ap (pot o fst) 
                       (split-mergec Γ (pot1 , defaultc Γ)) ∘
                     ap fst
                      (split-merge τ (pot (fst (splitc Γ (mergec Γ (pot1 , defaultc Γ)))) , snd (cst (splitc Γ (mergec Γ (pot1 , defaultc Γ)))))))) 
      (λ≃ (λ pc1 → ap2 _,_ 
                   (ap (λ h → fst (cst h)) (split-mergec Γ pc1)) 
                   (ap snd (split-merge τ (pot (fst pc1) , snd (cst pc1))) ∘ 
                    ap (λ h → snd (split τ (merge τ (pot (fst h) , snd (cst h))))) 
                       (split-mergec Γ pc1))))

  ret⊢ : (Γ : Ctx) (τ : Tp) → Retraction (Γ ⊢m τ) (Γ ⊢split τ)
  ret⊢ Γ τ = retraction (split⊢ Γ τ) (merge⊢ Γ τ) (split-merge⊢ Γ τ)


  Good : (τ : Tp) → << τ >> → Type
  Good b _ = Unit
  Good (τ1 ⇒ τ2) r = 
    (( x : << τ1 >>) → Good τ1 x → 
      -- reduction of split τ2 (snd (merge⇒ τ1 τ2 (split⇒ τ1 τ2 r) x)) == split τ2 (snd (r x))
      ((fst (split τ2 (snd (r (merge τ1 (fst (split τ1 x) , default τ1))))) == fst (split τ2 (snd (r x)))) × 
       (snd (split τ2 (snd (r (merge τ1 (split τ1 x))))) == snd (split τ2 (snd (r x)))) ×
       -- and the costs are equal
       (fst (r (merge τ1 (split τ1 x))) == fst (r x))) ×
      Good τ2 (snd (r x)))


  GoodC : (Γ : Ctx) → << Γ >>c → Type
  GoodC [] _ = Unit
  GoodC (τ :: Γ) θ = GoodC Γ (fst θ) × Good τ (snd θ)

  Good-merge : ∀ τ (x : _) → Good τ (merge τ x)
  Good-merge b x = <>
  Good-merge (τ ⇒ τ₁) r x gx = ({!OK!} , {!OK!} , {!OK!}) , (Good-merge τ₁ _)

  GoodC-merge : ∀ Γ (θ : _) → GoodC Γ (mergec Γ θ)
  GoodC-merge [] x = <>
  GoodC-merge (τ :: Γ) θ = GoodC-merge Γ _ , Good-merge τ _

  allgood : {Γ : Ctx} {τ : Tp} (e : Γ ⊢ τ) 
            → ( (θ : << Γ >>c) → GoodC Γ θ → 
                 ((fst (split τ (snd (<< e >>e (mergec Γ (fst (splitc Γ θ) , defaultc Γ))))) 
                  == fst (split τ (snd (<< e >>e θ)))) ×
                 (snd (split τ (snd (<< e >>e (mergec Γ (splitc Γ θ))))) == snd (split τ (snd (<< e >>e θ)))) × 
                 (fst (<< e >>e (mergec Γ (splitc Γ θ))) == fst (<< e >>e θ))) ×
                 Good τ (snd (<< e >>e θ)))
  allgood c θ gθ = (id , id , id) , <> 
  allgood (v i0) θ gθ = ({!OK!} , ({!OK!} , id)) , snd gθ
  allgood (v (iS x)) θ gθ = allgood (v x) (fst θ) (fst gθ)
  allgood (lam{τ1} e) θ gθ = 
          (λ≃ (λ pot → fst (fst (allgood e (θ , merge τ1 (pot , default τ1)) (gθ , Good-merge τ1 (pot , default τ1)))) ∘ {!OK!}) , 
          ((λ≃ (λ pc1 → ap2 _,_ 
                         (snd (snd (fst (allgood e (θ , merge τ1 pc1) (gθ , Good-merge τ1 pc1)))) ∘ {!OK!}) 
                         (fst (snd (fst (allgood e (θ , merge τ1 pc1) (gθ , Good-merge τ1 pc1)))) ∘ {!OK!}))) , 
          id)) , 
          (λ x gx → (fst (fst (allgood e (θ , x) (gθ , gx))) ∘ {!OK!} ∘ ! (fst (fst (allgood e (θ , merge τ1 (fst (split τ1 x) , default τ1)) (gθ , Good-merge τ1 _)))) , 
                     fst (snd (fst (allgood e (θ , x) (gθ , gx)))) ∘ {! same trick!} , 
                     (snd (snd (fst (allgood e (θ , x) (gθ , gx)))) ∘ {! same trick!})) , snd (allgood e (θ , x) (gθ , gx)))
  allgood {Γ} (app{τ1}{τ2} e1 e2) θ gθ with allgood e1 θ gθ | allgood e2 θ gθ | allgood e1 (mergec Γ (fst (splitc Γ θ) , defaultc Γ)) (GoodC-merge Γ _) | allgood e2 (mergec Γ (fst (splitc Γ θ) , defaultc Γ)) (GoodC-merge Γ _) | allgood e1 (mergec Γ (splitc Γ θ)) (GoodC-merge Γ _) | allgood e2 (mergec Γ (splitc Γ θ)) (GoodC-merge Γ _)
  ... | (ih1pot , ih1cst , ih1c) , ih1rec | (ih2pot , ih2cst , ih2c) , ih2rec | (ih1pot' , _ , _) , ih1rec' | (ih2pot' , _ , _) , ih2rec' |  (_ , ih1cst'' , _) , ih1rec'' | (ih2pot'' , ih2cst'' , _) , ih2rec''
    = (fst (fst (ih1rec _ ih2rec)) ∘ 
         ap≃ ih1pot {fst (split τ1 (snd (<< e2 >>e θ)))} ∘ 
         ap (λ h → fst (split τ2 (snd (snd (<< e1 >>e (mergec Γ (fst (splitc Γ θ) , defaultc Γ))) (merge τ1 (h , default τ1))))))
           ih2pot ∘ 
         ! (fst (fst (ih1rec' (snd (<< e2 >>e (mergec Γ (fst (splitc Γ θ) , defaultc Γ)))) ih2rec'))) , 
       fst (snd (fst (ih1rec _ ih2rec))) ∘ 
         ap snd (ap≃ ih1cst {split τ1 (snd (<< e2 >>e θ))}) ∘ 
         ap (λ h → snd (split τ2 (snd (snd (<< e1 >>e (mergec Γ (splitc Γ θ))) (merge τ1 h))))) foo ∘
         -- ap (λ h → snd (split τ2 (snd (snd (<< e1 >>e (mergec Γ (splitc Γ θ))) (merge τ1 h))))) (ap2 _,_ ih2pot ih2cst) ∘ -- FIXME one option
         ! (fst (snd (fst (ih1rec'' _ ih2rec'')))) , 
       ap
         (λ h → mc c1 (mc (fst (<< e1 >>e θ)) (mc (fst (<< e2 >>e θ)) h))) (snd (snd (fst (ih1rec (snd (<< e2 >>e θ)) ih2rec))) ∘ 
                ap (λ x → fst (snd (<< e1 >>e θ) (merge τ1 x))) foo ∘ ap fst (ap≃ ih1cst) ∘ ! (snd (snd (fst (ih1rec'' _ ih2rec'')))) ) ∘
         ap2
         (λ h1 h2 →
            mc c1
            (mc h1
             (mc h2
              (fst
               (snd (<< e1 >>e (mergec Γ (splitc Γ θ)))
                (snd (<< e2 >>e (mergec Γ (splitc Γ θ)))))))))
         ih1c ih2c) , 
      ((snd (ih1rec _ ih2rec)))  where
      foo : (split τ1 (snd (<< e2 >>e (mergec Γ (splitc Γ θ)))) == split τ1 (snd (<< e2 >>e θ)))
      foo = ap2 _,_ {!ih2pot''!} ih2cst 

  thm : ∀ {Γ} {τ} (e : Γ ⊢ τ) → split⊢ Γ τ << e >>e == ([[ e ]]e , << e >>cste)
  thm c = id
  thm {τ = τ} (v i0) = ap2 _,_ (λ≃ (λ x → ap fst (split-merge τ (snd x , default τ)))) 
                              (λ≃ (λ x → ap (λ h → c0 , h) (ap snd (split-merge τ ((snd (fst x)) , (snd (snd x)))))))
  thm {Γ = τ0 :: Γ} {τ = τ} (v (iS x)) = ap2 _,_ (λ≃ (λ p1 → ap≃ (ap fst (thm (v x))) {fst p1})) (λ≃ (λ p → ap≃ (ap snd (thm (v x)))))
  thm (lam e) = ap2 _,_ (λ≃ (λ θ → λ≃ (λ x → ap≃ (ap fst (thm e)))))
                        (λ≃ (λ pc1 → ap (λ h → c0 , h) (λ≃ (λ x → ap≃ (ap snd (thm e))))))
  thm {Γ = Γ} (app{τ1}{τ2} e1 e2) with ap fst (thm e1) | ap snd (thm e1) | ap fst (thm e2) | ap snd (thm e2)
  ... | ih1 | ih2 | ih3 | ih4 = {!!}
{-

ap2 _,_ (λ≃ (λ pot → ap2 (λ h1 h2 → h1 pot (h2 pot)) ih1 ih3 ∘ {!!})) 
    (λ≃ (\ pc1 → ap2 (λ h1 h2 → mc c1 (mc (fst (h1 pc1)) (mc (fst (h2 pc1)) (fst (snd (h1 pc1) ([[ e2 ]]e (fst pc1) , snd (h2 pc1)))))) , snd (snd (h1 pc1) ([[ e2 ]]e (fst pc1) , snd (h2 pc1))))
                        ih2 ih4
                ∘ ap (λ h2 → mc c1 (mc (fst (<< e1 >>e (mergec Γ pc1))) (mc (fst (<< e2 >>e (mergec Γ pc1))) (fst (snd (<< e1 >>e (mergec Γ pc1)) (merge τ1 (h2 (fst pc1) , snd (split τ1 (snd (<< e2 >>e (mergec Γ pc1)))))))))) , snd (split τ2 (snd (snd (<< e1 >>e (mergec Γ pc1)) (merge τ1 (h2 (fst pc1) , snd (split τ1 (snd (<< e2 >>e (mergec Γ pc1))))))))))
                     ih3
                ∘ ap2 _,_ 
                  (ap (λ h → mc c1 (mc (fst (<< e1 >>e (mergec Γ pc1))) (mc (fst (<< e2 >>e (mergec Γ pc1))) h)))
                      {!fst (snd (allgood e1 (mergec Γ pc1) ?) ? ?) !})
                  ({!!} ∘ ! (ap snd (fst (snd (allgood e1 (mergec Γ pc1) {!!}) (snd (<< e2 >>e (mergec Γ pc1))) {!!}))))))
-}
