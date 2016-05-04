{-# OPTIONS --type-in-type #-}

open import lib.Prelude hiding (wrap)

module misc.Retraction3f2 where

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


  {-
    Define an equivalence relation on (p1 p2 : << τ >>) by split p1 = split p2,
    or equivalently, merge (split p1) = merge (split p2).
   
    This logical relation picks out those elements that are
    well-defined on equivalence classes:

    Write nf(p) for merge(split p), which we think of as the "normal form" of p.

    We want that r is well-defined means if nf(x) = nf(y) then nf(r(x)) = nf(r(y)).

    It's equivalent to check that nf(r(x)) = nf(r(nf x)) for all x, because then

      nf(r(x)) = nf(r(nf x)) = nf(r(nf y)) = nf(r(y) when nf(x) = nf(y)

    (Conversely, if we know that r takes equals to equals, then 
     nf(r(x)) = nf(r(nf x)) because nf(x) = nf(nf x) by canceling split o merge 
     in the middle.)

    Finally, it's slightly simpler (and equivalent) to check that
    split(r(x)) = split(r(nf x)) and then we can tack on the merge
    later.
  -}
  
  -- other reasonable choice:
  --   (split τ2 (snd (r (merge τ1 (split τ1 x)))) == split τ2 (snd (r x)))

  Good : (τ : Tp) → << τ >> → Type
  Good b _ = Unit
  Good (τ1 ⇒ τ2) r = (merge⇒ τ1 τ2 (split⇒ τ1 τ2 r) == r) ×
                     (( x : << τ1 >>) → Good τ1 x → Good τ2 (snd (r x)))

  Good-normal : (τ : Tp) (x : << τ >>) → Good τ x → merge τ (split τ x) == x
  Good-normal b x gx = id
  Good-normal (τ1 ⇒ τ2) x gx = fst gx

  GoodC : (Γ : Ctx) → << Γ >>c → Type
  GoodC [] _ = Unit
  GoodC (τ :: Γ) θ = GoodC Γ (fst θ) × Good τ (snd θ)

  Good-normalC : (Γ : Ctx) (x : << Γ >>c) → GoodC Γ x → mergec Γ (splitc Γ x) == x
  Good-normalC [] x gx = id
  Good-normalC (τ :: Γ) x gx = {!!}

  allgood : {Γ : Ctx} {τ : Tp} (e : Γ ⊢ τ) 
            → ( (θ : << Γ >>c) → GoodC Γ θ → 
                 (merge⊢ Γ τ (split⊢ Γ τ << e >>e) θ == << e >>e θ) × 
                 Good τ (snd (<< e >>e θ)))
  allgood c θ gθ = id , <>
  allgood {τ = τ} (v i0) θ gθ = {! OK? !} , snd gθ
  allgood (v (iS x)) θ gθ = allgood (v x) (fst θ) (fst gθ)
  allgood (lam e) θ gθ = 
    ap (_,_ c0) (λ≃ (λ x → ap2 _,_ {!!} (ap snd (fst (allgood e (θ , x) (gθ , {!BROKEN!})))))) , 
    ({!!} , 
     (λ x gx → snd (allgood e (θ , x) (gθ , gx))))
  allgood (app e e₁) = {!!}

  independent : {τ1 τ2 : Tp} (r : τ1 ⇒m τ2) (gr : Good (τ1 ⇒ τ2) r) (x : << τ1 >>) (c1 : << τ1 >>cst) →
             (fst (split τ2 (snd (r (merge τ1 (fst (split τ1 x) , c1))))))
          == (fst (split τ2 (snd (r x))))
  independent {τ1} {τ2} r p x c2 = {!!} -- change meaning of r?
{-
    ! (ap fst (split-merge τ2 (fst r (fst (split τ1 x)) , snd (snd r (split τ1 x))))) ∘ 
    ap (fst r) (ap fst (split-merge τ1 (fst (split τ1 x) , c2))) ∘
    ap fst (split-merge τ2 (fst r (fst (split τ1 (merge τ1 (fst (split τ1 x) , c2)))) , snd (snd r (split τ1 (merge τ1 (fst (split τ1 x) , c2))))))
-}

  -- thm1 : ∀ {Γ} {τ} (e : Γ ⊢ τ) (θ : _) → split τ (snd (<< e >>e θ)) == split τ (snd (<< e >>e (mergec Γ (splitc Γ θ))))
  -- thm1 c θ = id
  -- thm1 {τ = τ} (v i0) θ = ! (split-merge τ (split τ (snd θ)))
  -- thm1 (v (iS x)) θ = thm1 (v x) (fst θ)
  -- thm1 (lam{τ1}{τ2} e) θ = ap2 _,_ (λ≃ (λ x → {!!})) {!!}
  -- thm1 (app e e₁) θ = {!!}


  thm : ∀ {Γ} {τ} (e : Γ ⊢ τ) → split⊢ Γ τ << e >>e == ([[ e ]]e , << e >>cste)
  thm c = id
  thm {τ = τ} (v i0) = ap2 _,_ (λ≃ (λ x → ap fst (split-merge τ (snd x , default τ)))) 
                              (λ≃ (λ x → ap (λ h → c0 , h) (ap snd (split-merge τ ((snd (fst x)) , (snd (snd x)))))))
  thm {Γ = τ0 :: Γ} {τ = τ} (v (iS x)) = ap2 _,_ (λ≃ (λ p1 → ap≃ (ap fst (thm (v x))) {fst p1})) (λ≃ (λ p → ap≃ (ap snd (thm (v x)))))
  thm (lam e) = ap2 _,_ (λ≃ (λ θ → λ≃ (λ x → ap≃ (ap fst (thm e)))))
                        (λ≃ (λ pc1 → ap (λ h → c0 , h) (λ≃ (λ x → ap≃ (ap snd (thm e))))))
  thm {Γ = Γ} (app{τ1}{τ2} e1 e2) with ap fst (thm e1) | ap snd (thm e1) | ap fst (thm e2) | ap snd (thm e2)
  ... | ih1 | ih2 | ih3 | ih4 = ap2 _,_ (λ≃ (λ pot → ap2 (λ h1 h2 → h1 pot (h2 pot)) ih1 ih3 ∘ {!!})) 
    (λ≃ (\ pc1 → ap2 (λ h1 h2 → mc c1 (mc (fst (h1 pc1)) (mc (fst (h2 pc1)) (fst (snd (h1 pc1) ([[ e2 ]]e (fst pc1) , snd (h2 pc1)))))) , snd (snd (h1 pc1) ([[ e2 ]]e (fst pc1) , snd (h2 pc1))))
                        ih2 ih4
                ∘ ap (λ h2 → mc c1 (mc (fst (<< e1 >>e (mergec Γ pc1))) (mc (fst (<< e2 >>e (mergec Γ pc1))) (fst (snd (<< e1 >>e (mergec Γ pc1)) (merge τ1 (h2 (fst pc1) , snd (split τ1 (snd (<< e2 >>e (mergec Γ pc1)))))))))) , snd (split τ2 (snd (snd (<< e1 >>e (mergec Γ pc1)) (merge τ1 (h2 (fst pc1) , snd (split τ1 (snd (<< e2 >>e (mergec Γ pc1))))))))))
                     ih3
                ∘ ap2 _,_ 
                  (ap (λ h → mc c1 (mc (fst (<< e1 >>e (mergec Γ pc1))) (mc (fst (<< e2 >>e (mergec Γ pc1))) h)))
                      {!fst (snd (allgood e1 (mergec Γ pc1) ?) ? ?) !})
                  {!!}))

--   thm c θ sθ = id
--   thm {τ = τ} (v i0) θ sθ = {!!}
--   thm (v (iS x)) θ sθ = thm (v x) (fst θ) {!!}
--   thm (lam{τ1}{τ2} e) θ sθ = ap (λ x → c0 , x) (λ≃ (λ x → {!!} ∘ thm e (θ , merge τ1 (split τ1 x)) {!!} ∘ {!!} ))
--   thm {Γ} (app{τ1}{τ2} e1 e2) θ sθ = {!!} ∘ 
-- --    ap (\ p → (mc c1 (mc (fst (<< e1 >>cste (splitc Γ θ))) (mc (fst (<< e2 >>cste (splitc Γ θ))) (fst (snd (<< e1 >>cste (splitc Γ θ)) (fst p) (snd p))))) , merge τ2 ([[ e1 ]]e (fst (splitc Γ θ)) (fst p)) (snd (snd (<< e1 >>cste (splitc Γ θ)) (fst p) (snd p))))) 
-- --      (split-merge12 τ1 ([[ e2 ]]e (fst (splitc Γ θ)) , snd (<< e2 >>cste (splitc Γ θ)))) ∘
--     ap2 (λ a b₁ → _>>=_ addc (λ _ → _>>=_ a (λ f → _>>=_ b₁ (λ x → f x))))
--         (thm e1 θ sθ) (thm e2 θ sθ) 

--   thm : ∀ {Γ} {τ} (e : Γ ⊢ τ) (θ : _) → GoodC Γ θ → << e >>e θ == Retraction.g (ret⊢ Γ τ) ([[ e ]]e , << e >>cste) θ
--   thm c θ sθ = id
--   thm {τ = τ} (v i0) θ sθ = {!!}
--   thm (v (iS x)) θ sθ = thm (v x) (fst θ) {!!}
--   thm (lam{τ1}{τ2} e) θ sθ = ap (λ x → c0 , x) (λ≃ (λ x → {!!} ∘ thm e (θ , merge τ1 (split τ1 x)) {!!} ∘ {!!} ))
--   thm {Γ} (app{τ1}{τ2} e1 e2) θ sθ = {!!} ∘ 
-- --    ap (\ p → (mc c1 (mc (fst (<< e1 >>cste (splitc Γ θ))) (mc (fst (<< e2 >>cste (splitc Γ θ))) (fst (snd (<< e1 >>cste (splitc Γ θ)) (fst p) (snd p))))) , merge τ2 ([[ e1 ]]e (fst (splitc Γ θ)) (fst p)) (snd (snd (<< e1 >>cste (splitc Γ θ)) (fst p) (snd p))))) 
-- --      (split-merge12 τ1 ([[ e2 ]]e (fst (splitc Γ θ)) , snd (<< e2 >>cste (splitc Γ θ)))) ∘
--     ap2 (λ a b₁ → _>>=_ addc (λ _ → _>>=_ a (λ f → _>>=_ b₁ (λ x → f x))))
--         (thm e1 θ sθ) (thm e2 θ sθ) 


{-
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
 
{-
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

{-
  thm : ∀ {Γ} {τ} (e : Γ ⊢ τ) (θ : _) → << e >>e θ == wrap e θ
  thm c θ = id
  thm {τ = τ} (v i0) θ = ap (λ x → c0 , x) (! (merge-split τ (snd θ)))
  thm (v (iS x)) θ = thm (v x) (fst θ)
  thm (lam e) θ = ap (λ x → c0 , x) (λ≃ (λ x → thm e (θ , x)))
  thm {Γ} (app{τ1}{τ2} e1 e2) θ = 
    ap (\ p → (mc c1 (mc (fst (<< e1 >>cste (splitc Γ θ))) (mc (fst (<< e2 >>cste (splitc Γ θ))) (fst (snd (<< e1 >>cste (splitc Γ θ)) (fst p) (snd p))))) , merge τ2 ([[ e1 ]]e (fst (splitc Γ θ)) (fst p)) (snd (snd (<< e1 >>cste (splitc Γ θ)) (fst p) (snd p))))) 
      (split-merge12 τ1 ([[ e2 ]]e (fst (splitc Γ θ)) , snd (<< e2 >>cste (splitc Γ θ)))) ∘
    ap2 (λ a b₁ → _>>=_ addc (λ _ → _>>=_ a (λ f → _>>=_ b₁ (λ x → f x))))
        (thm e1 θ) (thm e2 θ) 
-}

-}
-}
