
{-# OPTIONS --type-in-type --without-K #-}

-- identity types that never use K
-- homotopically, Id M N is thought of as a path from M to N
-- we also use M ≃ N and Path M N as notation for Id M N

open import lib.First

module lib.Paths where

 data Id {A : Type} : A → A → Type where
   id : {M : A} → Id M M

 Path : {A : Type} → A → A → Type
 Path = Id

 _≃_ : {A : Type} → A → A → Type
 _≃_ = Path

 infix 9 _≃_

 -- type-indepdendent operations on paths

 module Paths where
   -- induction

   jay : {A : Type} (C : (x y : A) -> Path x y -> Type)
       -> {M N : A} -> (P : Path M N)
       -> ((x : A) -> C x x id)
       -> C M N P
   jay _ id b = b _

   path-induction : {A : Type} {M : A}
                    (C : (x : A) → Path M x → Type)
                 → (C M id)
                 → {N : A} → (P : Path M N)
                 → C N P
   path-induction _ b id = b

   -- groupoid

   ! : {A : Type} {M N : A} → Path M N → Path N M 
   ! id = id
   
   _∘_  : {A : Type} {M N P : A} → Path N P → Path M N → Path M P
   β ∘ id = β
   
   infixr 10 _∘_ 
   
   infix  2 _∎
   infixr 2 _≃〈_〉_ 
   
   _≃〈_〉_ : {A : Type} (x : A) {y z : A} → Path x y → Path y z → Path x z
   _ ≃〈 p1 〉 p2 = (p2 ∘ p1)
   
   _∎ : ∀ {A : Type} (x : A) → Path x x
   _∎ _ = id
   
   ∘-unit-l  : {A : Type} {M N : A} (α : Path M N)
             → Path (id ∘ α) α
   ∘-unit-l id = id
   
   ∘-assoc  : {A : Type} {M N P Q : A} 
            (γ : Path P Q) (β : Path N P) (α : Path M N) 
            → Path (γ ∘ (β ∘ α)) ((γ ∘ β) ∘ α)
   ∘-assoc id id id = id
   
   !-inv-l  : {A : Type} {M N : A} (α : Path M N) 
            → Path (! α ∘ α) id
   !-inv-l id = id
   
   ∘-unit-r  : {A : Type} {M N : A} (α : Path M N)
             → Path (α ∘ id) α
   ∘-unit-r id = id
   
   !-inv-r : {A : Type} {M N : A} (α : Path M N) → Path (α ∘ (! α)) id
   !-inv-r id = id
   
   !-inv-r-front : {A : Type} {M N P : A} (p : Path P N) (q : Path M N) → Path (p ∘ (! p) ∘ q) q
   !-inv-r-front id id = id
   
   !-inv-r-back : {A : Type} {M N P : A} (q : Path N M) (p : Path P N) → Path (q ∘ (p ∘ ! p)) q
   !-inv-r-back id id = id
   
   !-invol : {A : Type} {M N : A} (p : Path M N) → Path (! (! p)) p
   !-invol id = id
   
   !-∘ : {A : Type} {M N P : A} → (q : Path N P) → (p : Path M N)
       → (! (q ∘ p)) ≃ ! p ∘ ! q
   !-∘ id id = id
   
   move-right :  {A : Type} {M N P : A}
                 (β : Path N P) (α : Path M N) (γ : Path M P)
              → Path (β ∘ α) γ
              → Path α (! β ∘ γ)
   move-right id id γ x = ! (∘-unit-l γ) ∘ x
   
   move-left-! :  {A : Type} {M N P : A}
                 (α : Path M N) (β : Path N P) (γ : Path M P)
              → Path α (! β ∘ γ)
              → Path (β ∘ α) γ
   move-left-! id id γ x = ∘-unit-l γ ∘ x

   move-left-right :  {A : Type} {M N P : A}
                 (α : Path M P) (β : Path N P) (γ : Path M N)
              → Path α (β ∘ γ) 
              → Path (α ∘ ! γ) β 
   move-left-right id β id x = x
   
   move-right-! :  {A : Type} {M N P : A}
                  (β : Path P N) (α : Path M N) (γ : Path M P)
               → Path (! β ∘ α) γ
               → Path α (β ∘ γ)
   move-right-! id id γ x = ! (∘-unit-l γ) ∘ x
   
   move-right-right :  {A : Type} {M N P : A}
                         (β : Path N P) (α : Path M N) (γ : Path M P)
                      → Path (β ∘ α) γ
                      → Path β (γ ∘ ! α)
   move-right-right id id γ x = x

   move-right-right-! :  {A : Type} {M N P : A}
                         (β : Path N P) (α : Path N M) (γ : Path M P)
                      → Path (β ∘ ! α) γ
                      → Path β (γ ∘ α)
   move-right-right-! id id γ x = x
   
   rassoc-1-3-1 : ∀ {A} {M1 M2 M3 M4 M5 M6 : A}
                  (a56 : Path M5 M6) (a45 : Path M4 M5) (a34 : Path M3 M4) (a23 : Path M2 M3) (a12 : Path M1 M2)
                → Path (a56 ∘ (a45 ∘ a34 ∘ a23) ∘ a12) (a56 ∘ a45 ∘ a34 ∘ a23 ∘ a12)
   rassoc-1-3-1 id id id id id = id


   -- transport and ap
   
   transport :  {B : Type} (E : B → Type) 
                {b1 b2 : B} → Path b1 b2 → (E b1 → E b2)
   transport C id = λ x → x
   
   transport-Path-right :  {A : Type} {M N P : A} 
     (α' : Path N P) (α : Path M N)
     → Path (transport (\ x → Path M x) α' α) (α' ∘ α)
   transport-Path-right id id = id 

   ap :  {A B : Type} {M N : A}
         (f : A → B) → Path{A} M N → Path{B} (f M) (f N)
   ap f id = id
   
   apd  :  {B : Type} {E : B → Type} {b₁ b₂ : B} 
           (f : (x : B) → E x) (β : Path b₁ b₂) 
        → Path (transport E β (f b₁)) (f b₂) 
   apd f id = id 
   
   transport-∘ : {A : Type} (C : A → Type) {M N P : A} (β : Path N P) (α : Path M N)
             → Path (transport C (β ∘ α)) (\ x → transport C β (transport C α x))
   transport-∘ _ id id = id
   
   transport-ap-assoc : {A : Type} (C : A → Type) {M N : A} (α : Path M N) → Path (transport C α) (transport (\ x → x) (ap C α))
   transport-ap-assoc C id = id 
   
   transport-ap-assoc' : {A B : Type} (C : B → Type) (f : A → B) {M N : A} (α : Path M N) 
                       → Path (transport (\ x -> C (f x)) α) (transport C (ap f α))
   transport-ap-assoc' C f id = id 

   coe : {A B : Type} -> Path A B -> A -> B
   coe = transport (\ x -> x)

   coe-inv-2 : {A B : Type} -> (α : Path A B) -> {M : _} -> coe α (coe (! α) M) ≃ M
   coe-inv-2 id = id

   coe-inv-1 : {A B : Type} -> (α : Path A B) -> {M : _} -> coe (! α) (coe α M) ≃ M
   coe-inv-1 id = id

   transport-inv-1 : {A : Type} (B : A -> Type) {M N : A} (α : M ≃ N) -> (\y -> transport B (! α) (transport B α y)) ≃ (\ x -> x)
   transport-inv-1 _ id = id

   transport-inv-2 : {A : Type} (B : A -> Type) {M N : A} (α : M ≃ N) -> (\y -> transport B α (transport B (! α) y)) ≃ (\ x -> x)
   transport-inv-2 _ id = id

   ap-o : {A B C : Type} (g : B → C) (f : A → B)
              {M N : A} (α : Path M N)
            → ap (\ x → g (f x)) α ≃ ap g (ap f α)
   ap-o g f id = id
   
   ap-id : {A : Type} {M N : A} (α : Path M N)
          → Path (ap (\ x → x) α) α
   ap-id id = id 
   
   ap-! : {A B : Type} (F : A → B) {M N : A} (α : Path M N)
         → Path (ap F (! α)) (! (ap F α))
   ap-! _ id = id 
   
   ap-∘ : {A B : Type} (F : A → B) {M N P : A} (β : Path N P) (α : Path M N)
        → Path (ap F (β ∘ α)) (ap F β ∘ ap F α)
   ap-∘ _ _ id = id
   
   apd-∘ : {A : Type} {B : A -> Type} (F : (x : A) -> B x) {M N P : A} (β : Path N P) (α : Path M N)
           -> Path (apd F (β ∘ α)) (apd F β ∘ ap (λ x → transport B β x) (apd F α) ∘ ap (λ f → f (F M)) (transport-∘ B β α))
   apd-∘ _ id id = id

   ap-by-id : {A : Type} {f : A → A}
                  (αf : (x : _) → x ≃ f x) 
               → {M N : A} (α : M ≃ N)
               → (ap f α ≃ αf N ∘ α ∘ ! (αf M))
   ap-by-id αf id = ap (λ x → αf _ ∘ x) (! (∘-unit-l (! (αf _)))) ∘ ! (!-inv-r (αf _)) 

   -- FIXME: relation to ap≃2 ?
   ap-by-equals : {A B : Type} {f g : A → B}
                  (α : (x : _) → f x ≃ g x) 
                → {M N : A} (β : M ≃ N)
                → (ap f β ≃ ! (α N) ∘ ap g β ∘ (α M))
   ap-by-equals α id = ! (!-inv-l (α _) ∘ ap (λ x → ! (α _) ∘ x) (∘-unit-l (α _)))

   ap-constant : {A C : Type} {M N : A} (v : C) -> (p : Path M N) -> Path (ap (\ _ -> v) p) id
   ap-constant v id = id 

   transport-constant : {A C : Type} {M N : A} -> (p : Path M N) -> Path (transport (\ _ -> C) p) (\ x -> x)
   transport-constant id = id 

   transport-Path : {Γ A : Type} (f g : Γ → A) {M N : Γ} (p : Path M N)
                  → (p' : _) → Path (transport (\ x → Path (f x) (g x)) p p')
                                      ((ap g p) ∘ p' ∘ (! (ap f p)))
   transport-Path _ _ id p' = ! (∘-unit-l p')

   transport-Path-d : {Γ : Type} {A : Γ -> Type} (f g : (x : Γ) -> A x) {M N : Γ} (p : Path M N)
              -> (p' : f M ≃ g M) 
              -> Path (transport (\ x -> Path (f x) (g x)) p p')
                    (apd g p ∘ ap (transport A p) p' ∘ ! (apd f p))
   transport-Path-d _ _ id p' = ! (∘-unit-l p' ∘ ap (λ x → id ∘ x) (ap-id p'))

   transport-Path-pre : {A : Type} {M N P : A} (p' : Path N M) (p : Path N P)
                 -> Path (transport (\ x -> Path x P) p' p) (p ∘ ! p')
   transport-Path-pre id id = id -- FIXME J

   transport-com-for-ap-of-transport : 
       {Γ : Type} {θ1 θ2 : Γ} (δ : θ1 ≃ θ2)
       (A : Γ -> Type) (C : (γ : Γ) -> A γ -> Type)
       (M1 M2 : (γ : Γ) -> A γ)
       (α : (γ : Γ) -> M1 γ ≃ M2 γ)
       (M : (γ : Γ) -> C γ (M1 γ))
    -> Path (transport (λ z → C z (M2 z)) δ (transport (C θ1) (α θ1) (M θ1)))
          (transport (λ _ → C θ2 (M2 θ2)) (apd M δ)
                 (transport (C θ2) (α θ2) (transport (λ z → C z (M1 z)) δ (M θ1))))
   transport-com-for-ap-of-transport id A C M1 M2 α M = id

   ap-of-transport : {Γ : Type} {θ1 θ2 : Γ} {δ : θ1 ≃ θ2}
                   {A : Γ -> Type} {C : (γ : Γ) -> A γ -> Type}
                   {M1 M2 : (γ : Γ) -> A γ}
                   {α : (γ : Γ) -> M1 γ ≃ M2 γ}
                   {M : (γ : Γ) -> C γ (M1 γ)}
                -> apd (\ γ -> transport (C γ) (α γ) (M γ)) δ 
                   ≃ apd (λ x → transport (C θ2) (α θ2) x) (apd M δ) 
                     ∘ transport-com-for-ap-of-transport δ A C M1 M2 α M
   ap-of-transport {δ = id} = id 

   ap2 : ∀ {A B C} {M N : A} {M' N' : B} (f : A -> B -> C) -> Path M N -> Path M' N' -> Path (f M M') (f N N')
   ap2 f id id = id

   ap2-aps-1 : ∀ {A B C} {M N : A} {M' N' : B} (f : A -> B -> C) -> (α : Path M N) (β : Path M' N')
                   -> Path (ap2 f α β) (ap (λ x → f x N') α ∘ ap (λ y → f M y) β)
   ap2-aps-1 f id id = id 

   ap2-aps-2 : ∀ {A B C} {M N : A} {M' N' : B} (f : A -> B -> C) -> (α : Path M N) (β : Path M' N')
                   -> Path (ap2 f α β) (ap (λ y → f N y) β ∘ ap (λ x → f x M') α)
   ap2-aps-2 f id id = id 

   ap2-β1 : ∀ {A B} {M N : A} {M' N' : B} -> (α : Path M N) -> (β : Path M' N')
            -> Path (ap2 (\ x y -> x) α β) α
   ap2-β1 id id = id

   ap∘ : {A : Type} {x y z : A} {p q : Path x y} {p' q' : Path y z} 
             -> Path p' q' -> Path p q -> Path (p' ∘ p) (q' ∘ q) 
   ap∘ a b = ap2 _∘_ a b 

   ap-ap : {A B : Type} {f g : A -> B}
                (α : f ≃ g) 
             -> {M N : A} (β : M ≃ N)
             -> (ap f β ≃ ! (ap (\ f -> f N) α)  ∘ ap g β ∘ ap (\ f -> f M) α)
   ap-ap id id = id

   ap2-ap : {A B C : Type} {f g : A -> B -> C}
                (α : f ≃ g) 
             -> {M N : A} (β : M ≃ N)
             -> {M' N' : B} (β' : M' ≃ N')
             -> (ap2 f β β' ≃ ! (ap (\ f -> f N N') α)  ∘ ap2 g β β' ∘ ap (\ f -> f M M') α)
   ap2-ap id id id = id
  
   ap∘-unit-r : {A : Type} {x y : A} {p q : Path x y} 
                    -> (a : Path p q) -> Path (ap∘ a (id{_}{id})) a -- definitional equalities work out such that this works unadjusted
   ap∘-unit-r a = jay (λ _ _ p → Path (ap∘ p (id {_} {id})) p) a (λ _ → id)
  
   ap∘-unit-l : {A : Type} {x y : A} {p q : Path x y} 
                    -> (a : Path p q) -> Path (ap∘ (id{_}{id}) a)
                                          (! (∘-unit-l q) ∘ a ∘ ∘-unit-l p)
               -- definitional equalities work out such that you need an adjustment on the right
   ap∘-unit-l {A}{x}{y}{p}{.p} id = lemma p where
     lemma : {x y : A} (q : Path x y) -> Path id (! (∘-unit-l q) ∘ id ∘ ∘-unit-l q)
     lemma id = id

   -- interchange law for a particular type A
   -- objects = terms of type A
   -- morphisms = Path{A}
   -- 2-cells = Path{Path}
   -- 
   -- see Functions.agda for the interchange law for the type theory as a whole,
   -- viewed as a higher category
   ichange-type : {A : Type} {x y z : A} 
                  {p q r : Path x y} {p' q' r' : Path y z}
                -> (a : Path p q) (b : Path q r) (c : Path p' q') (d : Path q' r') 
                -> Path (ap∘ (d ∘ c) (b ∘ a)) (ap∘ d b ∘ ap∘ c a)
   ichange-type id id id id = id


   -- interderivability
   module PaulinMohring where
     jayfrompm : {A : Type} (C : (x y : A) -> Path x y -> Type)
       -> {M N : A} -> (P : Path M N)
       -> ((x : A) -> C x x id)
       -> C M N P
     jayfrompm {A} C {M}{N} P b = path-induction (λ x (p : Path M x) → C M x p) (b M) P

     pmfromjay : {A : Type} {M : A} (C : (N' : A) -> Path M N' -> Type)
       -> {N : A} -> (P : Path M N)
       -> (C M id)
       -> C N P
     pmfromjay {A}{M} C {N} P b = 
       (jay (λ M' N' (P' : Path M' N') → (C' : (N'' : A) → Path M' N'' → Type) → C' M' id → C' N' P') 
            P 
            (λ M' C' b' → b'))
       C b

     jayfrompm2 : {A : Type} (C : (x y : A) -> Path x y -> Type)
       -> {M N : A} -> (P : Path M N)
       -> ((x : A) -> C x x id)
       -> C M N P
     jayfrompm2 {A} C {M}{N} P b = transport (λ p → C M N p) (!-invol P)
                                     (path-induction (λ x p → C x N (! p)) (b N) (! P))

     fire-jay-const1 : {A : Type} {B : Type} 
          {M N : A} -> (P : Path M N)
       -> (f : A -> B)
       -> Path (jayfrompm (\ _ _ _ -> B) P f) (f M)
     fire-jay-const1 {A}{B} P f = jay (λ x y p → Path (jayfrompm (λ _ _ _ → B) p f) (f x)) P (\ _ -> id)

     fire-jay-const2 : {A : Type} {B : Type} 
          {M N : A} -> (P : Path M N)
       -> (f : A -> B)
       -> Path (jayfrompm2 (\ _ _ _ -> B) P f) (f N)
     fire-jay-const2 {A}{B} P f = jay (λ x y p → Path (jayfrompm2 (λ _ _ _ → B) p f) (f y)) P (\ _ -> id)