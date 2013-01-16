
{-# OPTIONS --type-in-type --without-K #-}

-- identity types that never use K
-- homotopically, Id M N is thought of as a path from M to N
-- we also use M ≃ N and Paths M N as notation for Id M N

open import lib.Paths
open Paths
open import lib.Prods using (Σ ; fst ; snd ; _,_ ; _×_)
open import lib.Functions using (λ≃)
open lib.Prods.NDPair using (nondep-pair≃)

module lib-pp.Paths where

 data PPath {Γ : Set} (A : Γ -> Set) : {θ1 θ2 : Γ} (δ : θ1 ≃ θ2) -> A θ1 -> A θ2 -> Set where
   Refl : {θ : Γ} {a : A θ} -> PPath A Refl a a

 cpair≃ : {Γ : Set} {A : Γ -> Set}  {θ1 θ2 : Γ} (δ : θ1 ≃ θ2) 
          {M1 : A θ1} {M2 : A θ2} (α : PPath A δ M1 M2)
       -> Id{Σ A} (θ1 , M1) (θ2 , M2)
 cpair≃ ._ Refl = Refl

{-
 adjust-basepath : {Γ : Set} {θ1 θ2 : Γ} {δ1 δ2 : θ1 ≃ θ2} (γ : δ1 ≃ δ2)
                   {A : Γ -> Set}
                   {a1 : A θ1} {a2 : A θ2} (α : PPath A δ1 a1 a2) 
                -> PPath A δ2 a1 a2
 adjust-basepath Refl Refl = Refl

 prespd : {Γ : Set} {θ1 θ2 : Γ} {δ : θ1 ≃ θ2}
          {A : Γ -> Set} {B : (θ : Γ) (x : A θ) -> Set}
          (f : (g : Γ) (x : A g) -> B g x)
          {a1 : A θ1} {a2 : A θ2} (α : PPath A δ a1 a2) 
       -> PPath (\ (p : Σ A) -> B (fst p) (snd p)) (cpair≃ δ α) (f _ a1) (f _ a2)
 prespd f Refl = Refl
-}

 presp : {Γ : Set} {θ1 θ2 : Γ} 
         {A : Γ -> Set} 
         (f : (g : Γ) -> (A g)) (δ : θ1 ≃ θ2)
       -> PPath A δ (f θ1) (f θ2)
 presp f Refl = Refl

 fndpair≃ : {Γ : Set} {A B : Γ -> Set} {θ1 θ2 : Γ} {δ : θ1 ≃ θ2}
            {M1 : A θ1} {N1 : B θ1} {M2 : A θ2} {N2 : B θ2} 
            (α : PPath A δ M1 M2)
            (β : PPath B δ N1 N2)
         -> PPath (\ g -> A g × B g) δ (M1 , N1) (M2 , N2)
 fndpair≃ {B = B} {M2 = M2} Refl p = {!presp (\ (p : Σ B) -> M2 , snd p) (cpair≃ Refl p)!}

 cfst≃ : {Γ : Set} {A : Γ -> Set} {p1 p2 : Σ A} (δ : p1 ≃ p2) 
       -> fst p1 ≃ fst p2
 cfst≃ = resp fst
         
 csnd≃ : {Γ : Set} {A : Γ -> Set} {p1 p2 : Σ A} (δ : p1 ≃ p2) 
       -> PPath (\ x -> A (fst x)) δ (snd p1) (snd p2)  -- ENH : could also be PPath A (cfst≃ δ)
 csnd≃ δ = presp snd δ
         
 _∘p_ : {Γ : Set} {θ1 θ2 θ3 : Γ} {δ12 : θ1 ≃ θ2} {δ23 : θ2 ≃ θ3}
        {A : Γ -> Set}
        {a1 : A θ1} {a2 : A θ2} {a3 : A θ3} (α23 : PPath A δ23 a2 a3)  (α12 : PPath A δ12 a1 a2) 
     -> PPath A (δ23 ∘ δ12) a1 a3
 _∘p_ Refl Refl = Refl

 infixr 10 _∘p_ 

 !p_ : {Γ : Set} {θ1 θ2 : Γ} {δ : θ1 ≃ θ2} 
       {A : Γ -> Set}
       {a1 : A θ1} {a2 : A θ2} (α : PPath A δ a1 a2) 
     -> PPath A (! δ) a2 a1
 !p Refl = Refl

 coeh : {Γ : Set} {θ1 θ2 : Γ} {δ : θ1 ≃ θ2} 
        (A : Γ -> Set) (a1 : A θ1)
      -> PPath A δ a1 (subst A δ a1)
 coeh {δ = Refl} A a1 = Refl

 coeh- : {Γ : Set} {θ1 θ2 : Γ} {δ : θ1 ≃ θ2} 
         (A : Γ -> Set) (a2 : A θ2)
      -> PPath A δ (subst A (! δ) a2) a2
 coeh- {δ = Refl} A a1 = Refl

 -- == functions ==

 postulate
   λ≃f  : {Γ : Set} {θ1 θ2 : Γ} {δ : θ1 ≃ θ2}
         {A : Γ -> Set} {B : (θ : Γ) (x : A θ) -> Set}
         {f : (x : A θ1) -> B θ1 x} {g : (x : A θ2) -> B θ2 x}
      -> ((x : A θ1) -> PPath (\ (p : Σ A) -> B (fst p) (snd p)) (cpair≃ δ (coeh A x)) (f x) (g (subst A δ x)))
      -> PPath (\ θ -> (x : A θ) -> (B θ x)) δ f g 

   λ≃f'  : {Γ : Set} {θ1 θ2 : Γ} {δ : θ1 ≃ θ2}
         {A : Γ -> Set} {B : (θ : Γ) (x : A θ) -> Set}
         {f : (x : A θ1) -> B θ1 x} {g : (x : A θ2) -> B θ2 x}
      -> ((x : A θ1) (y : A θ2) (α : PPath A δ x y) 
          -> PPath (\ (p : Σ A) -> B (fst p) (snd p)) (cpair≃ δ α) (f x) (g y))
      -> PPath (\ θ -> (x : A θ) -> (B θ x)) δ f g 

 papp≃ : {Γ : Set} {θ1 θ2 : Γ} {δ : θ1 ≃ θ2}
         {A : Γ -> Set} {B : (θ : Γ) (x : A θ) -> Set}
         {f : (x : A θ1) -> B θ1 x} {g : (x : A θ2) -> B θ2 x}
      -> PPath (\ θ -> (x : A θ) -> (B θ x)) δ f g 
      -> {x1 : A θ1} {x2 : A θ2} (α : PPath A δ x1 x2)
      -> PPath (\ (p : Σ A) -> B (fst p) (snd p)) (cpair≃ δ α) (f x1) (g x2)
 papp≃ p Refl = {!p!}

 subst-Π : ∀ {Γ} (A : Γ -> Set) (B : (γ : Γ) -> A γ -> Set)
            {θ1 θ2 : Γ} (δ : θ1 ≃ θ2) (f : (x : A θ1) -> B θ1 x) 
         -> subst (\ γ -> (x : A γ) -> B γ x) δ f ≃ 
            (\ x -> subst (\ (p : Σ \ (γ : Γ) -> A γ) -> B (fst p) (snd p))
                          (cpair≃ δ (coeh- A x))
                          (f (subst A (! δ) x)))
 subst-Π _ _ Refl f = Refl

 subst-Π' : ∀ {Γ} (A : Γ -> Set) (B : (γ : Γ) -> A γ -> Set)
              {θ1 θ2 : Γ} (δ : θ1 ≃ θ2) (f : (x : A θ1) -> B θ1 x) 
         -> PPath (\ θ -> (x : A θ) -> B θ x) 
                  Refl
                  (subst (\ γ -> (x : A γ) -> B γ x) δ f)
                  (\ x -> subst (\ (p : Σ \ (γ : Γ) -> A γ) -> B (fst p) (snd p))
                                (cpair≃ δ (coeh- A x))
                                (f (subst A (! δ) x)))
 subst-Π' _ _ Refl f = Refl

{-
 weaken1 : {Γ : Set} {A : Γ -> Set} {θ1 θ2 : Γ} {M1 : A θ1} {M2 : A θ2}
            {δ : θ1 ≃ θ2} {α : PPath A δ M1 M2} 
            {B : Γ -> Set} {b1 : B θ1} {b2 : B θ2}
         -> PPath B δ b1 b2
         -> PPath (\ p -> B (fst p)) (cpair≃ δ α) b1 b2
 weaken1 {α = Refl} p = {!p!}
-}

 weaken1-nd : {Γ Γ' : Set} {θ1 θ2 : Γ} {θ1' θ2' : Γ'}
              {δ : θ1 ≃ θ2} {δ' : θ1' ≃ θ2'}
              {B : Γ -> Set} {b1 : B θ1} {b2 : B θ2}
           -> PPath B δ b1 b2
           -> PPath (\ p -> B (fst p)) (nondep-pair≃ δ δ') b1 b2
 weaken1-nd {δ' = Refl} Refl = Refl

 weaken2-nd : {Γ Γ' : Set} {θ1 θ2 : Γ} {θ1' θ2' : Γ'}
              {δ : θ1 ≃ θ2} {δ' : θ1' ≃ θ2'}
              {B : Γ' -> Set} {b1 : B θ1'} {b2 : B θ2'}
           -> PPath B δ' b1 b2
           -> PPath (\ p -> B (snd p)) (nondep-pair≃ δ δ') b1 b2
 weaken2-nd {δ = Refl} Refl = Refl
         
 square-ppath : {Γ : Set} {θ1 θ2 θ1' θ2' : Γ}
          {δ12 : θ1 ≃ θ2} {δ12' : θ1' ≃ θ2'} {δ11 : θ1 ≃ θ1'} {δ22 : θ2 ≃ θ2'}
       -> (δ22 ∘ δ12) ≃ (δ12' ∘ δ11)
       -> PPath (λ z → Id (fst z) (snd z)) (resp2 _,_ δ11 δ22) δ12 δ12'
 square-ppath {δ12 = Refl}{δ12' = Refl}{δ11 = Refl} p = {!!} 

 FSquare : {Γ : Set} {θ1 θ2 θ1' θ2' : Γ}
           {δ12 : θ1 ≃ θ2} {δ12' : θ1' ≃ θ2'} {δ11 : θ1 ≃ θ1'} {δ22 : θ2 ≃ θ2'}
           (bsqaure : (δ22 ∘ δ12) ≃ (δ12' ∘ δ11))
           {A : Γ -> Set}
           {a1 : A θ1} {a2 : A θ2} {a1' : A θ1'} {a2' : A θ2'}
           (α12 : PPath A δ12 a1 a2)  
           (α12' : PPath A δ12' a1' a2')  
           (α11 : PPath A δ11 a1 a1')  
           (α22 : PPath A δ22 a2 a2')  
         -> Set
 FSquare {Γ} {θ1}{θ2}{θ1'}{θ2'}{δ12}{δ12'}{δ11}{δ22} bsquare {A}{a1}{a2}{a1'}{a2'} α12 α12' α11 α22 = 
   PPath
     (λ (p : Σ (λ (θ12 : Γ × Γ) → Id (fst θ12) (snd θ12) × A (fst θ12) × A (snd θ12))) →
        PPath A (fst (snd p)) (fst (snd (snd p))) (snd (snd (snd p))))
     (cpair≃ (nondep-pair≃ δ11 δ22) (fndpair≃ (square-ppath bsquare) (fndpair≃ (weaken1-nd α11) (weaken2-nd α22)))) --weakening
     α12 α12'

 path->ppath : ∀ {A} {M1 M2 : A} -> M1 ≃ M2 -> {Γ : Set}{θ : Γ} -> PPath (\ _ -> A) (Refl{_}{θ}) M1 M2
 path->ppath Refl = Refl

 homog :  {Γ : Set} {A : Γ -> Set} {θ1 θ2 : Γ} {δ : θ1 ≃ θ2} {a1 : A θ1} {a2 : A θ2}
       -> PPath A δ a1 a2
       -> subst A δ a1 ≃ a2
 homog Refl = Refl

 heterog :  {Γ : Set} {A : Γ -> Set} {θ1 θ2 : Γ} {δ : θ1 ≃ θ2} {a1 : A θ1} {a2 : A θ2}
       -> subst A δ a1 ≃ a2
       -> PPath A δ a1 a2
 heterog {δ = Refl} Refl = Refl

 homog-coeh : {Γ : Set} {A : Γ -> Set} {θ1 θ2 : Γ} {δ : θ1 ≃ θ2} {a1 : A θ1}
            -> homog (coeh {δ = δ} A a1) ≃ Refl
 homog-coeh {δ = Refl} = Refl

 heterog-coeh : {Γ : Set} {A : Γ -> Set} {θ1 θ2 : Γ} {δ : θ1 ≃ θ2} {a1 : A θ1}
              -> heterog Refl ≃ coeh {δ = δ} A a1
 heterog-coeh {δ = Refl} = Refl

 coehΠ : {Γ : Set} {θ1 θ2 : Γ} {δ : θ1 ≃ θ2}
         {A : Γ -> Set} {B : (θ : Γ) (x : A θ) -> Set}
         {f : (x : A θ1) -> B θ1 x} 
       -> (coeh{δ = δ} (\ θ -> (x : A θ) -> B θ x) f)
        ≃ heterog (! (subst-Π A B δ f) ∘ (λ≃ (λ x → {!!})) ∘ subst-Π A B δ f)
 coehΠ = {!!}

{- 
 coehΠ : {Γ : Set} {θ1 θ2 : Γ} {δ : θ1 ≃ θ2}
         {A : Γ -> Set} {B : (θ : Γ) (x : A θ) -> Set}
         {f : (x : A θ1) -> B θ1 x} 
      -> FSquare {Γ} {θ1} {θ2} {{!!}} {θ2} 
                 {δ} {δ} {{!!}} {Refl}
                 {!!}
                 {λ θ → (x : A θ) → B θ x}
                 {f} {subst (λ θ → (x : A θ) → B θ x) δ f} 
                 { {!λ x → {!f (subst A (! δ) (subst (λ z → A z) δ x))!}!}} -- guess 
                 {λ x →
                      subst (λ p → B (fst p) (snd p)) (cpair≃ δ (coeh- A x))
                      (f (subst A (! δ) x))}
                 (coeh{δ = δ} (\ θ -> (x : A θ) -> B θ x) f) 
                 (λ≃' (λ x y α → {! (coeh {δ = cpair≃ δ (coeh- A y)} (λ (p : Σ (λ (γ : Γ) → A γ)) → B (fst p) (snd p)) (f (subst A (! δ) y)))!}))
-- ingredients: 
-- (coeh {δ = cpair≃ δ α} (λ (p : Σ (λ (γ : Γ) → A γ)) → B (fst p) (snd p)) (f x))
-- : PPath (λ p → B (fst p) (snd p))
--      (cpair≃ δ α)
--      (f x)
--      (subst (λ p → B (fst p) (snd p)) (cpair≃ δ α) (f x))

-- coeh- {δ = δ} A y : PPath A δ (subst A (! δ) y) y
                 {!!}
                 {! (subst-Π' A B δ f) !}
               -- (λ≃ (λ x → adjust-basepath {!!} 
               --            (coeh {δ = cpair≃ δ (coeh- A (subst (λ z → A z) δ x))}
               --                  (λ (p : Σ (λ (γ : Γ) → A γ)) → B (fst p) (snd p))
               --                  (f (subst A (! δ) (subst (λ z → A z) δ x)))
               --                  ∘p {!presp (\ y -> f (y x)) (! (subst-inv-1 A δ))!})))
 coehΠ = {!!}
-}

 fkan2 : {Γ : Set} {θ1 θ2 θ1' θ2' : Γ}
         {δ12 : θ1 ≃ θ2} {δ12' : θ1' ≃ θ2'} {δ11 : θ1 ≃ θ1'} {δ22 : θ2 ≃ θ2'}
         (bsquare : (δ22 ∘ δ12) ≃ (δ12' ∘ δ11))
         {A : Γ -> Set}
         {a1 : A θ1} {a2 : A θ2} {a1' : A θ1'} {a2' : A θ2'}
         (α12 : PPath A δ12 a1 a2)  
         (α11 : PPath A δ11 a1 a1')  
         (α22 : PPath A δ22 a2 a2')  
         -> Σ \ (α12' : PPath A δ12' a1' a2') -> FSquare bsquare α12 α12' α11 α22
 fkan2 {δ12 = δ12} {δ12' = δ12'} {δ11 = δ11} {δ22 = δ22} bsquare {A}{a1}{a2}{a1'}{a2'} α12 α11 α22 = 
   subst (λ δ → PPath A δ a1' a2') 
         (subst (λ x → x) (move-left _ δ11 _) bsquare ∘ ∘-assoc δ22 δ12 (! δ11))
         (α22 ∘p α12 ∘p !p α11) , 
   {!coeh {δ = (subst (λ x → x) (move-left _ δ11 _) bsquare ∘ ∘-assoc δ22 δ12 (! δ11))} (λ δ → PPath A δ a1' a2') (α22 ∘p α12 ∘p !p α11) ∘p ? !} 



 

 



 -- ∘p-unit-l : {Γ : Set} {θ1 θ2 : Γ} {δ12 : θ1 ≃ θ2}
 --             {A : Γ -> Set}
 --             {a1 : A θ1} {a2 : A θ2} (α12 : PPath A δ12 a1 a2)
 --          -> PPath _ {!!} (Refl ∘p α12) α12
 -- ∘p-unit-l Refl = Refl

{-
   trans-unit-l : {A : Set} {M N : A} -> (p : Id M N) -> Id (trans Refl p) p
   trans-unit-l Refl = Refl

   trans-unit-r : {A : Set} {M N : A} -> (p : Id M N) -> Id (trans p Refl) p
   trans-unit-r Refl = Refl

   ∘-unit-r : {A : Set} {M N : A} -> (p : Id M N) -> Id (p ∘ Refl) p
   ∘-unit-r Refl = Refl

   trans-assoc : {A : Set} {M N P Q : A} -> (p : Id M N) (q : Id N P) (r : Id P Q) -> Id (trans (trans p q) r) (trans p (trans q r))
   trans-assoc Refl Refl Refl = Refl

   ∘-assoc : {A : Set} {M N P Q : A} -> (r : Id P Q) (q : Id N P) (p : Id M N) -> Id (r ∘ (q ∘ p)) ((r ∘ q) ∘ p)
   ∘-assoc Refl Refl Refl = Refl

   sym-inv : {A : Set} {M N : A} (p : Id M N) -> Id (trans p (sym p)) Refl
   sym-inv Refl = Refl

   sym-inv2 : {A : Set} {M N : A} (p : Id M N) -> Id (trans (sym p) p) Refl
   sym-inv2 Refl = Refl

   !-inv-l : {A : Set} {M N : A} (p : Id M N) -> Id ((! p) ∘ p) Refl
   !-inv-l Refl = Refl

   !-inv-r : {A : Set} {M N : A} (p : Id M N) -> Id (p ∘ (! p)) Refl
   !-inv-r Refl = Refl

   sym-invol : {A : Set} {M N : A} (p : Id M N) -> Id (sym (sym p)) p
   sym-invol Refl = Refl

   !-invol : {A : Set} {M N : A} (p : Id M N) -> Id (! (! p)) p
   !-invol Refl = Refl

   !-∘ : {A : Set} {M N P : A} -> (q : Id N P) -> (p : Id M N)
       -> (! (q ∘ p)) ≃ ! p ∘ ! q
   !-∘ Refl Refl = Refl

    -- Moving ! between sides of an Id
   !-left : {X : Set} {M N : X} -> (p : Id M N) -> (q : Id M M) -> (r : Id N N)
         -> Id (p ∘ q ∘ ! p) r ≃ Id (p ∘ q) (r ∘ p)
   !-left Refl q r = Refl
   
   subst-Id : {Γ A : Set} (f g : Γ -> A) {M N : Γ} (p : Id M N)
              -> (p' : _) -> Id (subst (\ x -> Id (f x) (g x)) p p') ((resp g p) ∘ p' ∘ (! (resp f p)))
   subst-Id _ _ Refl p' = ! (∘-unit-l p')

   subst-Id-post : {A : Set} {M N P : A} (p' : Id N P) (p : Id M N)
                 -> Id (subst (\ x -> Id M x) p' p) (p' ∘ p)
   subst-Id-post Refl Refl = Refl -- FIXME J

   subst-Id-pre : {A : Set} {M N P : A} (p' : Id N M) (p : Id N P)
                 -> Id (subst (\ x -> Id x P) p' p) (p ∘ ! p')
   subst-Id-pre Refl Refl = Refl -- FIXME J

   subst-resp : {A : Set} (C : A -> Set) {M N : A} (α : Id M N) -> Id (subst C α) (subst (\ x -> x) (resp C α))
   subst-resp C Refl = Refl 

   subst-resp' : {A A' : Set} (C : A' -> Set) (f : A -> A') 
                 {M N : A} (α : Id M N) -> Id (subst C (resp f α)) (subst (\ x -> C (f x)) α)
   subst-resp' C f Refl = Refl 

   subst-∘ : {A : Set} (C : A -> Set) {M N P : A} (β : Id N P) (α : Id M N)
           -> Id (subst C (β ∘ α)) (\ x -> subst C β (subst C α x))
   subst-∘ _ Refl Refl = Refl

   subst-o : {A B : Set} (C : B -> Set) (f : A -> B)
            {M N : A} (α : M ≃ N)
          -> subst (\ x -> C (f x)) α ≃ subst C (resp f α)
   subst-o _ f Refl = Refl

   -- fire-subst-d : {Γ : Set} {A : Γ -> Set} (f g : (x : Γ) -> A x) {M N : Γ} {p : Id M N}
   --              -> {p' : Id (f M) (g M)} -> Id (subst (\ x -> Id (f x) (g x)) p p') (trans (sym (respd f p)) (trans (resp (subst A p) p') (respd g p)))
   -- fire-subst-d _ _ {p = Refl} {p'} = {!!} 

   swap-left : {A : Set} {M N P : A} {p1 : Id M N} {p2 : Id M P} {p3 : Id N P}
                -> Id p3 ((trans (sym p1)) p2)
                -> Id (trans p1 p3) p2
   swap-left {p1 = Refl} p = trans (trans-unit-l _) (trans p (trans-unit-l _)) 

   resp-constant : {A C : Set} {M N : A} (v : C) -> (p : Id M N) -> Id (resp (\ _ -> v) p) Refl
   resp-constant v Refl = Refl 

   subst-constant : {A C : Set} {M N : A} -> (p : Id M N) -> Id (subst (\ _ -> C) p) (\ x -> x)
   subst-constant Refl = Refl 

   resp-! : {A B : Set} (F : A -> B) {M N : A} (α : Id M N)
           -> Id (resp F (! α)) (! (resp F α))
   resp-! _ Refl = Refl 

   resp-∘ : {A B : Set} (F : A -> B) {M N P : A} (β : Id N P) (α : Id M N)
           -> Id (resp F (β ∘ α)) (resp F β ∘ resp F α)
   resp-∘ _ _ Refl = Refl 

   respd-∘ : {A : Set} {B : A -> Set} (F : (x : A) -> B x) {M N P : A} (β : Id N P) (α : Id M N)
           -> Id (respd F (β ∘ α)) (respd F β ∘ resp (λ x → subst B β x) (respd F α) ∘ resp (λ f → f (F M)) (subst-∘ B β α))
   respd-∘ _ Refl Refl = Refl

   resp-id : {A : Set} {M N : A} (α : Id M N)
           -> Id (resp (\ x -> x) α) α
   resp-id Refl = Refl 

   resp-o : {A B C : Set} (g : B -> C) (f : A -> B)
            {M N : A} (α : M ≃ N)
          -> resp (\ x -> g (f x)) α ≃ resp g (resp f α)
   resp-o g f Refl = Refl

   resp-by-id : {A : Set} {f : A -> A}
                (αf : (x : _) -> x ≃ f x) 
             -> {M N : A} (α : M ≃ N)
             -> (resp f α ≃ αf N ∘ α ∘ ! (αf M))
   resp-by-id αf Refl = resp (λ x → αf _ ∘ x) (! (∘-unit-l (! (αf _)))) ∘ ! (!-inv-r (αf _)) 

   resp2 : ∀ {A B C} {M N : A} {M' N' : B} (f : A -> B -> C) -> Id M N -> Id M' N' -> Id (f M M') (f N N')
   resp2 f Refl Refl = Refl

   resp2-resps-1 : ∀ {A B C} {M N : A} {M' N' : B} (f : A -> B -> C) -> (α : Id M N) (β : Id M' N')
                   -> Id (resp2 f α β) (resp (λ x → f x N') α ∘ resp (λ y → f M y) β)
   resp2-resps-1 f Refl Refl = Refl 

   resp2-resps-2 : ∀ {A B C} {M N : A} {M' N' : B} (f : A -> B -> C) -> (α : Id M N) (β : Id M' N')
                   -> Id (resp2 f α β) (resp (λ y → f N y) β ∘ resp (λ x → f x M') α)
   resp2-resps-2 f Refl Refl = Refl 

   resp2-β1 : ∀ {A B} {M N : A} {M' N' : B} -> (α : Id M N) -> (β : Id M' N')
            -> Id (resp2 (\ x y -> x) α β) α
   resp2-β1 Refl Refl = Refl

   resp∘ : {A : Set} {x y z : A} {p q : Id x y} {p' q' : Id y z} 
             -> Id p' q' -> Id p q -> Id (p' ∘ p) (q' ∘ q) 
   resp∘ a b = resp2 _∘_ a b 

   resp-resp : {A B : Set} {f g : A -> B}
                (α : f ≃ g) 
             -> {M N : A} (β : M ≃ N)
             -> (resp f β ≃ ! (resp (\ f -> f N) α)  ∘ resp g β ∘ resp (\ f -> f M) α)
   resp-resp Refl Refl = Refl

   resp2-resp : {A B C : Set} {f g : A -> B -> C}
                (α : f ≃ g) 
             -> {M N : A} (β : M ≃ N)
             -> {M' N' : B} (β' : M' ≃ N')
             -> (resp2 f β β' ≃ ! (resp (\ f -> f N N') α)  ∘ resp2 g β β' ∘ resp (\ f -> f M M') α)
   resp2-resp Refl Refl Refl = Refl
  
   resp∘-unit-r : {A : Set} {x y : A} {p q : Id x y} 
                    -> (a : Id p q) -> Id (resp∘ a (Refl{_}{Refl})) a -- definitional equalities work out such that this works unadjusted
   resp∘-unit-r a = jay (λ _ _ p → Id (resp∘ p (Refl {_} {Refl})) p) a (λ _ → Refl)
  
   resp∘-unit-l : {A : Set} {x y : A} {p q : Id x y} 
                    -> (a : Id p q) -> Id (resp∘ (Refl{_}{Refl}) a)
                                          (! (∘-unit-l q) ∘ a ∘ ∘-unit-l p)
               -- definitional equalities work out such that you need an adjustment on the right
   resp∘-unit-l {A}{x}{y}{p}{.p} Refl = lemma p where
     lemma : {x y : A} (q : Id x y) -> Id Refl (! (∘-unit-l q) ∘ Refl ∘ ∘-unit-l q)
     lemma Refl = Refl

   subst-Id-d : {Γ : Set} {A : Γ -> Set} (f g : (x : Γ) -> A x) {M N : Γ} (p : Id M N)
              -> (p' : f M ≃ g M) 
              -> Id (subst (\ x -> Id (f x) (g x)) p p')
                    (respd g p ∘ resp (subst A p) p' ∘ ! (respd f p))
   subst-Id-d _ _ Refl p' = ! (∘-unit-l p' ∘ resp (λ x → Refl ∘ x) (resp-id p'))


   subst-com-for-resp-of-subst : 
       {Γ : Set} {θ1 θ2 : Γ} (δ : θ1 ≃ θ2)
       (A : Γ -> Set) (C : (γ : Γ) -> A γ -> Set)
       (M1 M2 : (γ : Γ) -> A γ)
       (α : (γ : Γ) -> M1 γ ≃ M2 γ)
       (M : (γ : Γ) -> C γ (M1 γ))
    -> Id (subst (λ z → C z (M2 z)) δ (subst (C θ1) (α θ1) (M θ1)))
          (subst (λ _ → C θ2 (M2 θ2)) (respd M δ)
                 (subst (C θ2) (α θ2) (subst (λ z → C z (M1 z)) δ (M θ1))))
   subst-com-for-resp-of-subst Refl A C M1 M2 α M = Refl

   resp-of-subst : {Γ : Set} {θ1 θ2 : Γ} {δ : θ1 ≃ θ2}
                   {A : Γ -> Set} {C : (γ : Γ) -> A γ -> Set}
                   {M1 M2 : (γ : Γ) -> A γ}
                   {α : (γ : Γ) -> M1 γ ≃ M2 γ}
                   {M : (γ : Γ) -> C γ (M1 γ)}
                -> respd (\ γ -> subst (C γ) (α γ) (M γ)) δ 
                   ≃ respd (λ x → subst (C θ2) (α θ2) x) (respd M δ) 
                     ∘ subst-com-for-resp-of-subst δ A C M1 M2 α M
   resp-of-subst {δ = Refl} = Refl 

   -- interchange law for a particular type A
   -- objects = terms of type A
   -- morphisms = Id{A}
   -- 2-cells = Id{Id}
   -- 
   -- see Functions.agda for the interchange law for the type theory as a whole,
   -- viewed as a higher category
   ichange-type : {A : Set} {x y z : A} 
                  {p q r : Id x y} {p' q' r' : Id y z}
                -> (a : Id p q) (b : Id q r) (c : Id p' q') (d : Id q' r') 
                -> Id (resp∘ (d ∘ c) (b ∘ a)) (resp∘ d b ∘ resp∘ c a)
   ichange-type Refl Refl Refl Refl = Refl

   coe : {A B : Set} -> Id A B -> A -> B
   coe = subst (\ x -> x)

   coe-inv-2 : {A B : Set} -> (α : Id A B) -> {M : _} -> coe α (coe (! α) M) ≃ M
   coe-inv-2 Refl = Refl

   coe-inv-1 : {A B : Set} -> (α : Id A B) -> {M : _} -> coe (! α) (coe α M) ≃ M
   coe-inv-1 Refl = Refl

   subst-inv-1 : {A : Set} (B : A -> Set) {M N : A} (α : M ≃ N) -> (\y -> subst B (! α) (subst B α y)) ≃ (\ x -> x)
   subst-inv-1 _ Refl = Refl

   subst-inv-2 : {A : Set} (B : A -> Set) {M N : A} (α : M ≃ N) -> (\y -> subst B α (subst B (! α) y)) ≃ (\ x -> x)
   subst-inv-2 _ Refl = Refl

   module PaulinMohring where
     jayfrompm : {A : Set} (C : (x y : A) -> Id x y -> Set)
       -> {M N : A} -> (P : Id M N)
       -> ((x : A) -> C x x Refl)
       -> C M N P
     jayfrompm {A} C {M}{N} P b = jay1 (λ x (p : Id M x) → C M x p) P (b M)

     pmfromjay : {A : Set} {M : A} (C : (N' : A) -> Id M N' -> Set)
       -> {N : A} -> (P : Id M N)
       -> (C M Refl)
       -> C N P
     pmfromjay {A}{M} C {N} P b = 
       (jay (λ M' N' (P' : Id M' N') → (C' : (N'' : A) → Id M' N'' → Set) → C' M' Refl → C' N' P') 
            P 
            (λ M' C' b' → b'))
       C b

     jayfrompm2 : {A : Set} (C : (x y : A) -> Id x y -> Set)
       -> {M N : A} -> (P : Id M N)
       -> ((x : A) -> C x x Refl)
       -> C M N P
     jayfrompm2 {A} C {M}{N} P b = subst (λ p → C M N p) (sym-invol P)
                                     (jay1 (λ x p → C x N (sym p)) {M} (sym P) (b N))

     fire-jay-const1 : {A : Set} {B : Set} 
          {M N : A} -> (P : Id M N)
       -> (f : A -> B)
       -> Id (jayfrompm (\ _ _ _ -> B) P f) (f M)
     fire-jay-const1 {A}{B} P f = jay (λ x y p → Id (jayfrompm (λ _ _ _ → B) p f) (f x)) P (\ _ -> Refl)

     fire-jay-const2 : {A : Set} {B : Set} 
          {M N : A} -> (P : Id M N)
       -> (f : A -> B)
       -> Id (jayfrompm2 (\ _ _ _ -> B) P f) (f N)
     fire-jay-const2 {A}{B} P f = jay (λ x y p → Id (jayfrompm2 (λ _ _ _ → B) p f) (f y)) P (\ _ -> Refl)
-}
