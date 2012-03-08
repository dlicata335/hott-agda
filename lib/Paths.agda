
{-# OPTIONS --type-in-type --without-K #-}

-- identity types that never use K
-- homotopically, Id M N is thought of as a path from M to N
-- we also use M ≃ N and Paths M N as notation for Id M N

module lib.Paths where
 data Id {A : Set} : A -> A -> Set where
   Refl : {a : A} -> Id a a

 _≃_ : {A : Set} -> A -> A -> Set
 _≃_ = Id

 infix 9 _≃_

 Paths : {A : Set} -> A -> A -> Set
 Paths = Id

 -- type-indepdendent operations on paths

 module Paths where
   -- define the operations using pattern-matching 
   -- this version makes it much easier to read normalized goals

   jay : {A : Set} (C : (x y : A) -> Id x y -> Set)
       -> {M N : A} -> (P : Id M N)
       -> ((x : A) -> C x x Refl)
       -> C M N P
   jay _ Refl b = b _

   jay1 : {A : Set} {M : A} (C : (x : A) -> Id M x -> Set)
       -> {N : A} -> (P : Id M N)
       -> (C M Refl)
       -> C N P
   jay1 _ Refl b = b

   subst : {A : Set} (p : A -> Set) {x y : A} -> Id x y -> p x -> p y
   subst C Refl =  λ x' → x'

   resp : {A C : Set} {M N : A} (f : A -> C) -> Id M N -> Id (f M) (f N)
   resp f Refl = Refl

   respd : {A : Set} {C : A -> Set} {M N : A} (f : (x : A) -> C x) -> (p : Id M N) -> Id (subst C p (f M)) (f N)
   respd f Refl = Refl

   trans : {A : Set} {M N P : A} -> Id M N -> Id N P -> Id M P
   trans Refl p = p

   _∘_ : {A : Set} {M N P : A} -> Id N P -> Id M N -> Id M P
   β ∘ Refl = β

   infixr 10 _∘_ 

   sym : {a : Set} {x y : a} -> Id x y -> Id y x 
   sym Refl = Refl

   ! : {a : Set} {x y : a} -> Id x y -> Id y x 
   ! Refl = Refl

   trans-unit-l : {A : Set} {M N : A} -> (p : Id M N) -> Id (trans Refl p) p
   trans-unit-l Refl = Refl

   trans-unit-r : {A : Set} {M N : A} -> (p : Id M N) -> Id (trans p Refl) p
   trans-unit-r Refl = Refl

   ∘-unit-l : {A : Set} {M N : A} -> (p : Id M N) -> Id (Refl ∘ p) p
   ∘-unit-l Refl = Refl

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

   subst-Id : {Γ A : Set} (f g : Γ -> A) {M N : Γ} (p : Id M N)
              -> (p' : _) -> Id (subst (\ x -> Id (f x) (g x)) p p') ((resp g p) ∘ p' ∘ (! (resp f p)))
   subst-Id _ _ Refl p' = ! (∘-unit-l p')

   subst-Id-post : {A : Set} {M N P : A} (p' : Id N P) (p : Id M N)
                 -> Id (subst (\ x -> Id M x) p' p) (p' ∘ p)
   subst-Id-post Refl Refl = Refl -- FIXME J

   subst-resp : {A : Set} (C : A -> Set) {M N : A} (α : Id M N) -> Id (subst C α) (subst (\ x -> x) (resp C α))
   subst-resp C Refl = Refl 

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

   resp-id : {A : Set} {M N : A} (α : Id M N)
           -> Id (resp (\ x -> x) α) α
   resp-id Refl = Refl 

   resp-by-id : {A : Set} {f : A -> A}
                (αf : (x : _) -> x ≃ f x) 
             -> {M N : A} (α : M ≃ N)
             -> (resp {_}{_}{M}{N} f α ≃ αf N ∘ α ∘ ! (αf M))
   resp-by-id αf Refl = resp (λ x → αf _ ∘ x) (! (∘-unit-l (! (αf _)))) ∘ ! (!-inv-r (αf _)) 

   subst-∘ : {A : Set} (C : A -> Set) {M N P : A} (β : Id N P) (α : Id M N) 
           -> Id (subst C (β ∘ α)) (\ x -> subst C β (subst C α x))
   subst-∘ C _ Refl = Refl 

   resp2 : ∀ {A B C} {M N : A} {M' N' : B} (f : A -> B -> C) -> Id M N -> Id M' N' -> Id (f M M') (f N N')
   resp2 f Refl Refl = Refl

   resp∘ : {A : Set} {x y z : A} {p q : Id x y} {p' q' : Id y z} 
             -> Id p' q' -> Id p q -> Id (p' ∘ p) (q' ∘ q) 
   resp∘ a b = resp2 _∘_ a b 
  
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
  
   -- would be a one-liner using pattern matching
   -- nothing about the interchange law depends on talking about loops
   trans-resp∘-ichange : {A : Set} {x y z : A} 
               (p q : Id x y) 
            -> (a : Id p q) (r : Id x y) (b : Id q r) 
               (p' q' : Id y z) (c : Id p' q') 
               (r' : Id y z) (d : Id q' r') 
            -> Id (resp∘ (d ∘ c) (b ∘ a)) (resp∘ d b ∘ resp∘ c a)
   trans-resp∘-ichange {A}{x}{y}{z} p .p Refl r b p' .p' Refl .p' Refl = Refl

   infix  2 _∎
   infixr 2 _≃〈_〉_ 
   
   _≃〈_〉_ : {A : Set} (x : A) {y z : A} → Id x y → Id y z → Id x z
   _ ≃〈 p1 〉 p2 = (p2 ∘ p1)
  
   _∎ : ∀ {A : Set} (x : A) → Id x x
   _∎ _ = Refl

   module PaulinMohring where
     jayfrompm : {A : Set} (C : (x y : A) -> Id x y -> Set)
       -> {M N : A} -> (P : Id M N)
       -> ((x : A) -> C x x Refl)
       -> C M N P
     jayfrompm {A} C {M}{N} P b = jay1 (λ x p → C M x p) {N} P (b M)

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

 module PathsOfficial where
   -- derive everything from J
 
   jay : {A : Set} (C : (x y : A) -> Id x y -> Set)
       -> {M N : A} -> (P : Id M N)
       -> ((x : A) -> C x x Refl)
       -> C M N P
   jay _ Refl b = b _
  
   subst : {A : Set} (p : A -> Set) {x y : A} -> Id x y -> p x -> p y
   subst C p = jay (λ x y _ → C x → C y) p (λ x → λ x' → x')
  
   resp : {A C : Set} {M N : A} (f : A -> C) -> Id M N -> Id (f M) (f N)
   resp {A}{C}{M}{N} f a = subst (\ x -> Id (f M) (f x)) a Refl
  
   resp2 : ∀ {A B C} {M N : A} {M' N' : B} (f : A -> B -> C) -> Id M N -> Id M' N' -> Id (f M M') (f N N')
   resp2 {A}{B}{C}{M}{N}{M'}{N'} f a b = 
     subst (\ x -> Id (f M M') (f x N')) a (subst (λ x → Id (f M M') (f M x)) b Refl) 
  
   trans : {A : Set} {M N P : A} -> Id M N -> Id N P -> Id M P
   trans {A}{M}{N}{P} a b = subst (\ x -> Id M x) b a
  
   sym : {a : Set} {x y : a} -> Id x y -> Id y x 
   sym p = jay (λ x y _ → Id y x) p (λ _ → Refl)
  
   trans-unit-l : {A : Set} {M N : A} -> (p : Id M N) -> Id (trans Refl p) p
   trans-unit-l p = jay (λ _ _ p' → Id (trans Refl p') p') p (λ _ → Refl)
  
   trans-unit-r : {A : Set} {M N : A} -> (p : Id M N) -> Id (trans p Refl) p
   trans-unit-r p = Refl
  
   sym-inv : {A : Set} {M N : A} (p : Id M N) -> Id (trans p (sym p)) Refl
   sym-inv p = jay (λ x y p' → Id (trans p' (sym p')) Refl) p (\ _ -> Refl)

   resptrans : {A : Set} {x y z : A} {p q : Id x y} {p' q' : Id y z} 
             -> Id p q -> Id p' q' -> Id (trans p p') (trans q q') 
   resptrans a b = resp2 trans a b 
  
   resptrans-unit-r : {A : Set} {x y : A} {p q : Id x y} 
                    -> (a : Id p q) -> Id (resptrans a (Refl{_}{Refl})) a -- definitional equalities work out such that this works unadjusted
   resptrans-unit-r a = jay (λ _ _ p → Id (resptrans p (Refl {_} {Refl})) p) a (λ _ → Refl)
  
   resptrans-unit-l : {A : Set} {x y : A} {p q : Id x y} 
                    -> (a : Id p q) -> Id (resptrans (Refl{_}{Refl}) a)
                                          ((trans (trans-unit-l p) (trans a (sym (trans-unit-l q)))) )
               -- definitional equalities work out such that you need an adjustment on the right
   resptrans-unit-l a = jay {_}
                          (λ p' q' a' →
                             Id (resp (trans Refl) a')
                             (trans (trans-unit-l p') (trans a' (sym (trans-unit-l q')))))
                          {_} {_} a
                          (λ x →
                             jay
                             (λ xend _ x' →
                                Id Refl
                                (subst (Id (subst (Id xend) x' Refl))
                                 (subst (Id x')
                                  (jay (λ x0 y _ → Id y x0)
                                   (jay (λ _ _ p' → Id (subst (Id _) p' Refl) p') x' (λ _ → Refl))
                                   (λ _ → Refl))
                                  Refl)
                                 (jay (λ _ _ p' → Id (subst (Id _) p' Refl) p') x' (λ _ → Refl))))
                             x (λ _ → Refl))
  
   -- would be a one-liner using pattern matching
   -- nothing about the interchange law depends on talking about loops
   trans-resptrans-ichange : {A : Set} {x y z : A} 
               (p q : Id x y) 
            -> (a : Id p q) (r : Id x y) (b : Id q r) 
               (p' q' : Id y z) (c : Id p' q') 
               (r' : Id y z) (d : Id q' r') 
            -> Id (resptrans (trans a b) (trans c d)) (trans (resptrans a c) (resptrans b d))
   trans-resptrans-ichange {A}{x}{y}{z} p q a = jay
                   (λ p' q' a' →
                      (r : Id x y) (b : Id q' r) (p0 q0 : Id y z) (c : Id p0 q0) (r' : Id y z)
                      (d : Id q0 r') →
                      Id (resptrans (trans a' b) (trans c d))
                      (trans (resptrans a' c) (resptrans b d)))
                   a
                   (λ pq r b →
                      jay
                      (λ pq' r' b' →
                         (p' q' : Id y z) (c : Id p' q') (r0 : Id y z) (d : Id q' r0) →
                         Id (resptrans (trans Refl b') (trans c d))
                         (trans (resptrans Refl c) (resptrans b' d)))
                      b
                      (λ pqr p' q' c →
                         jay
                         (λ p0 q0 c' →
                            (r' : Id y z) (d : Id q0 r') →
                            Id (resptrans Refl (trans c' d))
                            (trans (resptrans Refl c') (resptrans Refl d)))
                         c
                         (λ p'q' r' d →
                            jay
                            (λ p'q0 r0 d' →
                               Id (resptrans Refl (trans Refl d'))
                               (trans Refl (resptrans Refl d')))
                            d (λ _ → Refl))))


   {- more general interchange?
   hcomp : {Γ : Set} {Δ : Set} {θ1' θ2' : Γ -> Δ} {θ1 θ2 : Γ} 
           -> (δ1 : Id θ1' θ2')
           -> (δ2 : Id θ1 θ2)
           -> Id (θ1' θ1) (θ2' θ2)
   hcomp δ1 δ2 = resp2 (λ x y → x y) δ1 δ2
  
   ichange : {Γ : Set} {Δ : Set} {θ1' θ2' θ3' : Γ -> Δ} {θ1 θ2 θ3 : Γ} 
           -> (δ1' : Id θ1' θ2')
           -> (δ1 : Id θ1 θ2)
           -> (δ2' : Id θ2' θ3')
           -> (δ2 : Id θ2 θ3)
           -> Id (hcomp (trans δ1' δ2') (trans δ1 δ2)) (trans (hcomp δ1' δ1) (hcomp δ2' δ2))
   ichange δ1' δ1 δ2' δ2 = {!!}
   -}
  
   -- fire-subst : {Γ A : Set} (f g : Γ -> A) {M N : Γ} {p : Id M N}
   --            -> (p' : Id (f M) (g M)) -> Id (subst (\ x -> Id (f x) (g x)) p p') (trans (sym (resp f p)) (trans {!!} (resp g p)))
   -- fire-subst _ _ {p = Refl} p' = sym (trans (trans-unit-l (trans p' Refl)) (trans-unit-r _)) -- FIXME do with J

   -- syntax for equality chain reasoning
  
   infix  2 _∎
   infixr 2 _≃〈_〉_ 
   
   _≃〈_〉_ : {A : Set} (x : A) {y z : A} → Id x y → Id y z → Id x z
   _ ≃〈 p1 〉 p2 = (trans p1 p2)
  
   _∎ : ∀ {A : Set} (x : A) → Id x x
   _∎ _ = Refl
