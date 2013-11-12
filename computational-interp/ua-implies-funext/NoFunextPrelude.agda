{-# OPTIONS --without-K --type-in-type #-}

module NoFunextPrelude where

 -- ----------------------------------------------------------------------
 -- Agda uses the word "Set" in a way that I want to suppress
 Type = Set

 _o_ : {A B C : Type} → (B → C) → (A → B) → A → C
 g o f = \ x → g (f x)
 infixr 10 _o_


 -- ----------------------------------------------------------------------
 -- paths
   
 data Id {A : Type} (M : A) : A → Type where
   id : Id M M

 Path : {A : Type} → A → A → Type
 Path = Id

 _≃_ : {A : Type} → A → A → Type
 _≃_ = Path

 _==_ : {A : Type} → A → A → Type
 _==_ = Path

 infix 9 _≃_
 infix 9 _==_

 ! : {A : Type} {M N : A} → Path M N → Path N M 
 ! id = id
 
 _∘_  : {A : Type} {M N P : A} 
      → Path N P → Path M N → Path M P
 β ∘ id = β

 infixr 10 _∘_ 

 infix  2 _∎
 infixr 2 _≃〈_〉_ 
 infixr 2 _=〈_〉_ 
 
 _≃〈_〉_ : {A : Type} (x : A) {y z : A} → Path x y → Path y z → Path x z
 _ ≃〈 p1 〉 p2 = (p2 ∘ p1)

 _=〈_〉_ : {A : Type} (x : A) {y z : A} → Path x y → Path y z → Path x z
 _ =〈 p1 〉 p2 = (p2 ∘ p1)
 
 _∎ : ∀ {A : Type} (x : A) → Path x x
 _∎ _ = id

 transport :  {B : Type} (E : B → Type) 
              {b1 b2 : B} → Path b1 b2 → (E b1 → E b2)
 transport C id = λ x → x
 
 ap :  {A B : Type} {M N : A}
       (f : A → B) → Path{A} M N → Path{B} (f M) (f N)
 ap f id = id
 
 apd  :  {B : Type} {E : B → Type} {b₁ b₂ : B} 
         (f : (x : B) → E x) (β : Path b₁ b₂) 
      → Path (transport E β (f b₁)) (f b₂) 
 apd f id = id 

 coe : {A B : Type} -> Path A B -> A -> B
 coe = transport (\ x -> x)


 -- enough lemmas to get through the rest of this file

 ∘-unit-l  : {A : Type} {M N : A} (α : Path M N)
             → Path (id ∘ α) α
 ∘-unit-l id = id

 ∘-unit-r  : {A : Type} {M N : A} (α : Path M N)
           → Path (α ∘ id) α
 ∘-unit-r id = id

 !-invol : {A : Type} {M N : A} (p : Path M N) → Path (! (! p)) p
 !-invol id = id

 -- ∘-assoc  : {A : Type} {a b c d : A} 
 --     (p : Path a b) (q : Path b c) (r : Path c d) 
 --   → Path (r ∘ (q ∘ p)) ((r ∘ q) ∘ p)
 -- ∘-assoc id id id = id

 ∘-assoc  : {A : Type} {M N P Q : A} 
          (γ : Path P Q) (β : Path N P) (α : Path M N) 
          → Path (γ ∘ (β ∘ α)) ((γ ∘ β) ∘ α)
 ∘-assoc id id id = id
 
 !-inv-l  : {A : Type} {M N : A} (α : Path M N) 
            → Path (! α ∘ α) id
 !-inv-l id = id
 
 !-inv-r : {A : Type} {M N : A} (α : Path M N) → Path (α ∘ (! α)) id
 !-inv-r id = id

 !-inv-r-front : {A : Type} {M N P : A} (p : Path P N) (q : Path M N) → Path (p ∘ (! p) ∘ q) q
 !-inv-r-front id id = id
 
 !-inv-r-back : {A : Type} {M N P : A} (q : Path N M) (p : Path P N) → Path (q ∘ (p ∘ ! p)) q
 !-inv-r-back id id = id

 !-inv-l-front : {A : Type} {M N P : A} (p : Path N P) (q : Path M N) → Path (! p ∘ p ∘ q) q
 !-inv-l-front id id = id

 !-inv-l-back : {A : Type} {M N P : A} (q : Path N M) (p : Path N P) → Path (q ∘ ! p ∘ p) q
 !-inv-l-back id id = id

 square-id : {A : Type} {x : A} (p : x ≃ x) -> (p ∘ p) ≃ p → p ≃ id
 square-id p α = !-inv-r p ∘ ap (λ x' → x' ∘ ! p) α ∘ ∘-assoc p p (! p) ∘ ap (λ x' → p ∘ x') (! (!-inv-r p))

 move-right :  {A : Type} {M N P : A}
               (β : Path N P) (α : Path M N) (γ : Path M P)
            → Path (β ∘ α) γ
            → Path α (! β ∘ γ)
 move-right id id γ x = ! (∘-unit-l γ) ∘ x

 move-left-right :  {A : Type} {M N P : A}
               (α : Path M P) (β : Path N P) (γ : Path M N)
            → Path α (β ∘ γ) 
            → Path (α ∘ ! γ) β 
 move-left-right id β id x = x

 -- ENH: make β and γ implicit
 move-right-right-! :  {A : Type} {M N P : A}
                       (β : Path N P) (α : Path N M) (γ : Path M P)
                    → Path (β ∘ ! α) γ
                    → Path β (γ ∘ α)
 move-right-right-! id id γ x = x

 move-right-right-!≃ :  {A : Type} {M N P : A}
                       (β : Path N P) (α : Path N M) (γ : Path M P)
                    → Path (β ∘ ! α) γ
                    ≃ Path β (γ ∘ α)
 move-right-right-!≃ id id γ = id

 rassoc-1-3-1 : ∀ {A} {M1 M2 M3 M4 M5 M6 : A}
                  (a56 : Path M5 M6) (a45 : Path M4 M5) (a34 : Path M3 M4) (a23 : Path M2 M3) (a12 : Path M1 M2)
                → Path (a56 ∘ (a45 ∘ a34 ∘ a23) ∘ a12) (a56 ∘ a45 ∘ a34 ∘ a23 ∘ a12)
 rassoc-1-3-1 id id id id id = id

   
 transport-Path : {Γ A : Type} (f g : Γ → A) {M N : Γ} (p : Path M N)
                → (p' : _) → Path (transport (\ x → Path (f x) (g x)) p p')
                                    ((ap g p) ∘ p' ∘ (! (ap f p)))
 transport-Path _ _ id p' = ! (∘-unit-l p')

 transport-Path-right :  {A : Type} {M N P : A} 
   (α' : Path N P) (α : Path M N)
   → Path (transport (\ x → Path M x) α' α) (α' ∘ α)
 transport-Path-right id id = id 

 coe-inv-1 : {A B : Type} -> (α : Path A B) -> {M : _} -> coe (! α) (coe α M) ≃ M
 coe-inv-1 id = id

 coe-inv-2 : {A B : Type} -> (α : Path A B) -> {M : _} -> coe α (coe (! α) M) ≃ M
 coe-inv-2 id = id

 ap-o : {A B C : Type} (g : B → C) (f : A → B)
            {M N : A} (α : Path M N)
          → ap (\ x → g (f x)) α ≃ ap g (ap f α)
 ap-o g f id = id

 ap-id : {A : Type} {M N : A} (α : Path M N)
        → Path (ap (\ x → x) α) α
 ap-id id = id 
 
 ap-by-id : {A : Type} {f : A → A}
                (αf : (x : _) → x ≃ f x) 
             → {M N : A} (α : M ≃ N)
             → (ap f α ≃ αf N ∘ α ∘ ! (αf M))
 ap-by-id αf id = ap (λ x → αf _ ∘ x) (! (∘-unit-l (! (αf _)))) ∘ ! (!-inv-r (αf _)) 

 ap-! : {A B : Type} (F : A → B) {M N : A} (α : Path M N)
       → Path (ap F (! α)) (! (ap F α))
 ap-! _ id = id 


 -- ----------------------------------------------------------------------
 -- functions

 ap≃ : ∀ {A} {B : A → Type} {f g : (x : A) → B x} 
        → Path f g → {x : A} → Path (f x) (g x)
 ap≃ α {x} = ap (\ f → f x) α

 -- ----------------------------------------------------------------------
 -- products

 record Σe (A : Type) (B : A -> Type) : Type where
    constructor _,_
    field
      fst : A
      snd : B fst
 open Σe public

 Σ : {A : Type} -> (B : A -> Type) -> Type
 Σ {A} B = Σe A B

 infixr 0 _,_

 syntax Σe A (\ x  -> B) = Σ[ x ∶ A ] B


 -- ----------------------------------------------------------------------
 -- equivalences

 record IsEquiv {A B : Type} (f : A → B) : Type where
  constructor isequiv
  field
     g : B → A
     α : (x : A) → Path (g (f x)) x
     β : (y : B) → Path (f (g y)) y
     γ : (x : A) →  Path (β (f x)) (ap f (α x)) -- coherence condition necessary for higher spaces
     -- also satifies:
     -- (y : B) →  Path (α (g y)) (ap g (β y));
     -- this is just γ with f<→g and α<→β, so we'll prove this in
     -- the process of defining !-equiv below

 Equiv : Type -> Type -> Type
 Equiv A B = Σ (IsEquiv{A}{B})

 equiv : {A B : Type}
     (f : A → B)
     (g : B → A)
     (α : (x : A) → Path (g (f x)) x)
     (β : (y : B) → Path (f (g y)) y)
     (γ : (x : A) →  Path (β (f x)) (ap f (α x)))
   → Equiv A B
 equiv f g α β γ = f , isequiv g α β γ

 record IsHEquiv {A B : Type} (f : A → B) : Type where
   constructor ishequiv
   field
     g : B → A
     α : (x : A) → Path (g (f x)) x
     β : (y : B) → Path (f (g y)) y

 HEquiv : Type → Type → Type
 HEquiv A B = Σ (IsHEquiv{A}{B})

 hequiv : {A B : Type}
     (f : A → B)
     (g : B → A)
     (α : (x : A) → Path (g (f x)) x)
     (β : (y : B) → Path (f (g y)) y)
     → HEquiv A B
 hequiv f g α β = f , ishequiv g α β

 inverses-natural : ∀ {A B} (f : A → B) (g : B → A) (η : (x : A) → Path (g (f x)) x)
                      {x : A} 
                   → Path (η (g (f x))) (ap (g o f) (η x))
 inverses-natural f g η {x} = 
   (∘-unit-l _ ∘ ap (λ y → y ∘ ap (λ x' → g (f x')) (η x)) (!-inv-l (η x))) ∘ 
   ap (λ a → (! a ∘ η x) ∘ ap (g o f) (η x)) (ap-id (η x)) ∘
   move-right-right-! (η (g (f x))) (ap (λ x' → g (f x')) (η x)) _
     (move-right (ap (λ x' → x') (η x)) (η (g (f x)) ∘ ! (ap (λ x' → g (f x')) (η x))) _
       (apd η (η x) ∘ ! (transport-Path (g o f) (λ x' → x') (η x) (η (g (f x)))))) 

 improve : {A B : Type} → HEquiv A B → Equiv A B
 improve (f , ishequiv g η ξ) = 
   equiv f g 
         η 
         (λ x → ξ x ∘ ap f (η (g x)) ∘ ap (f o g) (! (ξ x)))
         coh where
   abstract -- we might someday need to know this, but for now it's slowing things down too much
            -- at call sites to normalize it
     coh : (x : _) -> ξ (f x) ∘ ap f (η (g (f x))) ∘ ap (f o g) (! (ξ (f x))) ≃ ap f (η x)
     coh =
         (λ x → ξ (f x) ∘ ap f (η (g (f x))) ∘ ap (f o g) (! (ξ (f x)))                           ≃〈 ap (λ a → ξ (f x) ∘ ap f a ∘ ap (f o g) (! (ξ (f x)))) (inverses-natural f g η) 〉 
                ξ (f x) ∘ ap f (ap (g o f) (η x)) ∘ ap (f o g) (! (ξ (f x)))                      ≃〈 ap (λ a → ξ (f x) ∘ a ∘ ap (f o g) (! (ξ (f x)))) (ap-o (f o g) f (η x) ∘ ! (ap-o f (g o f) (η x))) 〉 
                ξ (f x) ∘ ap (f o g) (ap f (η x)) ∘ ap (f o g) (! (ξ (f x)))                      ≃〈 ap (λ a → ξ (f x) ∘ a ∘ ap (f o g) (! (ξ (f x)))) (ap (λ a → ! (ξ (f x)) ∘ ap f (η x) ∘ a) (!-invol (ξ (f (g (f x))))) ∘ ap-by-id (λ x' → ! (ξ x')) (ap f (η x))) 〉 
                ξ (f x) ∘ (! (ξ (f x)) ∘ (ap f (η x)) ∘ ξ (f (g (f x)))) ∘ ap (f o g) (! (ξ (f x))) ≃〈 rassoc-1-3-1 (ξ (f x)) (! (ξ (f x))) (ap f (η x)) (ξ (f (g (f x)))) (ap (f o g) (! (ξ (f x)))) 〉 
                ξ (f x) ∘ ! (ξ (f x)) ∘ (ap f (η x)) ∘ ξ (f (g (f x))) ∘ ap (f o g) (! (ξ (f x)))   ≃〈 !-inv-r-front (ξ (f x)) (ap f (η x) ∘ ξ (f (g (f x))) ∘ ap (f o g) (! (ξ (f x)))) 〉 
                (ap f (η x)) ∘ ξ (f (g (f x))) ∘ ap (f o g) (! (ξ (f x)))                          ≃〈 ap (λ a → ap f (η x) ∘ a ∘ ap (f o g) (! (ξ (f x)))) (inverses-natural g f ξ) 〉 
                (ap f (η x)) ∘ ap (f o g) (ξ ((f x))) ∘ ap (f o g) (! (ξ (f x)))                  ≃〈 ap (λ a → ap f (η x) ∘ ap (f o g) (ξ (f x)) ∘ a) (ap-! (f o g) (ξ (f x))) 〉 
                (ap f (η x)) ∘ ap (f o g) (ξ ((f x))) ∘ ! (ap (f o g) (ξ (f x)))                  ≃〈 ap (λ a → ap f (η x) ∘ a) (!-inv-r (ap (f o g) (ξ (f x)))) 〉 
                (ap f (η x) ∎)) 


 -- ----------------------------------------------------------------------
 -- univalence

 -- eta-expanded version; makes the later definitions easier
 -- and is maybe better for the computational interp,
 -- at least if it's based on groupoids.
 -- is the conceptual order backwards here? should J come from these, rather than the other way around?
 coe-is-equiv : ∀ {A B} (p : Path A B) → IsEquiv (coe p)
 coe-is-equiv {A}{B} p = isequiv (coe (! p)) (λ _ → coe-inv-1 p) (λ _ → coe-inv-2 p) (triangle p) where
   triangle : ∀ {B} (p : Path A B) → (x : A) → Path (coe-inv-2 p) (ap (transport (λ x' → x') p) (coe-inv-1 p))
   triangle id = λ _ → id

 coe-equiv : ∀ {A B} (p : Path A B) → Equiv A B
 coe-equiv p = (coe p , coe-is-equiv p)

 postulate {- HoTT Axiom -} 
   -- using pathToEquiv' instead of pathToEquiv (see Universe.agda)
   univalence : ∀ {A B} -> IsEquiv {Path A B} {Equiv A B} coe-equiv
 
 -- ua is the intro form; coe is the elim

 ua : ∀ {A B} -> Equiv A B -> Path A B
 ua = IsEquiv.g univalence

 univalence≃ : ∀ {A B} → Path A B ≃ Equiv A B
 univalence≃ = ua (coe-equiv , univalence)

 type≃β : {A B : Type} (e : Equiv A B) -> Path (coe (ua e)) (fst e)
 type≃β e = ap fst (IsEquiv.β univalence e)

 type≃β! : {A B : Type} (a : Equiv A B) -> coe (! (ua a)) ≃ IsEquiv.g (snd a)
 type≃β! a = ap (λ x → IsEquiv.g (snd x)) (IsEquiv.β univalence a)

 type≃η : ∀ {A B} (p : Path A B) → ua (coe-equiv p) ≃ p
 type≃η p = IsEquiv.α univalence p

 type≃-coh : ∀ {A B} (p : Path A B) -> ap coe (type≃η p) ≃ type≃β (coe-equiv p)
 type≃-coh p = ap (ap fst) (! (IsEquiv.γ univalence p)) ∘ ap-o fst coe-equiv (IsEquiv.α univalence p) 


 -- ----------------------------------------------------------------------
 -- truncation levels

 data TLevel : Type where
   -2 : TLevel 
   S : TLevel -> TLevel

 -1 : TLevel
 -1 = S -2

 Contractible : Type -> Type
 Contractible A = Σ \(c : A) → (y : A) → Path c y

 -- want some control over unfolding
 mutual
   data NType (n : TLevel) (A : Type) : Type where
     ntype  : NType' n A -> NType n A
 
   NType' : TLevel -> Type -> Type 
   NType' -2 A = Contractible A
   NType' (S n) A = (x y : A) → NType n (Path x y)

 use-level : ∀ {n A} → NType n A -> NType' n A
 use-level (ntype p) = p

 HProp : Type -> Type
 HProp A = NType -1 A

 HSet : Type -> Type
 HSet A = NType (S (S -2)) A

 HGpd : Type -> Type
 HGpd A = NType (S (S (S -2))) A

 HProp-unique : ∀ {A} -> HProp A -> (x y : A) -> x ≃ y
 HProp-unique h x y = fst (use-level (use-level h x y))

 HSet-UIP : ∀ {A} -> HSet A -> (x y : A) (p q : x ≃ y) -> p ≃ q
 HSet-UIP h x y p q = fst (use-level (use-level (use-level h x y) p q))

 1Type-unique : ∀ {A} (nA : NType (S (S (S -2))) A)
               -> { x y : A} {p q : x ≃ y} {r s : p ≃ q} -> r ≃ s
 1Type-unique nA = HSet-UIP (use-level {(S (S (S -2)))} nA _ _) _ _ _ _


 abstract 
   unique-HProp : ∀ {A} -> ((x y : A) -> x ≃ y) -> HProp A
   unique-HProp f = ntype (λ x y → ntype (f x y , contra)) where
     contra : ∀ {x y} → (α : Path x y) → Path (f x y) α
     contra {x} id = square-id (f x x) (! lemma) where 
        lemma : f x x ≃ (f x x ∘ (f x x))
        lemma = 
                f x x ≃〈 ! (apd (f x) (f x x)) 〉 
                transport (λ z → Id x z) (f x x) (f x x) ≃〈 transport-Path-right (f x x) (f x x) 〉 
                (f x x ∘ (f x x)) ∎
  
   UIP-HSet : ∀ {A} -> ((x y : A) (p q : x ≃ y) -> p ≃ q) → HSet A 
   UIP-HSet u = ntype (λ x y → unique-HProp (u _ _))

   -- weakening
   -- in fact, it decrements, but often you want this lemma
   Contractible-Path : ∀ {A} -> Contractible A → (x y : A) -> Contractible (Path x y)
   Contractible-Path (acenter , apaths) x y = 
     (apaths y ∘ ! (apaths x)) , (λ α → move-left-right (apaths y) α (apaths x) (! (apd apaths α ∘ ! (transport-Path-right α (apaths x)))))
  
   path-preserves-level : {n : TLevel} {A : Type} -> NType n A -> {x y : A} -> NType n (Path x y)
   path-preserves-level { -2 } {A} tA {x} {y} = ntype (Contractible-Path (use-level tA) x y)
   path-preserves-level { S n } {A} tA {x} {y} = ntype (λ p q → path-preserves-level (use-level tA x y))
  
   increment-level : {n : TLevel} {A : Type} -> (NType n A) → (NType (S n) A)
   increment-level {n}{A} tA = ntype (λ x y → path-preserves-level tA)

   -- useful for ap because (BackPath _) will get inferred when (\x -> Path x _) won't
   BackPath : {A : Type} (M N : A) → Type
   BackPath M N = Path N M
  
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

 path-induction-l : {A : Type} {M : A}
                  (C : (x : A) → Path x M → Type)
               → (C M id)
               → {N : A} → (P : Path N M)
               → C N P
 path-induction-l _ b id = b

 -- laws (see First.agda also)
 
 !-∘ : {A : Type} {M N P : A} → (q : Path N P) → (p : Path M N)
     → (! (q ∘ p)) ≃ ! p ∘ ! q
 !-∘ id id = id

 -- ENH: make α β γ implicit
 move-left :  {A : Type} {M N P : A}
               (α : Path M P) (β : Path N P) (γ : Path M N)
            → Path α (β ∘ γ)
            → Path (! β ∘ α) γ
 move-left id id γ x = ∘-unit-l γ ∘ x
 
 move-left-! :  {A : Type} {M N P : A}
               (α : Path M N) (β : Path N P) (γ : Path M P)
            → Path α (! β ∘ γ)
            → Path (β ∘ α) γ
 move-left-! id id γ x = ∘-unit-l γ ∘ x

 move-left-right-! :  {A : Type} {M N P : A}
               (α : Path M P) (β : Path N P) (γ : Path N M)
            → Path α (β ∘ ! γ) 
            → Path (α ∘ γ) β 
 move-left-right-! id β id x = x
 
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
 
 assoc-131->212 : ∀ {A} {M1 M2 M3 M4 M5 M6 : A}
                (a56 : Path M5 M6) (a45 : Path M4 M5) (a34 : Path M3 M4) (a23 : Path M2 M3) (a12 : Path M1 M2)
              → Path (a56 ∘ (a45 ∘ a34 ∘ a23) ∘ a12) ((a56 ∘ a45) ∘ a34 ∘ (a23 ∘ a12))
 assoc-131->212 id id id id id = id

 !-∘3 : ∀ {A} {M1 M2 M3 M4 : A} (a34 : Path M3 M4) (a23 : Path M2 M3) (a12 : Path M1 M2)
     → ! (a34 ∘ a23 ∘ a12) ≃ (! a12 ∘ ! a23 ∘ ! a34)
 !-∘3 id id id = id

 !-inv-with-middle-r : ∀ {A} {a b : A} (α : Path a b) {β : Path a a} → (β ≃ id) → (α ∘ β ∘ ! α) ≃ id
 !-inv-with-middle-r id δ = δ ∘ (∘-unit-l _)

 !-inv-with-middle-l : ∀ {A} {a b : A} (α : Path b a) {β : Path a a} → (β ≃ id) → (! α ∘ β ∘ α) ≃ id
 !-inv-with-middle-l id δ = δ ∘ (∘-unit-l _)

 cancels-is-inverse : ∀ {A} {M N : A} {p : Path M N} {q : Path N M}
                    -> Path (q ∘ p) id
                    -> Path q (! p)
 cancels-is-inverse {_}{_}{_}{p}{q} α = ∘-unit-l (! p) ∘ move-right-right q p id α

 cancels-is-inverse≃ : ∀ {A} {M N : A} {p : Path M N} {q : Path N M}
                    -> Path (q ∘ p) id
                    ≃ Path q (! p)
 cancels-is-inverse≃ {p = id}{q} = id

 cancels-inverse-is≃ : ∀ {A} {M N : A} (q : Path N M) (p : Path N M)
                    -> Path (q ∘ ! p) id
                     ≃ Path q p
 cancels-inverse-is≃ q id = id

 move-transport-right-!≃ : ∀ {A : Type} {M M' : A} (B : A → Type)
                          (α : M' ≃ M) {b : B M} {b' : B M'}
                       -> (transport B (! α) b ≃ b')
                        ≃ (b ≃ transport B α b')
 move-transport-right-!≃ B id = id

 move-transport-right≃ : ∀ {A : Type} {M M' : A} (B : A → Type)
                          (α : M ≃ M') {b : B M} {b' : B M'}
                       -> (transport B α b ≃ b')
                        ≃ (b ≃ transport B (! α) b')
 move-transport-right≃ B id = id

 move-transport-left-!≃ : ∀ {A : Type} {M M' : A} (B : A → Type)
                          (α : M ≃ M') {b : B M} {b' : B M'}
                       -> (b ≃ transport B (! α) b')
                        ≃ (transport B α b ≃ b')
 move-transport-left-!≃ B id = id

 move-posto-with-transport-left : ∀ {A D : Type} (C : A → Type) {M M' : A}
                          (α : M ≃ M') 
                          (f : C M → D) (g : C M' → D)
                       -> f ≃ (g o transport C α)
                       -> (f o transport C (! α)) ≃ g
 move-posto-with-transport-left C id f g = λ x → x

 cancel-left≃ : ∀ {A} {m1 m2 : A}
              (q : m1 ≃ m2) 
              (p : m1 ≃ m1)
              -> ((q ∘ p) ≃ q) ≃ (p ≃ id)
 cancel-left≃ id p = ap (λ x → Id x id) (∘-unit-l p)

 flip≃ : ∀ {A} {m1 m2 : A} 
             -> (m1 ≃ m2) ≃ (m2 ≃ m1)
 flip≃ = ua (improve (hequiv ! ! !-invol !-invol))

 move-!≃' : ∀ {A} {m1 m1' m2 m2' : A}
                (q : m1 ≃ m2) 
                (a1 : m1 ≃ m1')
                (a2 : m2 ≃ m2')
                (p : m2' ≃ m1')
              -> (! q ≃ (! a1 ∘ p ∘ a2)) ≃ (a2 ∘ q ∘ ! a1 ≃ ! p)
 move-!≃' id id a2 id = ap (λ x → Id x id) (∘-unit-l a2 ∘ ap (λ x → id ∘ x) (∘-unit-l a2)) ∘ flip≃

 move-!≃ : ∀ {A} {m1 m2 : A}
                (q : m1 ≃ m2) 
                (p : m2 ≃ m1)
              -> (! q ≃ p) ≃ (q ≃ ! p)
 move-!≃ id p = move-!≃' id id id p ∘ ap (λ x → Id id x) (! (∘-unit-l p))

 rotate3≃ : ∀ {A} {x y z t : A} (b : y ≃ z) (f : x ≃ y) (c : x ≃ t) (g : t ≃ z) 
          → (b ∘ f ∘ (! c) ≃ g) ≃ (g ∘ c ∘ ! f ≃ b)
 rotate3≃ id id id g = flip≃

 rotate3≃-2 : ∀ {A} {w z : A} (a : z ≃ z) (b : w ≃ z) (c : w ≃ w)
            -> (a ∘ b ∘ ! c ≃ b) ≃ (a ≃ b ∘ c ∘ ! b)
 rotate3≃-2 a b c = flip≃ ∘ rotate3≃ a b c b 

 flip-triangle≃ : ∀ {A} {x y z : A} (p : Path x y) (q : Path z y) (r : Path x z)
                -> (p ∘ ! r ≃ q) ≃ (! q ∘ p ≃ r)
 flip-triangle≃ p id id = ap (λ x → Path x id) (! (∘-unit-l p))

 pre∘-equiv : ∀ {A} {a b c : A} → (a ≃ b) -> Equiv (b ≃ c) (a ≃ c)
 pre∘-equiv α = (improve (hequiv (λ β → β ∘ α) (λ β' → β' ∘ ! α) (λ β → !-inv-r-back β α ∘ ! (∘-assoc β α (! α))) (λ β → !-inv-l-back β α ∘ ! (∘-assoc β (! α) α))))

 -- transport stuff


 transport-∘ : {A : Type} (C : A → Type) {M N P : A} (β : Path N P) (α : Path M N)
           → Path (transport C (β ∘ α)) (\ x → transport C β (transport C α x))
 transport-∘ _ id id = id

 transport-∘3 : {A : Type} (C : A → Type) {M N P Q : A} (γ : Path P Q) (β : Path N P) (α : Path M N)
              → Path (transport C (γ ∘ β ∘ α)) (transport C γ o transport C β o transport C α)
 transport-∘3 _ id id id = id
 
 transport-ap-assoc : {A : Type} (C : A → Type) {M N : A} (α : Path M N) → Path (transport C α) (transport (\ x → x) (ap C α))
 transport-ap-assoc C id = id 
 
 transport-ap-assoc' : {A B : Type} (C : B → Type) (f : A → B) {M N : A} (α : Path M N) 
                     → Path (transport (\ x -> C (f x)) α) (transport C (ap f α))
 transport-ap-assoc' C f id = id 

 transport-inv-1 : {A : Type} (B : A -> Type) {M N : A} (α : M ≃ N) -> (\y -> transport B (! α) (transport B α y)) ≃ (\ x -> x)
 transport-inv-1 _ id = id

 transport-inv-2 : {A : Type} (B : A -> Type) {M N : A} (α : M ≃ N) -> (\y -> transport B α (transport B (! α) y)) ≃ (\ x -> x)
 transport-inv-2 _ id = id

 transport-inv-2' : {A : Type} (B : A -> Type) {M N : A} (α : M ≃ N) -> {y : _} -> transport B α (transport B (! α) y) ≃ y
 transport-inv-2' B α = coe (! (move-transport-right≃ B α)) id

 transport-isequiv : ∀ {A : Type} {M N : A} (B : A → Type) (α : M ≃ N) 
                  -> IsEquiv (transport B α)
 transport-isequiv {A}{M} B α = isequiv (transport B (! α)) (λ x → ap≃ (transport-inv-1 B α)) (λ x → ap≃ (transport-inv-2 B α)) 
                                  (coh α) where
                    coh : {N : _} (α : Path M N) 
                        → (x : B M) → Path (ap≃ (transport-inv-2 B α)) (ap (transport B α) (ap≃ (transport-inv-1 B α) {x}))
                    coh id = λ _ → id

 ap-o3 : {A B C D : Type} (h : C → D) (g : B → C) (f : A → B)
            {M N : A} (α : Path M N)
          → ap (h o g o f) α ≃ (ap h (ap g (ap f α)))
 ap-o3 _ _ _ id = id

 ap-o4 : {A B C D E : Type} (i : D -> E) (h : C → D) (g : B → C) (f : A → B)
            {M N : A} (α : Path M N)
          → ap (i o h o g o f) α ≃ ap i (ap h (ap g (ap f α)))
 ap-o4 _ _ _ _ id = id
 
 ap-∘ : {A B : Type} (F : A → B) {M N P : A} (β : Path N P) (α : Path M N)
      → Path (ap F (β ∘ α)) (ap F β ∘ ap F α)
 ap-∘ _ _ id = id

 ap-∘3 : {A B : Type} (F : A → B) {M N P Q : A} (γ : Path P Q) (β : Path N P) (α : Path M N)
      → Path (ap F (γ ∘ β ∘ α)) (ap F γ ∘ ap F β ∘ ap F α)
 ap-∘3 _ _ id id = id
 
 apd-∘ : {A : Type} {B : A -> Type} (F : (x : A) -> B x) {M N P : A} (β : Path N P) (α : Path M N)
         -> Path (apd F (β ∘ α)) (apd F β ∘ ap (λ x → transport B β x) (apd F α) ∘ ap (λ f → f (F M)) (transport-∘ B β α))
 apd-∘ _ id id = id

 -- FIXME: relation to ap≃2 ?
 ap-by-equals : {A B : Type} {f g : A → B}
                (α : (x : _) → f x ≃ g x) 
              → {M N : A} (β : M ≃ N)
              → (ap f β ≃ ! (α N) ∘ ap g β ∘ (α M))
 ap-by-equals α id = ! (!-inv-l (α _) ∘ ap (λ x → ! (α _) ∘ x) (∘-unit-l (α _)))

 transport-by-equals≃ : ∀ {A : Type} {a1 a2 : A} (α : a1 ≃ a2) {B B' : A → Type} (b1 : B a1) (b2 : B a2)
                        -> (β : B ≃ B')
                        -> (transport B α b1 ≃ b2) ≃ (transport B' α (coe (ap≃ β) b1) ≃ coe (ap≃ β) b2)
 transport-by-equals≃ _ _ _ id  = id

 ap-constant : {A C : Type} {M N : A} (v : C) -> (p : Path M N) -> Path (ap (\ _ -> v) p) id
 ap-constant v id = id 

 transport-constant : {A C : Type} {M N : A} -> (p : Path M N) -> Path (transport (\ _ -> C) p) (\ x -> x)
 transport-constant id = id 

 transport-Path-d : {Γ : Type} {A : Γ -> Type} (f g : (x : Γ) -> A x) {M N : Γ} (p : Path M N)
            -> (p' : f M ≃ g M) 
            -> Path (transport (\ x -> Path (f x) (g x)) p p')
                    (apd g p ∘ ap (transport A p) p' ∘ ! (apd f p))
 transport-Path-d _ _ id p' = ! (∘-unit-l p' ∘ ap (λ x → id ∘ x) (ap-id p'))

 transport-Path-pre : {A : Type} {M N P : A} (p' : Path N M) (p : Path N P)
               -> Path (transport (\ x -> Path x P) p' p) (p ∘ ! p')
 transport-Path-pre id id = id 

 transport-Path-pre' : {Γ A : Type} {g : A} (f : Γ → A) {M N : Γ} (p : Path M N)
                → (p' : _) → Path (transport (\ x → Path (f x) g) p p')
                                    (p' ∘ (! (ap f p)))
 transport-Path-pre' _ id p' = id

 transport-Path-post' : {Γ A : Type} {f : A} (g : Γ → A) {M N : Γ} (p : Path M N)
                → (p' : _) → Path (transport (\ x → Path f (g x)) p p')
                                   (ap g p ∘ p')
 transport-Path-post' _ id p' = ! (∘-unit-l p')

 transport-Path-right-∘ : ∀ {A} {a b c : A} (β : b ≃ c) (α : a ≃ b)
                           → transport-Path-right (β ∘ α) id ≃ 
                             ap (λ x → β ∘ x) (transport-Path-right α id) ∘
                             (transport-Path-right β (transport (Path a) α id) ∘
                              ap≃ (transport-∘ (Path a) β α))
 transport-Path-right-∘ id id = id

 apPath≃ : ∀ {A B} {x1 x2 : A} {y1 y2 : B} 
            -> (α : Path A B) -> Path (coe α x1) y1 -> Path (coe α x2) y2
            -> Path {A} x1 x2 ≃ Path {B} y1 y2
 apPath≃ id id id = id

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

 ap2-same-is-ap : ∀ {A C} {M N : A} (f : A -> A -> C) 
                  (α : Path M N) -> ap2 f α α ≃ ap (\ x -> f x x) α
 ap2-same-is-ap f id = id

 ap2-ap-assoc : ∀ {A B C D} {a b : A} (f : B → C → D) (g1 : A → B) (g2 : A → C) (α : a ≃ b) → ap (λ a → f (g1 a) (g2 a)) α ≃ ap2 f (ap g1 α) (ap g2 α)
 ap2-ap-assoc f g1 g2 id = id

 ap2-ap-assoc-1 : {A A' B  C : Type} (f : A → B → C) 
                  (g : A' → A) {M1 M2 : A'} (α : M1 ≃ M2) {N1 N2 : B} (β : N1 ≃ N2)
                → ap2 f (ap g α) β ≃ ap2 (λ x y → f (g x) y) α β
 ap2-ap-assoc-1 f g id id = id

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

 record Unit : Type where
   constructor <> 
 
 -- sometimes handy not to have definitional η
 data Unit⁺ : Type where
   <>⁺ : Unit⁺
 
 split1⁺ : (C : Unit⁺ → Type) → C <>⁺ → (x : Unit⁺) → C x
 split1⁺ C b <>⁺ = b
 
 -- gadget for defeating unused argument check in Agda 2.3.2.1 and later
 -- a version of Unit⁺ that's indexed by an arbitrary thing.  
 record Phantom {A : Type}(a : A) : Type where
   constructor phantom
   field 
     match : Unit⁺
 
 _×_ : Type -> Type -> Type
 a × b = Σ (\ (_ : a) -> b)
 
 infixr 10 _×_
 
 fst≃ : {A : Type} {B : A -> Type} {p q : Σ[ x ∶ A ] B x} -> p ≃ q -> (fst p) ≃ (fst q)
 fst≃ = ap fst
 
 snd≃ : {A : Type} {B : A -> Type} {p q : Σ B} -> (c : p ≃ q) -> (transport B (fst≃ c) (snd p)) ≃ (snd q)
 snd≃ {p = p} {q = .p} id = id
 
 snd≃' : {A : Type} {B : A -> Type} {p q : Σ B} -> (c : p ≃ q) -> (transport (B o fst) c (snd p)) ≃ (snd q)
 snd≃' α = apd snd α
 
 pair≃ : {A : Type} {B : A -> Type} {p q : Σ B} -> (α : (fst p) ≃ (fst q)) -> (transport B α (snd p)) ≃ (snd q) -> p ≃ q
 pair≃ {p = x , y} {q = .x , .y} id id = id
 
 Σ≃η : {A : Type} {B : A -> Type} {p q : Σ B} -> (α : p ≃ q) -> (pair≃ (fst≃ α) (snd≃ α)) ≃ α
 Σ≃η {p = p} {q = .p} id = id
 
 Σ≃β1 : {A : Type} {B : A -> Type} {p q : Σ B} 
      (α : Path (fst p) (fst q)) 
      (β : Path (transport B α (snd p)) (snd q))
      -> Path (fst≃{B = B} (pair≃ α β)) α
 Σ≃β1 {p = x , y} {q = .x , .y} id id = id
 
 Σ≃β2 : {A : Type} {B : A -> Type} {p q : Σ B} 
        (α : (fst p) ≃ (fst q))
        (β : (transport B α (snd p)) ≃ (snd q))
     -> (snd≃{B = B} (pair≃ α β)) ≃ 
        (β ∘ (ap (λ x → transport B x (snd p)) (Σ≃β1 {B = B} α β)))
 Σ≃β2 {p = x , y} {q = .x , .y} id id = id
 
 {-
 -- adjust on the other side
 Σ≃β2' : {A : Type} {B : A -> Type} {p q : Σ B} 
        (α : (fst p) ≃ (fst q))
        (β : (transport B α (snd p)) ≃ (snd q))
     -> {! (snd≃' {B = B} (pair≃ α β))  !} ≃ 
        β 
 Σ≃β2' {p = x , y} {q = .x , .y} id id = id
 -}
 
 -- subst extension for Γ,x:A⁻ in DTT
 pair≃⁻ : {A : Set} {B : A -> Set} {p q : Σ B} 
       -> (α : (fst p) ≃ (fst q)) -> (snd p) ≃ transport B (! α) (snd q) 
       -> p ≃ q
 pair≃⁻ {A}{B}{p}{q} α β = pair≃ α ((transport-inv-2' B α) ∘ ap (transport B α) β)
 
 snd≃⁻ : {A : Type} {B : A -> Type} {p q : Σ B} -> (c : p ≃ q) -> (snd p) ≃ transport B (! (fst≃ c)) (snd q)
 snd≃⁻ {p = p} {q = .p} id = id
 
 ∘-Σ : ∀ {A} {B : A → Type} {p q r : Σ B}
      → (α1 : fst p ≃ fst q) (α2 : fst q ≃ fst r)
      → (β1 : transport B α1 (snd p) ≃ (snd q)) (β2 : transport B α2 (snd q) ≃ (snd r))
      → (pair≃{B = B} α2 β2) ∘ (pair≃ α1 β1) ≃ pair≃ (α2 ∘ α1) (β2 ∘ ap (transport B α2) β1 ∘ ap≃ (transport-∘ B α2 α1))
 ∘-Σ {p = (p1 , p2)} {q = (.p1 , .p2)} {r = (.p1 , .p2)} id id id id = id
 
 module ΣPath where
 
   eqv : {A : Type} {B : A → Type} {p q : Σ B}
       → Equiv (Σ \ (α : Path (fst p) (fst q)) → Path (transport B α (snd p)) (snd q))
               (Path p q)
   eqv {B = B} {p = p} {q = q} = 
     improve (hequiv 
       (λ p → pair≃ (fst p) (snd p))
       (λ p → fst≃ p , snd≃ p)
       (λ p' → pair≃ (Σ≃β1 (fst p') (snd p')) 
                     (move-left-right (snd≃ (pair≃{B = B} (fst p') (snd p'))) (snd p')
                        (ap (λ v → transport B v (snd p)) (Σ≃β1 (fst p') (snd p')))
                        (Σ≃β2 {B = B} (fst p') (snd p')) ∘
                      transport-Path-pre' (λ v → transport B v (snd p))
                                          (Σ≃β1 (fst p') (snd p'))
                                          (snd≃ (pair≃{B = B} (fst p') (snd p'))))) 
       (λ p → Σ≃η p))
 
   path : {A : Type} {B : A → Type} {p q : Σ B}
       →   (Σ \ (α : Path (fst p) (fst q)) → Path (transport B α (snd p)) (snd q))
         ≃ (Path p q)
   path = ua eqv 
 
 
 -- tlevel stuff
 
 Σ-with-Contractible : {A : Type} {B : A → Type}
                       → ( (x : A) → Contractible (B x))
                       -> A ≃ Σ B
 Σ-with-Contractible c = 
    ua (improve (hequiv (λ a → a , fst (c a))
                        fst
                        (λ _ → id)
                        (λ p → pair≃ id (HProp-unique (increment-level (ntype (c (fst p)))) _ _)))) 
 
 Σ-with-Contractibleβ1 : {A : Type} {B : A → Type}
                       → (c : (x : A) → Contractible (B x))
                       → (coe (Σ-with-Contractible c)) ≃ (\a -> a , fst (c a))
 Σ-with-Contractibleβ1 c = type≃β _
 
 ΣSubsetPath : {A : Type} {B : A → Type} {p q : Σ B} 
               → ( (x : A) → HProp (B x))
               →   (Path (fst p) (fst q))
                 ≃ (Path p q)
 ΣSubsetPath {p = p}{q = q} hp = ΣPath.path ∘ Σ-with-Contractible (λ p' → use-level{n = -2} (use-level{n = S -2} (hp (fst q)) _ _))
 
 ΣSubsetPathβ : {A : Type} {B : A → Type} {p q : Σ B} 
              → (hp : (x : A) → HProp (B x)) (p1 : Path (fst p) (fst q))
              → fst≃ (coe (ΣSubsetPath {p = p} {q = q} hp) p1) ≃ p1
 ΣSubsetPathβ {p = (x , _)}  {q = (.x , _)} hp id = 
   ((Σ≃β1 _ _ ∘ ap fst≃ (ap≃ (type≃β ΣPath.eqv))) ∘ 
    ap (fst≃ o coe ΣPath.path) (ap≃ (Σ-with-Contractibleβ1 (λ p' → use-level {n = -2} (use-level {n = S -2} (hp x) _ _))))) ∘
    ap fst≃ (ap≃ (transport-∘ (λ x' → x') ΣPath.path (Σ-with-Contractible (λ p' → use-level {n = -2} (use-level {n = S -2} (hp x) _ _)))))
 
 postulate
   ΣSubsetPathβ! : {A : Type} {B : A → Type} {p q : Σ B} 
                 → (hp : (x : A) → HProp (B x)) (p' : Path{Σ B} p q)
                 → (coe (! (ΣSubsetPath {p = p} {q = q} hp)) p') ≃ fst≃ p'
 
 
 
 module Σassoc where
 
   rassoc : {X : Type} 
            -> {A : X -> Type}
            -> {B : (Σ[ x ∶ X ] (A x)) -> Type}
            -> (Σ[ p ∶ (Σ[ x ∶ X ] (A x)) ] (B p))
            -> Σ[ x  ∶ X ] (Σ[ l1 ∶ A x ] (B (x , l1)))
   rassoc ((fst , snd) , snd') = fst , (snd , snd')
 
   lassoc : {X : Type}
            -> {A : X -> Type}
            -> {B : (Σ[ x ∶ X ] (A x)) -> Type}
            -> Σ[ x ∶ X ] (Σ[ l1 ∶ A x ] (B (x , l1)))
            -> (Σ[ p ∶ (Σ[ x ∶ X ] (A x)) ] (B p))
   lassoc (fst , fst' , snd) = (fst , fst') , snd
 
   eqv : {X : Type}
        -> {A : X -> Type}
        -> {B : (Σ[ x ∶ X ] (A x)) -> Type}
        -> Equiv (Σ[ p ∶ (Σ[ x ∶ X ] (A x)) ] (B p))
                 (Σ[ x  ∶ X ] (Σ[ l1 ∶ A x ] (B (x , l1))))
   eqv = improve (hequiv  rassoc lassoc (λ y → id) (λ x → id))
 
   path : {X : Type}
        -> {A : X -> Type}
        -> {B : (Σ[ x ∶ X ] (A x)) -> Type}
        ->   (Σ[ p ∶ (Σ[ x ∶ X ] (A x)) ] (B p))
           ≃ (Σ[ x  ∶ X ] (Σ[ l1 ∶ A x ] (B (x , l1))))
   path = ua eqv
 
 
 Σlevel : ∀ {n} {A : Type} {B : A → Type}
          → NType n A
          → ((x : A) → NType n (B x))
          → NType n (Σ B)
 Σlevel {n = -2} tA tB = transport (NType -2) (Σ-with-Contractible (λ x → use-level (tB x))) tA
 Σlevel {n = S n} tA tB = ntype (λ x y → transport (NType n) ΣPath.path (Σlevel {n = n} (use-level tA _ _) (λ x → use-level (tB (fst y)) _ _)))
 
 
 -- transport and ap
 
 transport-Σ : {Γ : Type} {θ1 θ2 : Γ} (δ : θ1 ≃ θ2)
           (A : Γ -> Type) (B : (γ : Γ) -> A γ -> Type)
           (p : Σ \(x : A θ1) -> B θ1 x)
         -> transport (\ γ -> Σ (B γ)) δ p 
          ≃ (transport A δ (fst p) , 
             transport (λ (γ' : Σ A) → B (fst γ') (snd γ')) 
                   (pair≃ δ id) 
                   (snd p))
 transport-Σ id A B p = id
 
 transport-com-for-ap-pair :
   {Γ : Type} {θ1 θ2 : Γ} (δ : θ1 ≃ θ2)
   (A : Γ -> Type) (B : (γ : Γ) -> A γ -> Type)
   (p1 : (γ : Γ) -> A γ)
   (p2 : (γ : Γ) -> B γ (p1 γ))
  -> (transport (B θ2) (apd p1 δ)
            (transport (λ γ' → B (fst γ') (snd γ'))
                   (pair≃ {Γ}{A} δ id)
                   (p2 θ1)))
     ≃ 
     (transport (λ z → B z (p1 z)) δ (p2 θ1))
 transport-com-for-ap-pair id _ _ _ _ = id
 
 ap-pair : {Γ : Type} {θ1 θ2 : Γ} {δ : θ1 ≃ θ2}
             {A : Γ -> Type} {B : (γ : Γ) -> A γ -> Type} 
             {p1 : (γ : Γ) -> A γ} 
             {p2 : (γ : Γ) -> B γ (p1 γ)} 
          -> (apd (\ γ -> (_,_ {A γ} {B γ} (p1 γ) (p2 γ))) δ)
           ≃ pair≃ (apd p1 δ) (apd p2 δ ∘ (transport-com-for-ap-pair δ A B p1 p2))
             ∘ transport-Σ δ A B (p1 θ1 , p2 θ1)
 ap-pair {δ = id} = id
 
 ap-fst : {Γ : Type} {θ1 θ2 : Γ} {δ : θ1 ≃ θ2}
            {A : Γ -> Type} {B : (γ : Γ) -> A γ -> Type} 
            {p : (γ : Γ) -> Σ (B γ)} 
          -> apd (\ γ -> fst (p γ)) δ
           ≃ fst≃ ((apd p δ) ∘ ! (transport-Σ δ A B (p θ1)))
 ap-fst {δ = id} = id
 
 transport-com-for-ap-snd : 
            {Γ : Type} {θ1 θ2 : Γ} (δ : θ1 ≃ θ2)
            (A : Γ -> Type) (B : (γ : Γ) -> A γ -> Type)
            (p : (γ : Γ) -> Σ (B γ))
      -> Path (transport (λ z → B z (fst (p z))) δ (snd (p θ1)))
            (transport (B θ2) (fst≃ (apd p δ))
                   (snd (transport (λ z → Σe (A z) (B z)) δ (p θ1))))
 transport-com-for-ap-snd id _ _ _ = id
 
 ap-snd : {Γ : Type} {θ1 θ2 : Γ} {δ : θ1 ≃ θ2}
            {A : Γ -> Type} {B : (γ : Γ) -> A γ -> Type} 
            {p : (γ : Γ) -> Σ (B γ)} 
          -> apd (\ γ -> snd (p γ)) δ
           ≃ snd≃ (apd p δ) ∘ transport-com-for-ap-snd δ A B p
 ap-snd {δ = id} = id
 
 -- might want to know what coercing by this does... 
 apΣ : {A A' : Type} {B : A → Type} {B' : A' → Type}
       (a : A ≃ A')
       (b : (\ (x : A) → B x) ≃ (\ (x : A) → B' (coe a x)))
     → Σ B ≃ Σ B'
 apΣ id id = id
 
 apΣ-l : {A A' : Type} {B : A → Type} {B' : A' → Type}
       (a : A ≃ A')
       (b : (\ (x : A') → B (coe (! a) x)) ≃ B')
     → Σ B ≃ Σ B'
 apΣ-l id id = id
 
 -- non-dependent pairs
   
 transport-× : {Γ : Type} {θ1 θ2 : Γ} (δ : θ1 ≃ θ2)
         (A : Γ -> Type) (B : (γ : Γ) -> Type)
       -> transport (\ γ -> A γ × B γ) δ 
        ≃ (\ p -> (transport A δ (fst p) , transport B δ (snd p)))
 transport-× id A B = id
 
 transport-×2 : ∀ {A B} {M N : A} (C : A -> Type) (α : M ≃  N)
                → transport (\ a -> B × (C a)) α
                ≃ λ {(b , c) -> (b , (transport C α c))}
 transport-×2 C id = id
 
 transport-×1 : ∀ {A C} {M N : A} (B : A -> Type) (α : M ≃  N)
                → transport (\ a -> (B a) × C) α
                ≃ λ {(b , c) -> (transport B α b , c)}
 transport-×1 C id = id
 
 snd×≃ : {A B : Type} {p q : A × B} -> p ≃ q -> (snd p) ≃ (snd q)
 snd×≃ {p = p} {q = .p} id = id    
 
 pair×≃ : {A B : Type} {p q : A × B} -> (fst p) ≃ (fst q) -> (snd p) ≃ (snd q) -> p ≃ q
 pair×≃ a b = ap2 _,_ a b
 
 ×≃η : {A B : Type} {p q : A × B} -> (α : p ≃ q) -> (pair×≃ (fst≃ α) (snd×≃ α)) ≃ α
 ×≃η {p = p} {q = .p} id = id
 
 ×≃β1 : {A B : Type} {p q : A × B} 
       (α : Path (fst p) (fst q)) 
       (β : Path (snd p) (snd q))
       -> Path (fst≃{B = \ _ -> B} (pair×≃ α β)) α
 ×≃β1 {p = x , y} {q = .x , .y} id id = id
 
 ×≃β2 : {A B : Type} {p q : A × B} 
       (α : Path (fst p) (fst q)) 
       (β : Path (snd p) (snd q))
     -> (snd×≃ (pair×≃ α β)) ≃ 
        β
 ×≃β2 {p = x , y} {q = .x , .y} id id = id
 
 ∘-× : {A : Type} {M N P Q R S : A} (a : N ≃ P) (b : R ≃ S) (c : M ≃ N) (d : Q ≃ R)
     -> pair×≃ a b ∘ pair×≃ c d ≃ pair×≃ (a ∘ c) (b ∘ d)
 ∘-× id id id id = id
 
 ap-×-fst : {A B : Type} {N M : A} -> (f : A -> B) -> (y : B) -> (α : M ≃ N) ->
              ap (λ x → f (x) , y) α ≃ 
              pair×≃ (ap (λ x → f x) α) (ap (λ _ → y) α)
 ap-×-fst _ _ id = id
 
 ap-×-snd : {A B : Type} {N M : A} -> (f : A -> B) -> (y : B) -> (α : M ≃ N) ->
              ap (λ x → y , f (x)) α ≃
              pair×≃ (ap (λ _ → y) α) (ap (λ x → f (x)) α)
 ap-×-snd _ _ id = id



 transport-→-post : ∀ {C A B : Set} (δ : B ≃ C) (f : A -> B) 
       -> transport (\ X -> A -> X) δ f ≃ (transport (\ X -> X) δ o f)
 transport-→-post id f = id 


 HFiber : {A B : Type} -> (A -> B) -> B -> Type
 HFiber f y = Σ \x -> Path (f x) y
