{-# OPTIONS --new-without-K --type-in-type #-}

module lib.First where

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

 postulate {- HoTT Axiom -} 
    λ≃  : ∀ {A} {B : A -> Set} {f g : (x : A) -> B x} -> ((x : A) -> Path (f x) (g x)) -> Path f g
    Π≃η : ∀ {A} {B : A -> Set} {f g : (x : A) -> B x} 
         -> (α : Path f g)
         -> α ≃ λ≃ (\ x -> ap≃ α {x})
    Π≃β : ∀ {A} {B : A -> Set} {f g : (x : A) -> B x} -> (α : (x : A) -> Path (f x) (g x)) {N : A}
         -> ap≃ (λ≃ α) {N} ≃ (α N)
    -- FIXME should assume a coherence cell too

    -- for convenience
    λ≃i : ∀ {A} {B : A -> Set} {f g : {x : A} -> B x} -> ((x : A) -> Path (f {x}) (g {x})) -> Path{ {x : A} -> B x } f g


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

