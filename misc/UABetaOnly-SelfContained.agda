{-# OPTIONS --without-K #-}

open import Agda.Primitive

module misc.UABetaOnly-SelfContained where

 -- SKIP TO LINE 188 for the interesting part

 -- -------------------------------------------------------------------------------
 -- LIBRARY CODE, copied here to make sure I'm not using UA/funext
 -- -------------------------------------------------------------------------------

 -- paths

 data Path {l : Level} {A : Set l} (M : A) : A → Set l where
   id : Path M M

 _==_ : {l : Level} {A : Set l} → A → A → Set l
 _==_ = Path

 ! : {l : Level} {A : Set l} {M N : A} → Path M N → Path N M 
 ! id = id
 
 _∘_  : {l : Level} {A : Set l} {M N P : A} 
      → Path N P → Path M N → Path M P
 β ∘ id = β

 infixr 10 _∘_ 

 ap :  {l1 l2 : Level} {A : Set l1} {B : Set l2} {M N : A}
       (f : A → B) → Path M N → Path (f M) (f N)
 ap f id = id

 !-inv-l-front : {l : Level} {A : Set l} {M N P : A} (p : Path N P) (q : Path M N) → Path (! p ∘ p ∘ q) q
 !-inv-l-front id id = id
     
 !-inv-l  : {l : Level} {A : Set l} {M N : A} (α : Path M N) → Path (! α ∘ α) id
 !-inv-l id = id

 ∘-unit-l  : {l : Level} {A : Set l} {M N : A} (α : Path M N) → Path (id ∘ α) α
 ∘-unit-l id = id

 self-double-id : {l : Level} {A : Set l} {x : A} {α : x == x} → α == (α ∘ α) → α == id
 self-double-id {α = α} p = ! (!-inv-l-front α α ∘ ap (_∘_ (! α)) p ∘ ! (!-inv-l α))

 endo-path-naturality : {l : Level}  {A : Set l} (f : {x y : A} → x == y -> x == y) → { x y : A} (p : x == y) → f p == (p ∘ f id)
 endo-path-naturality f id = ! (∘-unit-l (f id))

 transport : {l1 l2 : Level} {B : Set l1} (E : B → Set l2) 
             {b1 b2 : B} → Path b1 b2 → (E b1 → E b2)
 transport C id = λ x → x

 coe : {l : Level} {A B : Set l} -> Path A B -> A -> B
 coe = transport (\ x -> x)

 coe-inv-1 : {l : Level} {A B : Set l} -> (α : Path A B) -> {M : _} -> coe (! α) (coe α M) == M
 coe-inv-1 id = id

 coe-inv-2 : {l : Level} {A B : Set l} -> (α : Path A B) -> {M : _} -> coe α (coe (! α) M) == M
 coe-inv-2 id = id

 -- -------------------------------------------------------------------------------
 -- sigmas

 record Σ  {l1 l2 : Level} {A : Set l1} (B : A -> Set l2) : Set (l1 ⊔ l2) where
    constructor _,_
    field
      fst : A
      snd : B fst
 open Σ public

 infixr 0 _,_

 pair= : ∀ {l1 l2} {A : Set l1} {B : A -> Set l2} {p q : Σ B} -> (α : (fst p) == (fst q)) -> (transport B α (snd p)) == (snd q) -> p == q
 pair= {p = x , y} {q = .x , .y} id id = id

 -- -------------------------------------------------------------------------------
 -- quasiequivs

 record QuasiInverse {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) : Set (l1 ⊔ l2) where
   constructor qinv
   field
     g : B → A
     α : (x : A) → Path (g (f x)) x
     β : (y : B) → Path (f (g y)) y

 QEquiv : {l1 l2 : Level} → Set l1 → Set l2 → Set (l1 ⊔ l2)
 QEquiv A B = Σ (QuasiInverse{A = A}{B})

 -- ----------------------------------------------------------------------
 -- hprops

 HProp : {l : Level} → Set l -> Set l
 HProp A = (x y : A) → x == y

 -- ----------------------------------------------------------------------
 -- I didn't have time to port all of the equivalence bootup, so I'm hypothesizing what I need
 -- I'm pretty sure these can be proved without UA/funext though

 module AssumeEquiv (IsEquiv : {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) → Set (l1 ⊔ l2))
                    (improve : {l1 l2 : Level} {A : Set l1} {B : Set l2} {f : A → B}
                             → QuasiInverse{l1}{l2} f → IsEquiv {l1}{l2}{A}{B} f) 
                    (use : {l1 l2 : Level} {A : Set l1} {B : Set l2} {f : A → B}
                             → IsEquiv {l1}{l2}{A}{B} f → QuasiInverse{l1}{l2} f)
                    (IsEquiv-HProp : {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) → HProp (IsEquiv f) )
                    where

    Equiv : {l1 l2 : Level} → Set l1 → Set l2 → Set (l1 ⊔ l2)
    Equiv A B = Σ (IsEquiv{A = A}{B})

    id-equiv : ∀ {l} {A : Set l} -> Equiv A A
    id-equiv = ( (\ x -> x) , improve (qinv (λ x → x) (\ _ -> id) (\ _ -> id)))

    -- ----------------------------------------------------------------------
    -- INTERESTING STUFF STARTS HERE! 
    -- ----------------------------------------------------------------------

    -- from Martin Escardo on HoTT book list https://github.com/HoTT/book/issues/718
    retract-of-Id-is-Id : ∀ {l1 l2 : Level} {A : Set l1} {R : A → A → Set l2} → 
                        (r : {x y : A} → x == y -> R x y)
                        (s : {x y : A} → R x y → x == y)
                        (comp1 : {x y : A} (c : R x y) → r (s c) == c) -- r is a retract of s 
                        → {x y : A} → IsEquiv {l1} {l2} {x == y} {R x y} (r {x}{y})
    retract-of-Id-is-Id {l1} {l2} r s comp1 = improve (qinv s comp2 comp1) where

       s-r-idempotent : ∀ {x y} p → s{x}{y} (r{x}{y} (s{x}{y} (r{x}{y} p))) == s (r p)
       s-r-idempotent p = ap s (comp1 (r p))
 
       comp2 : ∀ {x y} (p : x == y) → s (r p) == p
       comp2 id = self-double-id (endo-path-naturality (λ x → s (r x)) (s (r id)) ∘ ! (s-r-idempotent id)) 

    coe-is-equiv : ∀ {l : Level} {A B : Set l} (p : Path A B) → IsEquiv (coe p)
    coe-is-equiv {A}{B} p = improve (qinv (coe (! p)) (λ _ → coe-inv-1 p) (λ _ → coe-inv-2 p))

    coe-equiv : ∀ {l : Level} {A B : Set l} (p : Path A B) → Equiv A B
    coe-equiv p = (coe p , coe-is-equiv p)

    postulate
      ua : ∀ {l : Level} {A B : Set l} → Equiv A B → A == B
      uaβ : ∀ {l : Level} {A B : Set l} (e : Equiv A B) → coe (ua e) == fst e

    -- full univalence follows, where the map is coe-equiv
    full : ∀ {l : Level} {A B : Set l} → IsEquiv {_}{_} {A == B} {Equiv A B} (coe-equiv)
    full = retract-of-Id-is-Id coe-equiv ua (λ c → pair= (uaβ c) ((IsEquiv-HProp _) _ _))

    -- next we can fix the map, so that it's "the canonical one"
    -- i.e. path induction and then identity-equiv

    -- would follow from funext, but we can do it by hand
    transport-IsEquiv-homotopy : {l1 l2 : Level} {A : Set l1} {B : Set l2} {f g : A → B} 
                               → ((x : A) → f x == g x)
                               → IsEquiv f
                               → IsEquiv g
    transport-IsEquiv-homotopy h e = improve (qinv (QuasiInverse.g (use e)) (λ x → QuasiInverse.α (use e) x ∘ ap (QuasiInverse.g (use e)) (! (h x))) (λ x → QuasiInverse.β (use e) x ∘ ! (h _)))
  
    pathToEquiv : {l : Level} {A B : Set l} → Path A B → Equiv A B
    pathToEquiv id = id-equiv
  
    pathToEquiv-is-coe-equiv : ∀ {l : Level} {A B : Set l} (α : Path A B) → coe-equiv α == pathToEquiv α
    pathToEquiv-is-coe-equiv id = id
  
    fullVV : ∀ {l : Level} {A B : Set l} → IsEquiv {_}{_} {A == B} {Equiv A B} pathToEquiv
    fullVV = transport-IsEquiv-homotopy (pathToEquiv-is-coe-equiv) full
