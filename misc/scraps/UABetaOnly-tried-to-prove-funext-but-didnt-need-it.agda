{-# OPTIONS --without-K #-}

open import Agda.Primitive

module misc.UABetaOnly-SelfContained where

 -- SKIP TO LINE 188 for the interesting part

 -- -------------------------------------------------------------------------------
 -- LIBRARY CODE, copied here to make sure I'm not using UA/funext
 -- -------------------------------------------------------------------------------

 _o_ : ∀ {l1 l2 l3} {A : Set l1} {B : Set l2} {C : Set l3} → (B → C) → (A → B) → A → C
 g o f = \ x → g (f x)
 infixr 10 _o_

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

 transport-ap-assoc' : {l1 l2 l3 : Level} {A : Set l1} {B : Set l2} (C : B → Set l3) (f : A → B) {M N : A} (α : Path M N) 
                  → Path (transport (\ x -> C (f x)) α) (transport C (ap f α))
 transport-ap-assoc' C f id = id 

 transport-→-post : ∀ {l1 l2} {A : Set l1} {B C : Set l2} (δ : B == C) 
      -> transport (\ X -> A -> X) δ == (\ f → (\ z → transport (\ X -> X) δ (f z)))
 transport-→-post id = id 

 path-induction : ∀ {l1 l2} {A : Set l1} {M : A}
               (C : (x : A) → Path M x → Set l2)
            → (C M id)
            → {N : A} → (P : Path M N)
            → C N P
 path-induction _ b id = b

 path-induction-l : ∀ {l1 l2} {A : Set l1} {M : A}
               (C : (x : A) → Path x M → Set l2)
            → (C M id)
            → {N : A} → (P : Path N M)
            → C N P
 path-induction-l _ b id = b

 ap= : ∀ {l1 l2} {A : Set l1} {B : A → Set l2} {f g : (x : A) → B x} 
          → Path f g → {x : A} → Path (f x) (g x)
 ap= α {x} = ap (\ f → f x) α 
     
 infix  2 _∎
 infixr 2 _=〈_〉_ 
 
 _=〈_〉_ : ∀ {l} {A : Set l} (x : A) {y z : A} → Path x y → Path y z → Path x z
 _ =〈 p1 〉 p2 = (p2 ∘ p1)

 _∎ : ∀ {l} {A : Set l} (x : A) → Path x x
 _∎ _ = id

 -- -------------------------------------------------------------------------------
 -- sigmas

 record Σ  {l1 l2 : Level} {A : Set l1} (B : A -> Set l2) : Set (l1 ⊔ l2) where
    constructor _,_
    field
      fst : A
      snd : B fst
 open Σ public


 _×_ : ∀ {l1 l2} → (Set l1) → Set l2 → Set (l1 ⊔ l2)
 a × b = Σ (\ (_ : a) -> b)

 infixr 0 _,_

 pair= : ∀ {l1 l2} {A : Set l1} {B : A -> Set l2} {p q : Σ B} -> (α : (fst p) == (fst q)) -> (transport B α (snd p)) == (snd q) -> p == q
 pair= {p = x , y} {q = .x , .y} id id = id

 Paths : ∀ {l} → Set l → Set l
 Paths A = Σ \ (p : A × A) → fst p == snd p

 Homotopies : ∀ {l1 l2} → (Set l1) → Set l2 → Set (l1 ⊔ l2)
 Homotopies A B = (Σ \ (fg : (A -> B) × (A → B)) → (x : A) → fst fg x == snd fg x)


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
                    (use-improve-g : {l1 l2 : Level} {A : Set l1} {B : Set l2} {f : A → B} → (q : QuasiInverse{l1}{l2} f) 
                                     → QuasiInverse.g (use (improve q)) == QuasiInverse.g q) 
                    (IsEquiv-γ : ∀ {l1 l2} {A : Set l1} {B : Set l2} {f : A → B} (e : IsEquiv f)
                                    (x : A) →  Path (QuasiInverse.β (use e) (f x)) (ap f (QuasiInverse.α (use e) x)))
                    (IsEquiv-HProp : {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) → HProp (IsEquiv f) )
                    where

    Equiv : {l1 l2 : Level} → Set l1 → Set l2 → Set (l1 ⊔ l2)
    Equiv A B = Σ (IsEquiv{A = A}{B})


    id-equiv : ∀ {l} {A : Set l} -> Equiv A A
    id-equiv = ( (\ x -> x) , improve (qinv (λ x → x) (\ _ -> id) (\ _ -> id)))

    !equiv : ∀ {l1 l2} {A : Set l1} {B : Set l2} → Equiv A B → Equiv B A
    !equiv (f , e) = QuasiInverse.g (use e) , improve (qinv f (QuasiInverse.β (use e)) (QuasiInverse.α (use e)))

     -- ENH: can probably do this one without changing α or β too
    _∘equiv_ : ∀ {l1 l2 l3} {A : Set l1} {B : Set l2} {C : Set l3} -> Equiv B C → Equiv A B -> Equiv A C
    _∘equiv_ (f , e) (f' , e') = ((\ x → (f (f' x))) , improve (qinv (QuasiInverse.g (use e') o QuasiInverse.g (use e))
                                                          (λ x → QuasiInverse.α (use e') x ∘ ap (QuasiInverse.g (use e')) (QuasiInverse.α (use e) (f' x)))
                                                          (λ y → QuasiInverse.β (use e) y ∘ ap f (QuasiInverse.β (use e') (QuasiInverse.g (use e) y)))))
    
    _≃〈_〉_ : ∀ {l1 l2 l3} (x : Set l1) {y : Set l2} {z : Set l3} → Equiv x y → Equiv y z → Equiv x z
    _ ≃〈 p1 〉 p2 = (p2 ∘equiv p1)
    
    _∎∎ : ∀ {l} (x : Set l) → Equiv x x
    _∎∎ _ = id-equiv
    
    infix  2 _∎∎
    infixr 2 _≃〈_〉_ 


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

    -- ----------------------------------------------------------------------
    -- from this we can get funext
  
    -- uses η for Σ and Π
    rearrange : ∀ {l1 l2} {A : Set l1} {B : Set l2} → Equiv (A → Paths B) (Homotopies A B)
    rearrange = (λ h → ((λ x → fst (fst (h x))) , (λ x → snd (fst (h x)))) , (λ x → snd (h x))) , 
                (improve (qinv  
                            (λ i → λ x → ((fst (fst i) x) , (snd (fst i) x)) , snd i x)
                            (λ a → id) (λ _ → id)))
      -- this can be written with AC, but it's too annoying to do the beta reduction if you write it this way
      -- (apΣ-l' (AC {A = A} {B = λ _ → B} {C = λ _ _ → B})) ∘ ua (AC {A = A} {B = λ _ → B × B} {C = λ _ b1b2 → fst b1b2 == snd b1b2})

    contract-Paths≃ : ∀ {l} {A : Set l} → Equiv (Paths A) A
    contract-Paths≃ {A = A} = ((\ {((x , y) , p) -> x}) , improve (qinv (λ x → (x , x) , id) α (λ _ → id) )) where
                 α : (x : Paths A) → ((fst (fst x) , fst (fst x)) , id) == x
                 α ((x , y) , p) = path-induction (λ y₁ p₁ → ((x , x) , id) == ((x , y₁) , p₁)) id p

    abstract
      funextt : ∀ {l1 l2} {A : Set l1} {B : Set l2} → Equiv (Paths (A → B)) (Homotopies A B)
      funextt {A = A} {B} = Paths (A → B) ≃〈 contract-Paths≃ {_}{A → B} 〉 
                        (A → B) ≃〈 coe-equiv (ap (λ y → A → y) (ua (!equiv (contract-Paths≃ {_}{B})))) 〉 
                        (A → Paths B) ≃〈 rearrange 〉 
                        Homotopies A B ∎∎
    
      funextt-id : ∀ {l1 l2} {A : Set l1} {B : Set l2} (f : A → B) → fst funextt ((f , f) , id) == ((f , f) , λ x → id)
      funextt-id {A = A} f = fst funextt ((f , f) , id) =〈 id 〉 
                             fst rearrange (coe (ap (λ y → A → y) (ua (!equiv (contract-Paths≃)))) f) =〈 ap (fst rearrange) (ap= (! (transport-ap-assoc' (λ x → x) (λ y → A → y) (ua (!equiv contract-Paths≃))))) 〉 
                             fst rearrange (transport (λ y → A → y) (ua (!equiv (contract-Paths≃))) f) =〈 ap (fst rearrange) (ap= (transport-→-post (ua (!equiv contract-Paths≃)))) 〉 
                             fst rearrange (coe (ua (!equiv (contract-Paths≃))) o f) =〈 ap (λ z → fst rearrange (z o f)) (uaβ (!equiv contract-Paths≃)) 〉 
                             fst rearrange (fst (!equiv (contract-Paths≃)) o f) =〈 ap (λ h → fst rearrange (h o f)) (use-improve-g _) 〉 
                             ((f , f) , (λ x → id)) ∎
  
    preserves-fst : ∀ {l1 l2} {A : Set l1} {B : Set l2} → (α : Paths (A → B)) 
            → (fst (fst funextt α)) == fst α
    preserves-fst {A}{B} ((f , .f) , id) = ap fst (funextt-id f)
  

    HFiber : {l1 l2 : Level} {A : Set l1} {B : Set l2} -> (A -> B) -> B -> Set (l1 ⊔ l2)
    HFiber f y = Σ \x -> Path (f x) y

    hfiber-fst≃ : ∀ {l1 l2} {A : Set l1} {B : A → Set l2} (a : A) → Equiv (B a) (HFiber {A = Σ B} fst a)
    hfiber-fst≃ {B = B} a = ((λ b → (a , b) , id) , improve (qinv (λ p₁ → transport B (snd p₁) (snd (fst p₁))) (λ _ → id) (λ {((a1 , b) , p) → path-induction-l (λ a2 p₁ → (b₁ : B a2) → Path ((a , transport B p₁ b₁) , id) ((a2 , b₁) , p₁)) (λ _ → id) p b})))

    fiberwise-to-total : ∀ {l1 l2} {A : Set l1} {B B' : A → Set l2} → (f : (a : A) → B a → B' a) → Σ B → Σ B'
    fiberwise-to-total f (a , b) = (a , f a b)

    fiberwise-equiv-to-total≃ : ∀ {l1 l2} {A : Set l1} {B B' : A → Set l2} → ((x : A) → Equiv (B x) (B' x)) → Equiv (Σ B) (Σ B')
    fiberwise-equiv-to-total≃ h = ((fiberwise-to-total (\ x -> fst (h x))) , improve (qinv 
                                                   (fiberwise-to-total (λ x → QuasiInverse.g (use (snd (h x)))))
                                                   (λ x → ap (λ y → fst x , y) (QuasiInverse.α (use (snd (h (fst x)))) _))
                                                   (λ x → ap (λ y → fst x , y) (QuasiInverse.β (use (snd (h (fst x)))) _))))

    transport-inv-1 : ∀ {l1 l2} {A : Set l1} (B : A -> Set l2) {M N : A} (α : M == N) -> (\y -> transport B (! α) (transport B α y)) == (\ x -> x)
    transport-inv-1 _ id = id
 
    transport-inv-2 : ∀ {l1 l2} {A : Set l1} (B : A -> Set l2) {M N : A} (α : M == N) -> (\y -> transport B α (transport B (! α) y)) == (\ x -> x)
    transport-inv-2 _ id = id

    apΣ-l≃ : ∀ {l1 l2} {A A' : Set l1} {B : A → Set l2} 
           (a : Equiv A A')
           → Equiv (Σ B) (Σ (\ (x : A') → B (QuasiInverse.g (use (snd a)) x)))
    apΣ-l≃ {B = B} a = (λ p → fst a (fst p) , transport B (! (QuasiInverse.α (use (snd a)) _)) (snd p)) , improve (qinv
                                       (λ p → QuasiInverse.g (use (snd a)) (fst p) , snd p) 
                                       (λ x → pair= (QuasiInverse.α (use (snd a)) (fst x)) (ap= (transport-inv-2 B (QuasiInverse.α (use (snd a)) (fst x)))))
                                       (λ x → pair= (QuasiInverse.β (use (snd a)) (fst x))
                                                                    ((ap= (transport-inv-2 B (QuasiInverse.α (use (snd a)) (QuasiInverse.g (use (snd a)) (fst x)))) ∘ 
                                                                      ap {M = ap (QuasiInverse.g (use (snd a))) (QuasiInverse.β (use (snd a)) (fst x))} {N = QuasiInverse.α (use (snd a)) (QuasiInverse.g (use (snd a)) (fst x))} (λ H → transport B H (transport B (! (QuasiInverse.α (use (snd a)) (QuasiInverse.g (use (snd a)) (fst x)))) (snd x)))
                                                                         {!! (IsEquiv-γ (snd (!equiv a)) (fst x)) !} ∘ 
                                                                      ap= (transport-ap-assoc' B (QuasiInverse.g (use (snd a))) (QuasiInverse.β (use (snd a)) (fst x)))))))
                                                                          -- ap= (ap (λ z → transport B z) (! {! (IsEquiv-γ (snd (!equiv a)) (fst x))!}))) ∘
                                                                          -- ap= (transport-ap-assoc' B (QuasiInverse.g (use (snd a))) (QuasiInverse.β (use (snd a)) (fst x))))))  
    !-inv-r-back : ∀ {l} {A : Set l} {M N P : A} (q : Path N M) (p : Path P N) → Path (q ∘ (p ∘ ! p)) q
    !-inv-r-back id id = id

    !-inv-l-back : ∀ {l} {A : Set l} {M N P : A} (q : Path N M) (p : Path N P) → Path (q ∘ ! p ∘ p) q
    !-inv-l-back id id = id

    ∘-assoc  : ∀ {l} {A : Set l} {M N P Q : A} 
          (γ : Path P Q) (β : Path N P) (α : Path M N) 
          → Path (γ ∘ (β ∘ α)) ((γ ∘ β) ∘ α)
    ∘-assoc id id id = id


    pre∘-equiv : ∀ {l} {A : Set l} {a b c : A} → (a == b) -> Equiv (b == c) (a == c)
    pre∘-equiv α = ((λ β → β ∘ α) , improve (qinv (λ β' → β' ∘ ! α) (λ β → !-inv-r-back β α ∘ ! (∘-assoc β α (! α))) (λ β → !-inv-l-back β α ∘ ! (∘-assoc β (! α) α))))

    fiberwise-equiv-from-total≃ : ∀ {l1 l2} {A : Set l1} {B B' : A → Set l2} → 
                               (t : Equiv (Σ B) (Σ B'))
                            → ((y : Σ B) → fst (fst t y) == fst y)
                            → ((x : A) → Equiv (B x) (B' x))
    fiberwise-equiv-from-total≃ {A = A}{B}{B'} t f x = 
                      B x ≃〈 hfiber-fst≃ x 〉 
                      HFiber {_}{_}{(Σ B)} fst x ≃〈 apΣ-l≃ t 〉 
                      HFiber {_}{_}{(Σ B')} (fst o (QuasiInverse.g (use (snd t)))) x ≃〈 fiberwise-equiv-to-total≃ (λ x₁ → pre∘-equiv (f (QuasiInverse.g (use (snd t)) x₁) ∘ ap fst (! (QuasiInverse.β (use (snd t)) _)))) 〉
                      HFiber {_}{_}{(Σ B')} fst x ≃〈 !equiv (hfiber-fst≃ x) 〉
                      B' x ∎∎


    funext : ∀ {l1 l2} {A : Set l1 } {B : Set l2} (f g : A → B) → Equiv (f == g) ((x : A) → f x == g x)
    funext {A}{B} f g = fiberwise-equiv-from-total≃ funextt preserves-fst (f , g)

    -- ----------------------------------------------------------------------
    -- from funext we can fix the map to be "the canonical one" (path induction -> id-equiv)


    transport-IsEquiv-homotopy : {l1 l2 : Level} {A : Set l1} {B : Set l2} {f g : A → B} 
                               → ((x : A) → f x == g x)
                               → IsEquiv f
                               → IsEquiv g
    transport-IsEquiv-homotopy h e = {!!}
  
    pathToEquiv : {l : Level} {A B : Set l} → Path A B → Equiv A B
    pathToEquiv id = id-equiv
  
    pathToEquiv-is-coe-equiv : ∀ {l : Level} {A B : Set l} (α : Path A B) → coe-equiv α == pathToEquiv α
    pathToEquiv-is-coe-equiv id = id
  
    fullVV : ∀ {l : Level} {A B : Set l} → IsEquiv {_}{_} {A == B} {Equiv A B} pathToEquiv
    fullVV = transport IsEquiv (QuasiInverse.g (use (snd (funext coe-equiv pathToEquiv))) pathToEquiv-is-coe-equiv) full
