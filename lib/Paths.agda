{-# OPTIONS --type-in-type --without-K #-}

-- identity types that never use K
-- homotopically, Id M N is thought of as a path from M to N
-- we also use M ≃ N and Path M N as notation for Id M N

open import lib.First

module lib.Paths where

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

 path-induction-equiv : {B : Type} {b : B} {C : (y : B) -> Path b y → Type}
                   → Equiv ((y : B) (p : Path b y) → C y p)
                           (C b id)
 path-induction-equiv {b = b} {C = C} = (improve (hequiv (λ f → f b id) (λ b' y p → path-induction C b' p) (λ f → λ≃ (λ x → λ≃ (λ p → path-induction (λ x' x0 → Id (path-induction C (f b id) x0) (f x' x0)) id p))) (λ _ → id)))

 path-induction≃ : {B : Type} {b : B} {C : (y : B) -> Path b y → Type}
                   → ((y : B) (p : Path b y) → C y p)
                     ≃ (C b id)
 path-induction≃ = ua path-induction-equiv


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

 unitlr-coh : ∀ {A} {M : A} → (∘-unit-l (id {_}{M})) == (∘-unit-r (id {_}{M}))
 unitlr-coh = id

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

