{-# OPTIONS --type-in-type --without-K --allow-unsolved-metas #-}

open import lib.First
open import lib.Paths 
open import lib.Prods

module lib.Functions where 

  -- interchange law for the type theory as a whole:
  -- objects = types
  -- morphisms = functions
  -- 2-cells = identity type
  ichange-theory : {Γ1 Γ2 Γ3 : Set} 
                   {θ1 θ2 θ3 : Γ1 -> Γ2} 
                   {θ1' θ2' θ3' : Γ2 -> Γ3} 
                   (δ1 : θ1 ≃ θ2) (δ2 : θ2 ≃ θ3)
                   (δ1' : θ1' ≃ θ2') (δ2' : θ2' ≃ θ3')
                 -> ap2 _o_ (δ2' ∘ δ1') (δ2 ∘ δ1) ≃ ap2 _o_ δ2' δ2 ∘ ap2 _o_ δ1' δ1 
  ichange-theory id id id id = id
  
  ap≃i : ∀ {A} {B : A -> Set} {f g : {x : A} -> B x} 
       -> Path (\ {x} -> f {x}) (\ {x} -> g {x}) -> ({x : A} -> Path (f {x}) (g {x}))
  ap≃i α {x} = ap (\ f -> f {x}) α

  -- apply a path to a 1-cell (path)
  ap≃₁ : ∀ {A} {B : A -> Set} {f g : (x : A) -> B x} 
       -> Path f g -> ({x y : A} -> (α : Path x y) -> Path (transport B α (f x)) (g y))
  ap≃₁ {A} {B} {f} {.f} id id = id 

  ap≃₁' : ∀ {A} {B : A -> Set} {f g : (x : A) -> B x} 
       -> Path f g -> ({x y : A} -> (α : Path x y) -> Path (f x) (transport B (! α) (g y)))
  ap≃₁' {A} {B} {f} {.f} id id = id 

  -- non-dependent version
  ap≃₁→ : {A B : Type} {f g : A → B} {x y : A} → f ≃ g → x ≃ y → f x ≃ g y
  ap≃₁→ α β = ap2 (\ f x -> f x) α β

  module ΠPath where
    eqv : {A : Type} {B : A → Type} {f g : (x : A) → B x} 
        → Equiv ((x : A) → Path (f x) (g x)) (Path f g)
    eqv = improve (hequiv λ≃ (λ α → λ x → ap≃ α {x}) (λ α → λ≃ (λ x → Π≃β α)) (λ y → ! (Π≃η y)))

    path : {A : Type} {B : A → Type} {f g : (x : A) → B x} 
        → ((x : A) → Path (f x) (g x)) ≃ (Path f g)
    path = ua eqv

  Π≃ext : {A : Type} {B : A → Type} {f g : (x : A) → B x} {α β : f ≃ g}
          → ((x : A) → ap≃ α {x} ≃ ap≃ β {x}) → α ≃ β
  Π≃ext h = (! (Π≃η _) ∘ ap λ≃ (λ≃ h)) ∘ Π≃η _ 

  transport-→ :  {Γ : Type} (A B : Γ → Type) {θ1 θ2 : Γ} 
                  (δ : θ1 ≃ θ2) (f : A θ1 → B θ1) 
     → Path  (transport (\ γ → (A γ) → B γ) δ f) 
             (transport B δ o f o (transport A (! δ)))
  transport-→ _ _ id f = id 
   
  transport-→-pre : ∀ {C A B : Set} (δ : A ≃ B) (f : A -> C) 
         -> transport (\ X -> X -> C) δ f ≃ (f o (transport (\ X -> X) (! δ)))
  transport-→-pre id f = id 

  transport-→-post : ∀ {C A B : Set} (δ : B ≃ C) (f : A -> B) 
         -> transport (\ X -> A -> X) δ f ≃ (transport (\ X -> X) δ o f)
  transport-→-post id f = id 

  transport-→-from-square :  ∀ {A} (B C : A → Type) {a a' : A} (α : a ≃ a') 
                             (f : B a -> C a) (g : B a' -> C a')
                          -> transport C α o f ≃ g o (transport B α)
                          -> transport (\ x -> B x -> C x) α f ≃ g
  transport-→-from-square _ _ id _ _ p = p

  transport-→-pre' : {Γ B : Type} (A : Γ -> Type) {θ1 θ2 : Γ} 
                  (δ : θ1 ≃ θ2) (f : (x : A θ1) → B) 
     → Path  (transport (\ γ → (A γ) → B) δ f) 
             (\ x -> f (transport (\ γ -> A γ) (! δ) x))
  transport-→-pre' _ id f = id 

  transport-Π-post' :  {Γ A : Type} (B : Γ → A -> Type) {θ1 θ2 : Γ} 
                  (δ : θ1 ≃ θ2) (f : (x : A) → B θ1 x) 
     → Path  (transport (\ γ → (x : A) → B γ x) δ f) 
             (\ x -> transport (\ γ -> B γ x) δ (f x))
  transport-Π-post' _ id f = id 

  transport-Π : ∀ {Γ} (A : Γ -> Set) (B : (γ : Γ) -> A γ -> Set)
            {θ1 θ2 : Γ} (δ : θ1 ≃ θ2) (f : (x : A θ1) -> B θ1 x) 
         -> transport (\ γ -> (x : A γ) -> B γ x) δ f ≃ 
            (\ x -> transport (\ (p : Σ \ (γ : Γ) -> A γ) -> B (fst p) (snd p))
                          (pair≃⁻ δ id)
                          (f (transport A (! δ) x)))
  transport-Π _ _ id f = id

  transport-Πi : ∀ {Γ} (A : Γ -> Set) (B : (γ : Γ) -> A γ -> Set)
            {θ1 θ2 : Γ} (δ : θ1 ≃ θ2) (f : {x : A θ1} -> B θ1 x) 
         -> Path{ {x : A θ2} -> B θ2 x}
              (transport (\ γ -> {x : A γ} -> B γ x) δ f)
              (\ {x} -> transport (\ (p : Σ \ (γ : Γ) -> A γ) -> B (fst p) (snd p))
                              (pair≃⁻ δ id)
                              (f {(transport A (! δ) x)}))
  transport-Πi _ _ id f = id

  -- only the range depends on the predicate
  transport-Π2 : ∀ {Γ} (A : Set) (B : (γ : Γ) -> A -> Set)
            {θ1 θ2 : Γ} (δ : θ1 ≃ θ2) (f : (x : A) -> B θ1 x) 
         -> transport (\ γ -> (x : A) -> B γ x) δ f ≃ 
            (\ x -> transport (\ γ -> B γ x) δ (f x))
  transport-Π2 _ _ id f = id

  transport-Π2i : ∀ {Γ} (A : Set) (B : (γ : Γ) -> A -> Set)
            {θ1 θ2 : Γ} (δ : θ1 ≃ θ2) (f : {x : A} -> B θ1 x) 
         -> Path{ {x : A} -> B θ2 x }
            (transport (\ γ -> {x : A} -> B γ x) δ f)
            (\ {x} -> transport (\ γ -> B γ x) δ (f {x}))
  transport-Π2i _ _ id f = id 

  -- could have →≃β for application to a single term, and
  -- →≃β2 for the other way to go around the square
  →≃β1 : {A B : Type} {f g : A → B} {x y : A} → (α : (x : _) → f x ≃ g x) (β : x ≃ y) 
             → ap≃₁→ (λ≃ α) β ≃ ap g β ∘ (α x) 
  →≃β1 α id = ap2 (λ f x → f x) (λ≃ α) id ≃〈 ap2-aps-1 (λ f x → f x) (λ≃ α) id 〉
                  ap≃ (λ≃ α) ≃〈 Π≃β α 〉
                  (α _) ≃〈 ! (∘-unit-l _) 〉
                  (id ∘ α _ ∎)

  -- →≃β1 and →≃β2 cohere
  naturality1 : {A B : Set} {F G : A -> B}
              -> (β : G ≃ F) 
              -> {M N : A} (α : M ≃ N) 
              -> ap G α ≃ ! (ap≃ β {N}) ∘ ap F α ∘ ap≃ β {M}
  naturality1 id id = id

  ap-λ : {Γ : Set} {θ1 θ2 : Γ} {δ : θ1 ≃ θ2}
           {A : Γ -> Set} {B : (γ : Γ) -> A γ -> Set}
           {M : (γ : Γ) -> (x : A γ) -> B γ x}
        -> (apd (\ γ -> (λ x -> M γ x)) δ) 
         ≃ λ≃ (λ γ → apd (λ (p : Σ (λ (γ' : Γ) → A γ')) → M (fst p) (snd p))
                           (pair≃⁻ δ id))
           ∘ transport-Π A B δ (M θ1)
  ap-λ {δ = id} = Π≃η id

  -- when they're independent, it looks like a kind of exchange 
  ap-λ-range-nd : {Γ : Set} {A B : Set} 
                  (M : Γ -> A -> B) {θ1 θ2 : Γ} (δ : θ1 ≃ θ2)
           -> (ap (\ γ -> (λ x -> M γ x)) δ) 
            ≃ λ≃ (λ x → ap (\ γ -> M γ x) δ)
  ap-λ-range-nd M id = Π≃η id

  transport-com-for-ap-app : 
    {Γ : Set} {θ1 θ2 : Γ} (δ : θ1 ≃ θ2)
    (A : Γ -> Set) (B : (γ : Γ) -> A γ -> Set)
    (F : (γ : Γ) -> (x : A γ) -> B γ x)
    (M : (γ : Γ) -> A γ)
   -> Path (transport (λ z → B z (M z)) δ (F θ1 (M θ1)))
        (transport (λ z → B θ2 z) (apd M δ)
         (transport (λ z → (x : A z) → B z x) δ (F θ1)
          (transport (λ z → A z) δ (M θ1))))
  transport-com-for-ap-app id _ _ _ _ = id

  ap-app : {Γ : Set} {θ1 θ2 : Γ} {δ : θ1 ≃ θ2}
             {A : Γ -> Set} {B : (γ : Γ) -> A γ -> Set}
             {F : (γ : Γ) -> (x : A γ) -> B γ x}
             {M : (γ : Γ) -> A γ}
           -> apd (\ γ -> (F γ) (M γ)) δ 
            ≃ ap≃₁ (apd F δ) (apd M δ) ∘ transport-com-for-ap-app δ A B F M
  ap-app {δ = id} = id

  ap-app-1-nd : {Γ A B : Set} 
                  (F : Γ -> A -> B)
                  {θ1 θ2 : Γ} (δ : θ1 ≃ θ2) (M : A)
               -> ap (\ x -> (F x) M) δ ≃ ap≃ (ap F δ) {M}
  ap-app-1-nd _ id _ = id

  -- NOTE: special case of ap-λ and ap-app 
  ap-of-o : {A B C D : _} (f : A → B → C) (g : A → D → B) {M N : A} (α : M ≃ N)
          → ap (\ x -> f x o g x) α ≃ λ≃ (λ x → ap2 (λ f' x' → f' x') (ap f α) (ap (λ y → g y x) α))
  ap-of-o f g id = Π≃η id

  uncurry : ∀ {A B C : Set} -> (A -> B -> C) -> A × B -> C
  uncurry f = \ x -> f (fst x) (snd x)

  ap-uncurry : {A B C : Set} (f : A -> B -> C) -> ∀ {M M' N N'} ->
                 (α : M ≃ M') (β : N ≃ N') 
                 -> ap (uncurry f) (pair×≃ α β)
                    ≃ ap2 f α β
  ap-uncurry f id id = id

  uncurryd : ∀ {A : Set} {B : A → Type} {C : (x : A) → B x → Set} -> ((a : A) (b : B a) -> C a b) -> (p : (Σ B)) -> C (fst p) (snd p)
  uncurryd f = \ x -> f (fst x) (snd x)

  ∘Π : ∀ {A} {B : A → Type} {f g h : (x : A) → B x} (β : g ≃ h) (α : f ≃ g) 
      → β ∘ α ≃ λ≃ (\x -> ap≃ β {x} ∘ ap≃ α {x})
  ∘Π id id = Π≃η id

  ∘λ≃ : ∀ {A} {B : A → Type} {f g h : (x : A) → B x} (β : (x : A) → g x ≃ h x) (α : (x : A) → f x ≃ g x) 
      → λ≃ β ∘ λ≃ α ≃ λ≃ (\x -> β x ∘ α x)
  ∘λ≃ β α = ap λ≃ (λ≃ (λ x → ap∘ (Π≃β β) (Π≃β α))) ∘ ∘Π (λ≃ β) (λ≃ α)


  abstract 
    Πlevel : ∀{A n}{B : A → Type} → ((x : A) -> NType n (B x)) → NType n ((x : A) → B x)
    Πlevel {A} { -2} a = ntype ((λ x → fst (use-level (a x))) , (λ f → λ≃ (λ x → snd (use-level (a x)) (f x))))
    Πlevel {A} {S n} a = ntype (λ f g → transport (NType n) (ua ΠPath.eqv) (Πlevel {A} {n} (λ x → use-level (a x) _ _)))

  uncurry≃ : (A : Type) (B : A -> Type) (C : Σ B -> Type)
           -> ((p : Σ B) → C p)
           ≃  ((x : A) (y : B x) -> C (x , y))
  uncurry≃ _ _ _ = ua (equiv (λ f x y → f (x , y)) (λ f p → f (fst p) (snd p)) (λ _ → id) (λ _ → id) (λ _ → id))
 
  exchange≃ : {A : Type} {B : Type} {C : A → B → Type}
            -> ((x : A) (y : B) → C x y)
             ≃ ((y : B) (x : A) → C x y)
  exchange≃ = ua (equiv (λ f x y → f y x) (λ f x y → f y x) (λ _ → id) (λ _ → id) (λ _ → id))

  ΠΣcommuteEquiv : (A : Type) (B : A -> Type) (C : (x : A) → B x → Type)
            → Equiv ((x : A) → (Σ \ (y : B x) -> C x y))
                    (Σ \ (f : (x : A) →  B x) → ((x : A) → C x (f x)))
  ΠΣcommuteEquiv A B C = (improve (hequiv ((λ f → (λ x → fst (f x)) , (λ x → snd (f x))))
                                           (λ p → λ x → fst p x , snd p x) (λ _ → id) (λ _ → id)))

  ΠΣcommute : (A : Type) (B : A -> Type) (C : (x : A) → B x → Type)
            → ((x : A) → (Σ \ (y : B x) -> C x y))
            ≃ Σ \ (f : (x : A) →  B x) → ((x : A) → C x (f x))
  ΠΣcommute A B C = ua (ΠΣcommuteEquiv A B C) 

  apΠ : {A A' : Type} {B : A → Type} {B' : A' → Type}
      (a : A == A')
      (b : (\ (x : A) → B x) == (\ (x : A) → B' (coe a x)))
    → ((x : A) → B x) == ((x' : A') → B' x')
  apΠ id id = id

  apΠ' : {A A' : Type} {B : A → Type} {B' : A' → Type}
       (a : Equiv A A')
       (b : (x' : A') → B (IsEquiv.g (snd a) x') ≃ B' x')
     → ((x : A) → B x) ≃ ((x' : A') → B' x')
  apΠ' {A = A} {B = B} {B' = B'}  a b = apΠ (ua a) (λ≃ (λ x' → ap B' (! (ap≃ (type≃β a))) ∘ b (fst a x') ∘ ap B (! (IsEquiv.α (snd a) _)))) 

  -- also comes up in UA implies funext, but easier to do it with funext
  postcomp-equiv-is-equiv : ∀ {A B C} → (e : Equiv B C) → IsEquiv {A → B} {A → C} (\ f -> (fst e o f))
  postcomp-equiv-is-equiv {A} e = transport IsEquiv ((λ≃ (λ f → λ≃ (λ x → ap (λ g → g (f x)) (type≃β e) ∘ ap≃ (transport-→-post (ua e) f)))) ∘ ! (transport-ap-assoc (λ x → A → x) (ua e))) (snd (coe-equiv (ap (λ x → A → x) (ua e))))

  precomp-equiv-is-equiv : ∀ {A B C} → (e : Equiv B C) → IsEquiv {C → A} {B → A} (\ f -> (f o (fst e)))
  precomp-equiv-is-equiv {A}{B}{C} e = transport IsEquiv (λ≃ (λ f → λ≃ (λ x → ap (λ x₁ → f x₁) (ap≃ (type≃β e) {x} ∘ ap (λ z → coe z x) (!-invol (ua e))) ∘ ap≃ (transport-→-pre (! (ua e)) f))) ∘
                                                            ! (transport-ap-assoc (λ x → x → A) (! (ua e)))) (snd (coe-equiv (ap (λ x → x → A) (! (ua e)))))


