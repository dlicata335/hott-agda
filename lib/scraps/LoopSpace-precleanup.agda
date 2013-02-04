{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open import lib.Prods
open import lib.Int

open Int
open import lib.AdjointEquiv
open import lib.Functions
open import lib.Univalence

module lib.LoopSpace where

  collapse : ∀ {A} {a b : A} (α : Path a b) {β : Path a a} → (β ≃ id) → (α ∘ β ∘ ! α) ≃ id
  collapse α δ = (!-inv-r α ∘ ap (λ x → α ∘ x) (∘-unit-l (! α))) ∘ ap (λ x → α ∘ x ∘ ! α) δ

  mutual
    Loop : (n : Positive) (A : Type) (base : A) → Type
    Loop One A b = Path b b
    Loop (S n) A b = Path {Loop n A b} (id^ n) (id^ n)

    id^ : ∀ n {A b} → Loop n A b
    id^ One = id
    id^ (S n) = id{_}{id^ n}

  mutual
    rebase : ∀ n → ∀ {A a a'} (α : a ≃ a') -> Loop n A a → Loop n A a'
    rebase One α l = α ∘ l ∘ ! α
    rebase (S n) α l = rebase-id n α ∘ ap (rebase n α) l ∘ ! (rebase-id n α)
    
    rebase-id : ∀ n → ∀ {A} {a a' : A} (α : a ≃ a') -> rebase n α (id^ n) ≃ id^ n
    rebase-id One α = collapse α id
    rebase-id (S n) α = collapse (rebase-id n α) id

  postulate 
    transport-Loop-base : ∀ n → ∀ {A a a'} (α : a ≃ a') →
                          transport (Loop n A) α ≃ rebase n α
    rebase-idpath : ∀ n → {A : Type} {a : A} -> rebase n (id{_}{a}) ≃ \ x -> x

  mutual 
    ap^ : ∀ {A B} → (n : _) → (f : A → B) → {base : A} → Loop n A base → Loop n B (f base)
    ap^ One   f {base} l = ap f l 
    ap^ (S n) f {base} l = ap^-id n f ∘ ap (ap^ n f) l ∘ ! (ap^-id n f)

    ap^-id : ∀ {A B} → (n : _) → (f : A → B) → {base : A} →
             ap^ n f (id^ n) ≃ id^ n {_} {f base} 
    ap^-id One f = id
    ap^-id (S n) f = collapse (ap^-id n f) id

  ∘^ : ∀ n {A a} → Loop n A a → Loop n A a → Loop n A a
  ∘^ One p q = p ∘ q
  ∘^ (S n) p q = p ∘ q

  infixr 10 ∘^

  !^ : ∀ n → ∀ {A a} → Loop n A a → Loop n A a 
  !^ One q = ! q
  !^ (S n) q = ! q

  postulate 
    ap^-idfunc : ∀ {A} {a : A} → (n : _) (α : Loop n A a) → ap^ n (\ (x : A) -> x) α ≃ α

{-
  ap^-o : ∀ {A B C} → (n : _) → (g : B → C) (f : A → B)
        → {a : A} (α : Loop n A a)
        → ap^ n (g o f) α ≃ ap^ n g (ap^ n f α) 
  ap^-o One g f α = ap-o g f α
  ap^-o (S n) g f α = {!!}
-}

  mutual 
    LoopOver : (n : Positive) {A : Type} {a : A} (α : Loop n A a) 
             → (B : A -> Type) (b : B a) → Type
    LoopOver One α B b = transport B α b ≃ b
    LoopOver (S n) α B b = Path {LoopOver n (id^ n) B b}
                                (transport (λ x → LoopOver n x B b) α (idOver n B b)) 
                                (idOver n B b)

    idOver : (n : Positive) {A : Type} {a : A} (B : A → Type) (b : B a) 
           → LoopOver n (id^ n) B b
    idOver One B b = id
    idOver (S n) B b = id

  {-
  n = (S (S (S (S One))))

  test : {S : Type} {base : S} (loop : Loop n S base) → (B : S → Type) (b : B base) → Type 
  test {Sn} {base} loop X x = {!LoopOver n loop X x !}
  -}

  postulate
    LoopΠ : ∀ n → ∀ {A} {B : A → Type} {f : _} → 
            ((x : A) → Loop n (B x) (f x))
          ≃ (Loop n ((x : A) -> B x) f)

  Loop→ : ∀ n → ∀ {A B} {f : A → B} → 
            ((x : A) → Loop n B (f x))
          ≃ (Loop n (A -> B) f)
  Loop→ n {A}{B} = LoopΠ n {A} {\ _ -> B}

{-
   LoopΠ n {A} {B} {m} = improve (hequiv (i n) (e n) {!!} {!!}) where
   mutual  
    i : ∀ n → ((x : A) → Loop n (B x) (m x)) → Loop n ((x : A) → B x) m
    i One   α = λ≃ α
    i (S n) α = i-id n ∘ ap (i n) (λ≃ α) ∘ ! (i-id n) 

    i-id : ∀ n → i n (\ x -> (id^ n)) ≃ (id^ n)
    i-id One = ! (Π≃η id)
    i-id (S n') = collapse (i-id n') (ap (ap (i n')) (! (Π≃η id)))

   mutual  
    e : ∀ n → Loop n ((x : A) → B x) m → (x : A) → Loop n (B x) (m x)
    e One   = λ α x → ap≃ α {x}
    e (S n) = λ α x → e-id n ∘ ap≃ (ap (e n) α) {x} ∘ ! (e-id n)

    e-id : ∀ n → ∀ {x} → e n (id^ n) x ≃ (id^ n)
    e-id One = id
    e-id (S n') = collapse (e-id n') id

   mutual
    β : ∀ n → (a : (x' : A) → Loop n (B x') (m x')) → (e n (i n a)) ≃ a
    β One a = λ≃ (λ x → Π≃β a)
    β (S n) a = {!!}

    {-
    β-id : ∀ n x → e-id n ∘ ap≃ (ap (e n) (i-id n)) {x} ≃ {!!}
    β-id = {!!}
    -}
-}

  -- lots of other definitions should be equivalent
  ap≃→^ : ∀ n {A B} {f x} → Loop n (A → B) f → Loop n A x → Loop n B (f x)
  ap≃→^ n {A}{B}{f}{x} α β = ∘^ n (coe (! (LoopΠ n)) α x) (ap^ n f β)

  LoopPath : ∀ {n A a} 
             → (Loop (S n) A a) ≃ (Loop n (Path a a) id) -- what about for non-id?
  LoopPath {n} {A} {α} = ua (improve (hequiv (i n) (e n) β η)) where
   mutual
    i : ∀ n → Loop (S n) A α → Loop n (Path α α) id
    i One l = l
    i (S n) l = i-id n ∘ ap (i n) l ∘ ! (i-id n)

    i-id : ∀ n → i n id ≃ id^ n
    i-id One = id
    i-id (S n) = collapse (i-id n) id

   mutual
    e : ∀ n → Loop n (Path α α) id → Loop (S n) A α 
    e One l = l
    e (S n) l = e-id n ∘ ap (e n) l ∘ ! (e-id n)

    e-id : ∀ n → e n (id^ n) ≃ id
    e-id One = id
    e-id (S n) = collapse (e-id n) id

   postulate 
     β : _
     η : _

  postulate
    -- FIXME: works for non-id base?  
    LoopPathType : ∀ n {A} -> Loop n (Path{Type} A A) id ≃ ((a : A) -> Loop n A a)
    -- LoopPathType n {A} = Loop n (Path A A) id ≃〈 ! (LoopPath{n}) 〉 
    --                    Loop (S n) Type A    ≃〈 {!!} 〉 
    --                    ((x : A) -> Loop n A x) ∎
    -- forward direction should be \ x -> (ap^ n (λ x → coe x a))

  LoopSType : ∀ n {A} -> Loop (S n) Type A ≃ ((a : A) -> Loop n A a)
  LoopSType n = ua (improve (hequiv (λ α y → (ap^ n (λ x → coe x y) α))
                                    (λ h → {! (coe (Loop→ n) h) !})
                                    {!!}
                                    {!!}))
                ∘ (LoopPath{n})
  

  postulate
    ap^-ap-assoc : ∀ {A B} → (n : _) → (f : A → B) → {a : A} 
                   (α : Loop n (Path a a) id)
                 → (ap^ n (ap f) α) ≃ coe (LoopPath{n}) (ap^ (S n) f (coe (! (LoopPath{n})) α))

  LoopOver' :  (n : Positive) {A : Type} {a : A} (α : Loop (S n) A a) 
             → (B : A -> Type) (b : B a) → Type
  LoopOver' n {A}{a} α B b = 
    Path{Loop n (B a) b} 
        (coe (LoopSType n) (ap^ (S n) B α) b)
        (id^ n)
            -- where 
            --   loop1 : Loop (S n) Type (B a)
            --   loop1 : (ap^ (S n) B α)
            
            --   coe (LoopPath {n}) loop1 : Loop n (Path Type Type) (B a)
            -- \ α y → ap^ n (\ x -> coe x y) α : Loop n (Path Type Type) (B a) → ((y : B a) → Loop n (B a) y)

  postulate 
    LoopOverS : (n : Positive) {A : Type} {a : A} (α : Loop (S n) A a) → (B : A -> Type) (b : B a) 
              → LoopOver (S n) α B b ≃ LoopOver' n α B b 


  LoopType→ : ∀ n {A B} → (Loop (S n) Type A) -> Loop (S n) Type B -> Loop (S n) Type (A → B)
  LoopType→ n lA lB = coe (! (LoopSType n)) 
                          (λ f → coe (Loop→ n) (λ x → ∘^ n (coe (LoopSType n) lB (f x)) 
                                                           (ap^ n f (coe (LoopSType n) (!^ (S n) lA) x))))

  postulate
    ap^→ : ∀ {A} → (n : _) → (C D : A → Type) → {base : A} {α : Loop (S n) A base} →
           ap^ (S n) (\ x -> C x → D x) α 
         ≃ LoopType→ n (ap^ (S n) C α) (ap^ (S n) D α)

  -- note: non-dependent 
  postulate
   LoopPathOver : (n : Positive) {A : Type} {a : A} (α : Loop n A a) 
                → {B : Type} (f g : A → B) (β : Path {B} (f a) (g a))
                →   (Path {Loop n B (g a)} (rebase n β (ap^ n f α)) (ap^ n g α))
                  ≃ (LoopOver n α (\ x -> f x ≃ g x) β) 
  {-
  LoopPathOver n {A}{a} α B f g β = ua (improve (hequiv (i n α) {!!} {!!} {!!})) where
   mutual
    i : ∀ n (α : Loop n A a) 
          → (Path {Loop n B (g a)} (rebase n β (ap^ n f α)) (ap^ n g α))
          → (LoopOver n α (\ x -> f x ≃ g x) β) 
    i One α p = {!!}
    i (S n) α p = transport (λ x → LoopOver n x (λ x' → Id (f x') (g x')) β) α (idOver n (λ x → Id (f x) (g x)) β) ≃〈 {!!} 〉 
                  (i n _
                   (transport (\ x -> (Path {Loop n B (g a)} (rebase n β (ap^ n f x)) (ap^ n g x)))
                            α 
                            (e n _ (idOver n (λ x → Id (f x) (g x)) β)))) ≃〈 {!transport-by (i n)!} 〉 
                  (i n _
                   (ap (ap^ n g) α ∘
                    (e n _ (idOver n (λ x → Id (f x) (g x)) β)) ∘ 
                    ! (ap (\ x -> rebase n β (ap^ n f x)) α))) ≃〈 {!p!} 〉 
                  (i n _
                   (ap (ap^ n g) α ∘
                    (e n _ (idOver n (λ x → Id (f x) (g x)) β)) ∘ 
                    ! (ap (\ x -> rebase n β (ap^ n f x)) α))) ≃〈 {!e-id!} 〉 
                  (idOver n (λ x → Id (f x) (g x)) β ∎) where
     p' :  ap ((rebase n β) o (ap^ n f)) α 
         ≃ ! (rebase-id n β ∘ ap (rebase n β) (ap^-id n f)) 
         ∘ (ap^-id n g ∘ ap (ap^ n g) α ∘ ! (ap^-id n g) 
         ∘ ((rebase-id n β) ∘ (ap (rebase n β) (ap^-id n f))))
     p' = {!rearrange p!}

    e : ∀ n (α : Loop n A a) 
          → (LoopOver n α (\ x -> f x ≃ g x) β) 
          → (Path {Loop n B (g a)} (rebase n β (ap^ n f α)) (ap^ n g α))
    e = {!!}
  -}

  {-
  n = S One
  test : (Γ : Type) (A B : Γ → Set) (g : Γ) (α : Loop n Γ g) (f : A(g) → B(g)) -> Type
  test Γ A B g α f = {!LoopOver n α (\ x -> A (x) → B x) f !}
  -}

  Loop→Over' : (n : Positive) {A : Type} {a : A} (α : Loop n A a) 
            → {B : Type} (C D : A → Type) (h : C a → D a) → (x : C a) → Type
  Loop→Over' n{A}{a} α {B} C D h x = 
                         Path{Loop n (_) (_)} 
                             {!coe (LoopPathType (S n) ∘ (! (LoopPath {n}))) (ap^ (S n) C α)
                                     !}
                             (id^ n)
             where 
               arg : Loop n Type (C a)
               arg = (ap^ n C (!^ n α))

               res : Loop n Type (D a)
               res = (ap^ n D α)


  Loop→Over : (n : Positive) {A : Type} {a : A} (α : Loop n A a) 
                → {B : Type} (C D : A → Type) (h : C a → D a) 
                → Path ((x : _) → Loop→Over' n α C D h x)
                       (LoopOver n α (\ x -> C x → D x) h) 
  Loop→Over One α C D h = ua (improve (hequiv (λ p → {!!}) {!!} {!!} {!!}))
  Loop→Over (S One) α C D h = ua (improve (hequiv (λ p → {!!}) {!!} {!!} {!!}))
  Loop→Over n α C D h = ua (improve (hequiv (λ p → {!!}) {!!} {!!} {!!}))


  {-
   -- ENH: should be derivable from a general rule for LoopOver - - (\x -> A(x) -> B(x)) -
   -- but I can't figure out what that would be
  Loop→PathOver : (n : Positive) {A : Type} {a : A} (α : Loop n A a) 
                → {B : Type} (C : A → Type) (f g : A → B) (h : C a → Path {B} (f a) (g a)) 
                → Path ((x : C a) → 
                         Path{Loop n (Path {B} (f a) (g a)) (h x)} 
                             (ap≃→^ n {!ap^ n (transport (\ x -> ) α)!} {!!})
                             (id^ n))
                       (LoopOver n α (\ x -> C x → f x ≃ g x) h) 
  Loop→PathOver n α C f g h = ua (improve (hequiv (λ p → {!!}) {!!} {!!} {!!}))
  -}
  {-
  Loop→PathOver One α C f g h = ua (improve (hequiv (λ p → {!!}) {!!} {!!} {!!}))
  Loop→PathOver (S n) α C f g h = {!!}
  -}
  {-
  postulate
   LoopΣ : (n : Positive) {A : Type}{B : A → Type}{p : Σ B} →
           (Σ \ (x : Loop n A (fst p)) → LoopOver n x B (snd p))
        ≃ Loop n (Σ B) p
  
  Loop→PathOverD : (n : Positive) {A : Type} {a : A} (α : Loop n A a) 
                → {B : Type} (C : A → Type) (f g : (x : A) → C x → B) (h : (c : C a) → Path {B} (f a c) (g a c)) 
                → Path ((c : C a) (γ : LoopOver n α C c) 
                        → (Path {Loop n B (f a c)} 
                                 (ap^ n (λ (p : Σ C) → f (fst p) (snd p)) (coe (LoopΣ n) (α , γ))) 
                                 ({! (ap^ n (f a)) !} )))
-- (rebase n (! (h c))
--                                     (ap^ n (λ (p : Σ C) → g (fst p) (snd p)) (coe (LoopΣ n) (α , γ))))
--                                   ∘[ n ] 
                       (LoopOver n α (\ x -> (c : C x) → f x c ≃ g x c) h) 
  Loop→PathOverD One α C f g h = {!!} -- ua (improve (hequiv (λ p → {!!}) {!!} {!!} {!!}))
  Loop→PathOverD (S n) α C f g h = {!!}
  -}
  

