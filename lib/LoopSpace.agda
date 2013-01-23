{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open import lib.Prods
open import lib.Int
open Paths
open Int
open import lib.AdjointEquiv
open import lib.Functions
open import lib.Univalence
open import lib.Truncations
open Truncation

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
    {-
    transport-Loop-base One α = λ≃ (λ l →
                                    (transport (λ b → Id b b) α l) ≃〈 {!!} 〉
                                    (α ∘ l ∘ ! α)∎)
    transport-Loop-base (S n) α = λ≃ (λ l →
                           (transport (λ b → Id (id^ n) (id^ n)) α l) ≃〈 {!!} 〉
                           (apd (λ b → id^ n {_} {b}) α ∘ ap (transport (Loop n _) α) l ∘ ! (apd (λ b → id^ n {_} {b}) α)) ≃〈 {!!} 〉
                           (rebase-id n α ∘ ap (rebase n α) l ∘ ! (rebase-id n α))∎)

    apd-id^ : ∀ n {A} {a} (α : Loop (S n) A a) → apd (λ b → id^ n {_} {b}) α ≃ rebase-id n α ∘ ap≃ (transport-Loop-base n α)
    apd-id^ = {!!}
    -}

  postulate 
    rebase-idpath : ∀ n → {A : Type} {a : A} -> rebase n (id{_}{a}) ≃ \ x -> x
    -- follows from transport-Loop-base

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

  !^-invol : ∀ n → ∀ {A a} → (α : Loop n A a) → !^ n (!^ n α) ≃ α
  !^-invol One α = !-invol α
  !^-invol (S n) α = !-invol α

  LoopPathEquiv : ∀ n {A a} 
             → Equiv (Loop (S n) A a) (Loop n (Path a a) id) -- what about for non-id?
  LoopPathEquiv n {A} {α} = improve (hequiv (i n) (e n) β η) where
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

  LoopPath : ∀ n {A a} 
             → (Loop (S n) A a) ≃ (Loop n (Path a a) id) -- what about for non-id?
  LoopPath n {A} {α} = ua (LoopPathEquiv n)

  ap^-ap-assoc : ∀ {A B} → (n : _) → (f : A → B) → {a : A} 
                   (α : Loop n (Path a a) id)
                 → (ap^ n (ap f) α) ≃ coe (LoopPath n) (ap^ (S n) f (coe (! (LoopPath n)) α))
  ap^-ap-assoc One f α = ap (ap f) α ≃〈 ap≃ (! (transport-ua (LoopPathEquiv One))) 〉
                         coe (LoopPath One) (ap (ap f) α) ≃〈 ap (λ α → coe (LoopPath One) (ap (ap f) α)) (! (ap≃ (transport-ua-back {a = LoopPathEquiv One}))) 〉
                         coe (LoopPath One) (ap (ap f) (coe (! (LoopPath One)) α)) ≃〈 ap (coe (LoopPath One)) (! (∘-unit-l (ap (ap f) (coe (! (LoopPath One)) α)))) 〉
                         coe (LoopPath One) (id ∘ ap (ap f) (coe (! (LoopPath One)) α)) ∎
  ap^-ap-assoc (S n) f α = ap^ (S n) (ap f) α ≃〈 {!!} 〉
                           coe (LoopPath (S n)) (ap^-id (S n) f ∘ ({!!} ∘ ap (λ α → coe (! (LoopPath n)) (ap^ n (ap f) (coe (LoopPath n) α))) (coe (! (LoopPath (S n))) α) ∘ {!!}) ∘ ! (ap^-id (S n) f)) ≃〈 {!!} 〉
                           coe (LoopPath (S n)) (ap^-id (S n) f ∘ ap (ap^ (S n) f) (coe (! (LoopPath (S n))) α) ∘ ! (ap^-id (S n) f)) ≃〈 {!!} 〉
                           coe (LoopPath (S n)) (ap^ (S (S n)) f (coe (! (LoopPath (S n))) α)) ∎


  -- abc : ∀ n {A} {a} (α : Loop (S (S n)) A a) → (ap (coe (LoopPath n)) α) ≃ coe (LoopPath (S n)) α
  -- abc = ?

  ap^-S' : ∀ {A B} → (n : _) → (f : A → B) → {a : A} 
                   (α : Loop (S n) A a)
                 → ap^ (S n) f α ≃ coe (! (LoopPath n)) (ap^ n (ap f) (coe (LoopPath n) α))
  ap^-S' One f α = {!!}
  ap^-S' (S n) f α = ap^ (S (S n)) f α ≃〈 {!!} 〉
                     ap^-id (S n) f ∘ ap (ap^ (S n) f) α ∘ ! (ap^-id (S n) f) ≃〈 {!!} 〉
                     ap^-id (S n) f
                       ∘ (! (ap^-S' n f (id^ (S n)))
                         ∘ ap (λ α → coe (! (LoopPath n)) (ap^ n (ap f) (coe (LoopPath n) α))) α
                         ∘ ap^-S' n f (id^ (S n)))
                       ∘ ! (ap^-id (S n) f) ≃〈 {!!} 〉
                     ap^-id (S n) f
                       ∘ (! (ap^-S' n f (id^ (S n)))
                         ∘ (ap (coe (! (LoopPath n)))
                               (ap (ap^ n (ap f))
                                   (ap (coe (LoopPath n)) α)))
                         ∘ ap^-S' n f (id^ (S n)))
                       ∘ ! (ap^-id (S n) f) ≃〈 {!!} 〉
                     -- ap^-id (S n) f
                     --   ∘ (! (ap^-S' n f (id^ (S n)))
                     --     ∘ (ap (coe (! (LoopPath n)))
                     --           ({!!} ∘ {!ap^ (S n) (ap f) (ap (coe (LoopPath n)) α)!} ∘ {!!}))
                     --     -- ∘ (ap (coe (! (LoopPath n)))
                     --     --       (ap (ap^ n (ap f)) (ap (coe (LoopPath n)) α)))
                     --     ∘ ap^-S' n f (id^ (S n)))
                     --   ∘ ! (ap^-id (S n) f) ≃〈 {!!} 〉
                     coe (! (LoopPath (S n))) (ap^-id n (ap f) ∘ ap (ap^ n (ap f)) (coe (LoopPath (S n)) α) ∘ ! (ap^-id n (ap f))) ≃〈 {!!} 〉
                     coe (! (LoopPath (S n))) (ap^ (S n) (ap f) (coe (LoopPath (S n)) α)) ∎
--                 → (ap^ n (ap f) α) ≃ coe (LoopPath n) (ap^ (S n) f (coe (! (LoopPath n)) α))

  ap^-by-equals : ∀ n {A} {B} {f g : A → B} (α : f ≃ g) {a : A} (β : Loop n A a) → ap^ n f β ≃ rebase n (ap≃ (! α)) (ap^ n g β)
  ap^-by-equals n {f = f} id β = ! (ap≃ (rebase-idpath n) {ap^ n f β})

  mutual
    ap^-idfunc : ∀ {A} {a : A} → (n : _) (α : Loop n A a) → ap^ n (\ (x : A) -> x) α ≃ α
    ap^-idfunc One α = ap-id α
    ap^-idfunc (S n) α = ap^ (S n) (λ x → x) α  ≃〈 {!!} 〉
                         coe (! (LoopPath n)) (ap^ n (ap (λ x → x)) (coe (LoopPath n) α)) ≃〈 {!!} 〉
                         coe (! (LoopPath n)) (rebase n (ap≃ (! (λ≃ ap-id))) (ap^ n (λ x → x) (coe (LoopPath n) α))) ≃〈 {!!} 〉
                         coe (! (LoopPath n)) (rebase n (ap≃ (! (λ≃ ap-id))) (coe (LoopPath n) α)) ≃〈 {!!} 〉
                         coe (! (LoopPath n)) (rebase n (! (ap≃ (λ≃ ap-id))) (coe (LoopPath n) α)) ≃〈 {!!} 〉
                         coe (! (LoopPath n)) (rebase n id (coe (LoopPath n) α)) ≃〈 {!!} 〉
                         coe (! (LoopPath n)) (coe (LoopPath n) α) ≃〈 {!!} 〉
                         α ∎
--  ap^-id n (λ x → x) ∘ ap (ap^ n (λ x → x)) α ∘ ! (ap^-id n (λ x → x)) ≃〈 ap (λ x → ap^-id n (λ x' → x') ∘ x ∘ ! (ap^-id n (λ x' → x'))) (ap-by-id{_}{(ap^ n (λ x → x))} (λ x → ! (ap^-idfunc n x)) α) 〉 
                         -- ap^-id n (λ x → x) ∘ (! (ap^-idfunc n (id^ n)) ∘ α ∘ ! (! (ap^-idfunc n (id^ n)))) ∘ ! (ap^-id n (λ x → x)) ≃〈 assoc-131->212 (ap^-id n (λ x → x)) (! (ap^-idfunc n (id^ n))) α (! (! (ap^-idfunc n (id^ n)))) (! (ap^-id n (λ x → x))) 〉 
                         -- (ap^-id n (λ x → x) ∘ (! (ap^-idfunc n (id^ n)))) ∘ α ∘ (! (! (ap^-idfunc n (id^ n))) ∘ ! (ap^-id n (λ x → x))) ≃〈 ap (λ z → (ap^-id n (λ x → x) ∘ ! z) ∘ α ∘ ! (! z) ∘ ! (ap^-id n (λ x → x))) (ap^-idfunc-id n) 〉 
                         -- (ap^-id n (λ x → x) ∘ ! (ap^-id n (\ x -> x))) ∘ α ∘ (! (! (ap^-id n (λ x → x))) ∘ ! (ap^-id n (λ x → x))) ≃〈 ap (λ x → x ∘ α ∘ ! (! (ap^-id n (λ x' → x'))) ∘ ! (ap^-id n (λ x' → x'))) (!-inv-r (ap^-id n (λ x → x))) 〉 
                         -- id ∘ α ∘ (! (! (ap^-id n (\ x -> x))) ∘ ! (ap^-id n (λ x → x))) ≃〈 ∘-unit-l (α ∘ ! (! (ap^-id n (λ x → x))) ∘ ! (ap^-id n (λ x → x))) 〉 
                         -- α ∘ (! (! (ap^-id n (\ x -> x))) ∘ ! (ap^-id n (λ x → x))) ≃〈 ap (λ x → α ∘ x) (!-inv-l (! (ap^-id n (λ x → x)))) 〉 
                         -- α ∎

    -- ap^-idfunc-id : ∀ {A} {a : A} → (n : _) → ap^-idfunc{A}{a} n (id^ n) ≃ ap^-id n (λ x → x)
    -- ap^-idfunc-id One = id
    -- ap^-idfunc-id{A}{a} (S n) = {!  !} -- not gonna work... 

  ap^-! : ∀ n → ∀ {A B} {a : A} → (f : A → B) → (α : Loop n A a)
        → ap^ n f (!^ n α) ≃ !^ n (ap^ n f α)
  ap^-! One f α = ap-! f α
  ap^-! (S n) f α = ! (! (ap^-id n f ∘ ap (ap^ n f) α ∘ ! (ap^-id n f)) ≃〈 !-∘3 (ap^-id n f)  (ap (ap^ n f) α) (! (ap^-id n f)) 〉
                       (! (! (ap^-id n f)) ∘ ! (ap (ap^ n f) α) ∘ ! (ap^-id n f)) ≃〈 ap (λ x → ! (! (ap^-id n f)) ∘ x ∘ ! (ap^-id n f)) (! (ap-! (ap^ n f) α)) 〉 
                       (! (! (ap^-id n f)) ∘ (ap (ap^ n f) (! α)) ∘ ! (ap^-id n f)) ≃〈 ap (λ x → x ∘ ap (ap^ n f) (! α) ∘ ! (ap^-id n f)) (!-invol (ap^-id n f)) 〉 
                       (ap^-id n f ∘ ap (ap^ n f) (! α) ∘ ! (ap^-id n f) ∎))
  
  postulate
    ap^-o : ∀ {A B C} → (n : _) → (g : B → C) (f : A → B)
          → {a : A} (α : Loop n A a)
          → ap^ n (g o f) α ≃ ap^ n g (ap^ n f α) 
{-
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

  λl : ∀ n → ∀ {A} {B : A → Type} {f : _} → 
          ((x : A) → Loop n (B x) (f x))
       -> (Loop n ((x : A) -> B x) f)
  λl n h = coe (LoopΠ n) h

  apl : ∀ n → ∀ {A} {B : A → Type} {f : _} → 
          (Loop n ((x : A) -> B x) f)
       -> ((x : A) → Loop n (B x) (f x))
  apl n h = coe (! (LoopΠ n)) h


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

  postulate
    LoopSType : ∀ n {A} -> ((a : A) -> Loop n A a) ≃ (Loop (S n) Type A)
  {-
  LoopSType n = (! (LoopPath{n})) ∘ 
                ua (improve (hequiv (λ h → {! (coe (Loop→ n) h) !})
                                    (λ α y → (ap^ n (λ x → coe x y) α))
                                    {!!}
                                    {!!}))
  -}

  apt : ∀ n {A} -> Loop (S n) Type A → ((a : A) -> Loop n A a)
  apt n l a = coe (! (LoopSType n)) l a

  postulate
    apt-def : ∀ n {A} -> (l : Loop (S n) Type A) → (a : A) 
            → apt n l a ≃ ap^ n (\ x -> coe x a) (coe (LoopPath n) l) 


  λt : ∀ n {A} -> ((a : A) -> Loop n A a) -> Loop (S n) Type A
  λt n l = coe (LoopSType n) l

  postulate
    apt-! : ∀ n {A} -> (α : Loop (S n) Type A) (a : _) →
              apt n (!^ (S n) α) a
            ≃ !^ n (apt n α a)

  add-!-≃ : ∀ {A} {M : A} (p : Path M M) → (! p ≃ id) ≃ (p ≃ id)
  add-!-≃ {A} {M} p = ua (improve (hequiv (λ α → ap ! α ∘ ! (!-invol p))
                                            (λ β → ap ! β) 
                                            (λ x → ap ! (ap ! x ∘ ! (!-invol p)) ≃〈 {!!} 〉
                                                   ap ! (ap ! x) ∘ ap ! (! (!-invol p)) ≃〈 {!!} 〉 
                                                   ap (! o !) x ∘ ap ! (! (!-invol p)) ≃〈 ap (λ y → y ∘ ap ! (! (!-invol p))) (ap-by-id (λ x' → ! (!-invol x')) x) 〉 
                                                   (! (!-invol id) ∘ x ∘ ! (! (!-invol (! p)))) ∘ ap ! (! (!-invol p)) ≃〈 {!! (!-invol id)!} 〉 
                                                   (id ∘ x ∘ ! (! (!-invol (! p)))) ∘ ap ! (! (!-invol p)) ≃〈 {!!} 〉 
                                                   (x ∘ ! (! (!-invol (! p)))) ∘ ap ! (! (!-invol p)) ≃〈 {!!} 〉 
                                                   (x ∘ (! (! (!-invol (! p))) ∘ ap ! (! (!-invol p)))) ≃〈 ap (λ y → x ∘ y ∘ ap ! (! (!-invol p))) coh 〉 
                                                   (x ∘ (! (ap ! (! (!-invol p))) ∘ ap ! (! (!-invol p)))) ≃〈 ap (λ y → x ∘ y) (!-inv-l (ap ! (! (!-invol p)))) 〉 
                                                   (x ∎))
                                            {!probably similar!})) where
          coh : ∀ {A} {M N : A} {p : Path M N} → ! (! (!-invol (! p))) ≃ ! (ap ! (! (!-invol p)))
          coh {p = id} = id

  LoopOverS :  (n : Positive) {A : Type} {a : A} (α : Loop (S n) A a) 
             → (B : A -> Type) (b : B a) → Type
  LoopOverS n {A}{a} α B b = 
    Path{Loop n (B a) b} 
        (apt n (ap^ (S n) B α) b)
        (id^ n)

  LoopOver-is-S : (n : Positive) {A : Type} {a : A} (α : Loop (S n) A a) → (B : A -> Type) (b : B a) 
                  → LoopOver (S n) α B b ≃ LoopOverS n α B b 
  LoopOver-is-S One α B b = add-!-≃
                              (apt One (id ∘ ap (λ l → ap B l) α) b)
                              ∘ ap (λ x → Id x id) 
                                   (transport (λ x → Id (transport B x b) b) α id ≃〈 {!!} 〉
                                    ap (\_ -> b) α ∘ id ∘ ! (ap (\ x -> transport B x b) α) ≃〈 {!!} 〉 
                                    id ∘ id ∘ ! (ap (\ x -> transport B x b) α) ≃〈 {!!} 〉 
                                    ! (ap (\ x -> transport B x b) α) ≃〈 {!!} 〉
                                    ! (ap (\ x -> coe (ap B x) b) α) ≃〈 {!!} 〉  
                                    ! (ap (\ x -> coe x b) (ap (ap B) α)) ≃〈 {!!} 〉 
                                    ! (ap (\ x -> coe x b) (coe (LoopPath One) (ap (ap B) α))) ≃〈 id 〉 
                                    ! (ap^ One (\ x -> coe x b) (coe (LoopPath One) (ap (ap B) α))) ≃〈 {!!} 〉 
                                    ! ((apt One (ap (ap B) α) b)) ≃〈 {!!} 〉 
                                    (! (apt One (id ∘ ap (ap B) α) b) ∎))
  LoopOver-is-S (S n) α B b = {!!} 

  LoopType→ : ∀ n {A B} → (Loop (S n) Type A) -> Loop (S n) Type B -> Loop (S n) Type (A → B)
  LoopType→ n {A} {B} lA lB = λt n (λ (f : A → B) →
                                      λl n (λ (x : A) →
                                              ∘^ n (apt n lB (f x)) 
                                                   (ap^ n f (apt n (!^ (S n) lA) x))))

  postulate
    ap^→ : ∀ {A} → (n : _) → (C D : A → Type) → {base : A} {α : Loop (S n) A base} →
           ap^ (S n) (\ x -> C x → D x) α 
         ≃ LoopType→ n (ap^ (S n) C α) (ap^ (S n) D α)

  postulate
   Loop→OverS : (n : Positive) {A : Type} {a : A} (α : Loop (S n) A a) 
              → {B C : A → Type} (f : B a → C a)
              →   Path {Loop n (B a → C a) f}
                    (λl n
                     (λ x →
                        ∘^ n (apt n (ap^ (S n) C α) (f x))
                             (ap^ n f (apt n (!^ (S n) (ap^ (S n) B α)) x))))
                    (λl n (λ x → id^ n))
                ≃ (LoopOver (S n) α (\ x -> B x → C x) f)

  -- postulate
  --   ap^Loop : ∀ n k {A} {a : A} (α : Loop (S n) A a) → ap^ (S n) (λ x → Loop k A x) α ≃ λt n (λ x → rebase n (ap≃ (rebase-idpath k)) (ap^ n (λ p → rebase k p x) (coe (LoopPath {n}) α)))
--  ap^Loop n k α = {!!}
  {-
  Loop→OverS n {A} {a} α {B}{C} f = 
    ! ((LoopOver (S n) α (\ x -> B x → C x) f) ≃〈 {!!} 〉 
       LoopOverS n α (\ x -> B x → C x) f ≃〈 id 〉 
       Path{Loop n (B a → C a) f} 
           (apt n (ap^ (S n) (\ x → B x → C x) α) f)
           (id^ n) ≃〈 {!!} 〉 
       Path{Loop n (B a → C a) f} 
           (apt n (LoopType→ n (ap^ (S n) B α) (ap^ (S n) C α)) f)
           (id^ n) ≃〈 {!!} 〉 
       Path{Loop n (B a → C a) f} 
           (λl n (λ x → ∘^ n (apt n (ap^ (S n) C α) (f x)) 
                            (ap^ n f (apt n (!^ (S n) (ap^ (S n) B α)) x))))
           (id^ n) ≃〈 eta 〉 
       Path{Loop n (B a → C a) f} 
           (λl n (λ x → ∘^ n (apt n (ap^ (S n) C α) (f x)) 
                            (ap^ n f (apt n (!^ (S n) (ap^ (S n) B α)) x))))
           (λl (\ _ -> id^ n))
    ∎)
  -}

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

  postulate
    HSet-Loop : ∀ n {A} {a} → IsTrunc (tlp n) A → HSet (Loop n A a)

    IsTrunc-LoopOver : ∀ n k {A} {a} (α : Loop n A a) {B} {b} → ((x : A) → IsTrunc (S k) (B x)) → IsTrunc k (LoopOver n α B b)

    IsNTrunc-Loop : ∀ n {A a} -> IsTrunc (tlp n) A → IsTrunc (tlp n) (Loop n A a)
  



  -- FIXME: should be able to derive these compositionally from a rule for 
  -- truncation and a rule for Path in general

  -- intended to to be "α ∘ β"
  LoopTypeTruncPathPost : ∀ n {A} {a : A} (α : Loop (S n) A a) (a0 : A) 
                   → Loop (S n) Type (Trunc (tlp n)(Path{A} a0 a))
  LoopTypeTruncPathPost n α a0 = λt n (Trunc-elim (λ tβ → Loop n (Trunc (tlp n) (Path a0 _)) tβ) 
                                                  (λ _ → IsNTrunc-Loop n Trunc-is) 
                                                  (λ β → ap^ n [_]
                                                        (rebase n (∘-unit-l β)
                                                           (ap^ n (λ x → x ∘ β) (coe (LoopPath n) α)))))

  postulate
    ap^TruncPathPost : ∀ n {A} {a : A} (α : Loop (S n) A a) (a0 : A)
                → 
                Path{Loop (S n) Type (Trunc (tlp n) (Path{A} a0 a))}
                    (ap^ (S n) (\ x -> Trunc (tlp n) (Path a0 x)) α)
                    (LoopTypeTruncPathPost n α a0)

  postulate -- transport plus inverses
   ∘^-inv-l≃ : ∀ n {A} {a : A} {α β : Loop n A a} -> 
                 α ≃ !^ n β -> (∘^ n α β) ≃ id^ n

