
{-# OPTIONS --type-in-type #-}

open import lib.First
open import lib.Paths
open Paths
open import lib.Functions
open import lib.Int
open Int
open import lib.AdjointEquiv
open import lib.Univalence
open import lib.Truncations
open Truncation
open import lib.WrappedPath

open import lib.loopspace.Basics

module lib.loopspace.Groupoid where

  -- need this for paths between loops, not just paths between paths
  adj-eq-loop : ∀ n {A}{a : A} {ins outs : Loop n A a} 
          → (wrapper : Path ins outs) (middle : Path ins ins)
          → (wrapper' : Path ins outs) (middle' : Path ins ins)
          → middle ≃ middle'  
          → adj wrapper middle ≃ adj wrapper' middle'
  adj-eq-loop One w m w' m' α = adj-eq w m w' m' α
  adj-eq-loop (S n) w m w' m' α = adj-eq w m w' m' α

  -- groupoid structure

  ∘^ : ∀ n {A a} → Loop n A a → Loop n A a → Loop n A a
  ∘^ One p q = p ∘ q
  ∘^ (S n) p q = p ∘ q

  infixr 10 ∘^

  !^ : ∀ n → ∀ {A a} → Loop n A a → Loop n A a 
  !^ One q = ! q
  !^ (S n) q = ! q


  -- basic groupoid properties;
  -- mostly we just use properties of ∘ ! etc after unfolding,
  -- but sometimes it's useful to use them at arbitrary n.
  -- add as needed.

  !^-inv-l : ∀ n {A} {a : A} (α : Loop n A a) -> 
           (∘^ n (!^ n α) α) ≃ id^ n  
  !^-inv-l One α = !-inv-l α
  !^-inv-l (S n) α = !-inv-l α

  !^-inv-l≃ : ∀ n {A} {a : A} {α β : Loop n A a} -> 
            α ≃ !^ n β -> (∘^ n α β) ≃ id^ n
  !^-inv-l≃ n {β = β} p = transport (λ x → ∘^ n x β ≃ id^ n) (! p) (!^-inv-l n β)

  !^-invol : ∀ n → ∀ {A a} → (α : Loop n A a) → !^ n (!^ n α) ≃ α
  !^-invol One α = !-invol α
  !^-invol (S n) α = !-invol α

 
  -- action of transporting at Loop n A -

  mutual
    rebase : ∀ n → ∀ {A a a'} (α : a ≃ a') -> Loop n A a → Loop n A a'
    rebase One α l = α ∘ l ∘ ! α
    rebase (S n) α l = adjust (rebase-id n α) (ap (rebase n α) l)
    
    rebase-id : ∀ n → ∀ {A} {a a' : A} (α : a ≃ a') -> rebase n α (id^ n) ≃ id^ n
    rebase-id One α = !-inv-with-middle-r α id
    rebase-id (S n) α = !-inv-with-middle-r (rebase-id n α) id

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

  rebase-idpath : ∀ n → {A : Type} {a : A} -> rebase n (id{_}{a}) ≃ \ x -> x
  rebase-idpath n = λ≃ (\ x -> ! (ap≃ (transport-Loop-base n id)))


  -- associate Ω^(n+1) as Ω^(Ω^n)
  -- instead of (Ω^n(Ω)), which is what you get by unfolding;
  -- useful for below

  module LoopPathEquiv {A : _} {a : A} where
     mutual
      i : ∀ n → Loop (S n) A a → Loop n (Path a a) id
      i One l = l
      i (S n) l = adjust (i-id n) (ap (i n) l)
  
      i-id : ∀ n → i n id ≃ id^ n
      i-id One = id
      i-id (S n) = !-inv-with-middle-r (i-id n) id
  
     mutual
      e : ∀ n → Loop n (Path a a) id → Loop (S n) A a
      e One l = l
      e (S n) l = adjust (e-id n) (ap (e n) l)
  
      e-id : ∀ n  → e n (id^ n) ≃ id
      e-id One = id
      e-id (S n) = !-inv-with-middle-r (e-id n) id
  
     postulate 
       β : ∀ n x → e n (i n x) ≃ x
       η : ∀ n x → i n (e n x) ≃ x

     Eq : ∀ n → Equiv (Loop (S n) A a) (Loop n (Path a a) id) 
     Eq n = improve (hequiv (i n) (e n) (β n) (η n)) 

  LoopPath : ∀ n {A a} 
             → (Loop (S n) A a) ≃ (Loop n (Path a a) id) -- what about for non-id?
  LoopPath n {A} {α} = ua (LoopPathEquiv.Eq n)

  loopSN1 : ∀ n {A a} -> (Loop (S n) A a) → (Loop n (Path a a) id)
  loopSN1 n = coe (LoopPath n)

  loopN1S : ∀ n {A a} -> (Loop n (Path a a) id) → (Loop (S n) A a) 
  loopN1S n = coe (! (LoopPath n))

  abstract 
    -- these are useful because loopSN1 (S n) does not directly compute to adjust - -, or
    -- else we could just use adj-def instead of these specialized ones
    -- but since we need lemmas anyway... 
    loopSN1-S : ∀ n {A a} (α : (Loop (S (S n)) A a)) →
                  loopSN1 (S n) α 
                ≃ adj (LoopPathEquiv.i-id n ∘ ap≃ (transport-ua (LoopPathEquiv.Eq n)))
                      (ap (loopSN1 n) α)
    loopSN1-S n α = loopSN1 (S n) α ≃〈 ap≃ (transport-ua (LoopPathEquiv.Eq (S n))) 〉 
                    adjust (LoopPathEquiv.i-id n) (ap (LoopPathEquiv.i n) α) ≃〈 ! (adj-def (LoopPathEquiv.i-id n) _) 〉 
                    adj    (LoopPathEquiv.i-id n) (ap (LoopPathEquiv.i n) α) ≃〈 adj-bind (ap-loop-by-equals{f = (LoopPathEquiv.i n)}{g = (loopSN1 n)}   (λ x → ap≃ (transport-ua (LoopPathEquiv.Eq n))) α) 〉 
                    adj (LoopPathEquiv.i-id n ∘ ap≃ (transport-ua (LoopPathEquiv.Eq n)))
                      (ap (loopSN1 n) α) ∎

    loopN1S-S : ∀ n {A a} (α : (Loop (S n) (Path{A} a a) id)) →
                  loopN1S (S n) α 
                ≃ adj (LoopPathEquiv.e-id n ∘ ap≃ (transport-ua-back (LoopPathEquiv.Eq n)))
                      (ap (loopN1S n) α)
    loopN1S-S n α = loopN1S (S n) α ≃〈 ap≃ (transport-ua-back (LoopPathEquiv.Eq (S n))) 〉 
                    adjust (LoopPathEquiv.e-id n) (ap (LoopPathEquiv.e n) α) ≃〈 ! (adj-def (LoopPathEquiv.e-id n) _) 〉 
                    adj    (LoopPathEquiv.e-id n) (ap (LoopPathEquiv.e n) α) ≃〈 adj-bind (ap-loop-by-equals{f = (LoopPathEquiv.e n)}{g = (loopN1S n)}   (λ x → ap≃ (transport-ua-back (LoopPathEquiv.Eq n))) α) 〉 
                    adj (LoopPathEquiv.e-id n ∘ ap≃ (transport-ua-back (LoopPathEquiv.Eq n)))
                      (ap (loopN1S n) α) ∎


  -- properties of n-functors

  abstract
    ap^-S' : ∀ {A B} → (n : _) → (f : A → B) → {a : A} 
                    (α : Loop (S n) A a)
                  → ap^ (S n) f α ≃ loopN1S n (ap^ n (ap f) (loopSN1 n α))
    ap^-S' One f α = ap^ (S One) f α ≃〈 ! (adj-def (ap^-id One f) _) 〉
                     adj _ (ap (ap f) α) ≃〈 adj-eq _ _ _ _ id 〉 
                     adj _ (ap (ap f) α) ≃〈 ! (adj-id _) 〉 
                     (ap (ap f) α) ≃〈 ap (ap (ap f)) (! (ap≃ (transport-ua (LoopPathEquiv.Eq One)) {α})) 〉 
                     (ap (ap f) (loopSN1 One α)) ≃〈 id 〉 
                     (ap^ One (ap f) (loopSN1 One α)) ≃〈 ! (ap≃ (transport-ua-back (LoopPathEquiv.Eq One))) 〉 
                     (loopN1S One (ap^ One (ap f) (loopSN1 One α)) ∎)
    ap^-S' (S n) f α = ap^ (S (S n)) f α ≃〈 ! (adj-def (ap^-id (S n) f) _) 〉 
                        -- note : could avoid having to mention (ap^-id ...) by defining
                        -- ap^ with adj, but then we'd lose definitional behavior, so this seems better
                       adj _ (ap (ap^ (S n) f) α)                                       ≃〈 adj-bind (ap-loop-by-equals (λ x → ! (ap^-S' n f x)) α) 〉
                       adj _ (ap (\ α' -> loopN1S n (ap^ n (ap f) (loopSN1 n α'))) α)   ≃〈 ap (adj _) (ap-o (loopN1S n) (λ α' → ap^ n (ap f) (loopSN1 n α')) α) 〉
                       adj _ (ap (loopN1S n) (ap (λ α → ap^ n (ap f) (loopSN1 n α)) α)) ≃〈 ap (adj _ o (ap (loopN1S n))) (ap-o (ap^ n (ap f)) (loopSN1 n) α) 〉
                       adj _ (ap (loopN1S n) (ap (ap^ n (ap f)) (ap (loopSN1 n) α)))    ≃〈 adj-eq _ _ _ _ id 〉
                       adj _ (ap (loopN1S n) (ap (ap^ n (ap f)) (ap (loopSN1 n) α)))    ≃〈 ! (adj-bind (ap-adj (loopN1S n) _ _)) 〉
                       adj _ (ap (loopN1S n) (adj _ (ap (ap^ n (ap f)) (ap (loopSN1 n) α)))) ≃〈 ap (adj _) (ap (\ x -> ap (loopN1S n) x) (! (ap-adj (ap^ n (ap f)) _ _)))  〉
                       adj _ (ap (loopN1S n) (ap (ap^ n (ap f)) (adj _ (ap (loopSN1 n) α)))) ≃〈 ap (adj _) (ap (\ x -> ap (loopN1S n) (ap (ap^ n (ap f)) x)) (! (loopSN1-S n α)))  〉
                                                                                               -- agda has trouble with the (adj _)'s when they occur under a binder
                       adj _ (ap (loopN1S n) (ap (ap^ n (ap f)) (loopSN1 (S n) α))) ≃〈 ! (adj-bind (ap-adj (loopN1S n) _ _))  〉
                       adj _ (ap (loopN1S n) (adj _ (ap (ap^ n (ap f)) (loopSN1 (S n) α)))) ≃〈 ap (adj _ o (ap (loopN1S n))) (adj-def (ap^-id n (ap f)) _)  〉
                       adj _ (ap (loopN1S n) (ap^ (S n) (ap f) (loopSN1 (S n) α)))  ≃〈 ! (loopN1S-S n (ap^ (S n) (ap f) (loopSN1 (S n) α))) 〉 
                       loopN1S (S n) (ap^ (S n) (ap f) (loopSN1 (S n) α)) ∎
    
    -- ap^-S' with coercions moved around
    ap^-ap-assoc : ∀ {A B} → (n : _) → (f : A → B) → {a : A} 
                    (α : Loop n (Path a a) id)
                 → (ap^ n (ap f) α) ≃ loopSN1 n (ap^ (S n) f (loopN1S n α))
    ap^-ap-assoc n f α = 
                       ! (ap (loopSN1 n) (ap^-S' n f (loopN1S n α))) 
                     ∘ ap (λ x → loopSN1 n (loopN1S n (ap^ n (ap f) x))) (! (coe-inv-2 (ua (LoopPathEquiv.Eq n))))
                     ∘ ! (coe-inv-2 (ua (LoopPathEquiv.Eq n)))
    
    ap^-by-equals : ∀ n {A} {B} {f g : A → B} (α : f ≃ g) {a : A} (β : Loop n A a) 
                  → ap^ n f β ≃ rebase n (ap≃ (! α)) (ap^ n g β)
    ap^-by-equals n {f = f} id β = ! (ap≃ (rebase-idpath n) {ap^ n f β})
    
    ap^-idfunc : ∀ {A} {a : A} → (n : _) (α : Loop n A a) → ap^ n (\ (x : A) -> x) α ≃ α
    ap^-idfunc One α = ap-id α
    ap^-idfunc (S n) α = ap^ (S n) (λ x → x) α  ≃〈 ap^-S' n (λ x → x) α 〉
                         loopN1S n (ap^ n (ap (λ x → x)) (loopSN1 n α)) ≃〈 ap (loopN1S n) (ap^-by-equals n (λ≃ ap-id) (loopSN1 n α)) 〉
                         loopN1S n (rebase n (ap≃ (! (λ≃ ap-id))) (ap^ n (λ x → x) (loopSN1 n α))) ≃〈 ap (loopN1S n o rebase n (ap≃ (! (λ≃ ap-id)))) (ap^-idfunc n _) 〉
                         loopN1S n (rebase n (ap≃ (! (λ≃ ap-id))) (loopSN1 n α)) ≃〈 ap (λ x → loopN1S n (rebase n x (loopSN1 n α))) (ap-! (\ f -> f id) (λ≃ ap-id)) 〉
                         loopN1S n (rebase n (! (ap≃ (λ≃ ap-id))) (loopSN1 n α)) ≃〈 ap (λ x → loopN1S n (rebase n (! x) (loopSN1 n α))) (Π≃β ap-id) 〉
                         loopN1S n (rebase n id (loopSN1 n α)) ≃〈 ap (loopN1S n) (ap≃ (rebase-idpath n)) 〉
                         loopN1S n (loopSN1 n α) ≃〈 coe-inv-1 (ua (LoopPathEquiv.Eq n)) 〉
                         α ∎
    
    ap^-! : ∀ n → ∀ {A B} {a : A} → (f : A → B) → (α : Loop n A a)
          → ap^ n f (!^ n α) ≃ !^ n (ap^ n f α)
    ap^-! One f α = ap-! f α
    ap^-! (S n) f α = ap^ (S n) f (!^ (S n) α) ≃〈 ! (adj-def (ap^-id n f) _) 〉 
                     adj _ (ap (ap^ n f) (! α)) ≃〈 ap (adj _) (ap-! (ap^ n f) α) 〉 
                     adj _ (! (ap (ap^ n f) α)) ≃〈 adj-! _ (ap (ap^ n f) α) 〉 
                     (! (adj _ (ap (ap^ n f) α))) ≃〈 ap ! (adj-def (ap^-id n f) _) 〉 
                     !^ (S n) (ap^ (S n) f α) ∎ 

    ap^-o : ∀ {A B C} → (n : _) → (g : B → C) (f : A → B)
          → {a : A} (α : Loop n A a)
          → ap^ n (g o f) α ≃ ap^ n g (ap^ n f α) 
    ap^-o One g f α = ap-o g f α
    ap^-o (S n) g f α = ap^ (S n) (g o f) α ≃〈 ! (adj-def (ap^-id n (g o f)) _) 〉
                        adj _ (ap (ap^ n (g o f)) α) ≃〈 adj-bind (ap-loop-by-equals {f = ap^ n (g o f)} {g = ap^ n g o ap^ n f} (λ x → ! (ap^-o n g f x)) _) 〉 
                        adj _ (ap (ap^ n g o ap^ n f) α) ≃〈 ap (adj _) (ap-o (ap^ n g) (ap^ n f) _) 〉 
                        adj _ (ap (ap^ n g) (ap (ap^ n f) α)) ≃〈 adj-eq-loop n _ _ _ _ id 〉 
                        adj _ (ap (ap^ n g) (ap (ap^ n f) α)) ≃〈 ! (adj-bind (ap-adj (ap^ n g) _ _)) 〉 
                        adj _ (ap (ap^ n g) (adj _ (ap  (ap^ n f) α))) ≃〈 ap (adj _ o (ap (ap^ n g))) (adj-def (ap^-id n f) _) 〉 
                        adj _ (ap (ap^ n g) (ap^ (S n) f α)) ≃〈 (adj-def (ap^-id n g) _) 〉 
                        ap^ (S n) g (ap^ (S n) f α) ∎
