
{-# OPTIONS --type-in-type --without-K #-}

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

  -- associate Ω^(n+1) as Ω^(Ω^n)
  -- instead of (Ω^n(Ω)), which is what you get by unfolding;
  -- useful for below

  module LoopPath {A : _} {a : A} where

     mutual
      loopSN1 : ∀ n → Loop (S n) A a → Loop n (Path a a) id
      loopSN1 One l = l
      loopSN1 (S n) l = adjust (loopSN1-id n) (ap (loopSN1 n) l)
  
      loopSN1-id : ∀ n → loopSN1 n id ≃ id^ n
      loopSN1-id One = id
      loopSN1-id (S n) = !-inv-with-middle-r (loopSN1-id n) id
  
     mutual
      loopN1S : ∀ n → Loop n (Path a a) id → Loop (S n) A a
      loopN1S One l = l
      loopN1S (S n) l = adjust (loopN1S-id n) (ap (loopN1S n) l)
  
      loopN1S-id : ∀ n  → loopN1S n (id^ n) ≃ id
      loopN1S-id One = id
      loopN1S-id (S n) = !-inv-with-middle-r (loopN1S-id n) id
  
      -- ENH use adjust to simplify the first couple of steps visually
      β : ∀ n x → loopN1S n (loopSN1 n x) ≃ x
      β One x = id
      β (S n) x = (loopN1S-id n ∘ ap (loopN1S n) (loopSN1-id n ∘ ap (loopSN1 n) x ∘ ! (loopSN1-id n)) ∘ ! (loopN1S-id n)) ≃〈 ! (ap (λ α → loopN1S-id n ∘ ap (loopN1S n) α ∘ ! (loopN1S-id n)) (adj-def (loopSN1-id n) _)) 〉
                  (loopN1S-id n ∘ ap (loopN1S n) (adj _ (ap (loopSN1 n) x)) ∘ ! (loopN1S-id n)) ≃〈 ! (adj-def (loopN1S-id n) _) 〉
                  adj _ (ap (loopN1S n) (adj _ (ap (loopSN1 n) x))) ≃〈 adj-bind (ap-adj (loopN1S n) _ _) 〉
                  adj _ (ap (loopN1S n) (ap (loopSN1 n) x)) ≃〈 ! (ap (adj _) (ap-o (loopN1S n) (loopSN1 n) x)) 〉
                  adj _ (ap ((loopN1S n) o (loopSN1 n)) x) ≃〈 adj-bind (ap-loop-by-equals {f = (loopN1S n) o (loopSN1 n)} {g = λ x → x} (λ x → ! (β n x)) x) 〉
                  adj _ (ap (λ x → x) x) ≃〈 ap (adj _) (ap-id x) 〉
                  adj _ x ≃〈 adj-eq _ _ _ _ id 〉
                  adj id x ≃〈 ! (adj-id x) 〉
                  x ∎

      η : ∀ n x → loopSN1 n (loopN1S n x) ≃ x
      η One x = id
      η (S n) x = (loopSN1-id n ∘ ap (loopSN1 n) (loopN1S-id n ∘ ap (loopN1S n) x ∘ ! (loopN1S-id n)) ∘ ! (loopSN1-id n)) ≃〈 ! (ap (λ α → loopSN1-id n ∘ ap (loopSN1 n) α ∘ ! (loopSN1-id n)) (adj-def (loopN1S-id n) _)) 〉
                  (loopSN1-id n ∘ ap (loopSN1 n) (adj _ (ap (loopN1S n) x)) ∘ ! (loopSN1-id n)) ≃〈 ! (adj-def (loopSN1-id n) _) 〉
                  adj _ (ap (loopSN1 n) (adj _ (ap (loopN1S n) x))) ≃〈 adj-bind (ap-adj (loopSN1 n) _ _) 〉
                  adj _ (ap (loopSN1 n) (ap (loopN1S n) x)) ≃〈 ! (ap (adj _) (ap-o (loopSN1 n) (loopN1S n) x)) 〉
                  adj _ (ap ((loopSN1 n) o (loopN1S n)) x) ≃〈 adj-bind (ap-loop-by-equals {f = (loopSN1 n) o (loopN1S n)} {g = λ x → x} (λ x → ! (η n x)) x) 〉
                  adj _ (ap (λ x → x) x) ≃〈 ap (adj _) (ap-id x) 〉
                  adj _ x ≃〈 adj-eq-loop n _ _ _ _ id 〉
                  adj id x ≃〈 ! (adj-id x) 〉
                  x ∎

     eqv : ∀ n → Equiv (Loop (S n) A a) (Loop n (Path a a) id) 
     eqv n = improve (hequiv (loopSN1 n) (loopN1S n) (β n) (η n)) 

     path : ∀ n → (Loop (S n) A a) ≃ (Loop n (Path a a) id) -- what about for non-id?
     path n = ua (eqv n)

  open LoopPath public using (loopN1S ; loopSN1)

  loopSN1-id : ∀ n {A : Type} (a : A) → loopSN1 n id ≃ id^ n {_} {id {_} {a}}
  loopSN1-id One a = id
  loopSN1-id (S n) a = !-inv-with-middle-r (LoopPath.loopSN1-id n) id

  loopSN1-! : ∀ n{A}{a} → (a : Loop (S n) A a) → loopSN1 n (! a) ≃ !^ n (loopSN1 n a)
  loopSN1-! One a' = id
  loopSN1-! (S n) a' = loopSN1 (S n) (! a') ≃〈 id 〉 
                       adjust (LoopPath.loopSN1-id n) (ap (loopSN1 n) (! a')) ≃〈 ! (adj-def (LoopPath.loopSN1-id n) _) 〉
                       adj _ (ap (loopSN1 n) (! a')) ≃〈 ap (adj _) (ap-! (loopSN1 n) _) 〉
                       adj _ (! (ap (loopSN1 n) a')) ≃〈 adj-! _ _ 〉
                       ! (adj _ (ap (loopSN1 n) a')) ≃〈 ap ! (adj-def (LoopPath.loopSN1-id n) _) 〉
                       (! (loopSN1 (S n) a') ∎)

   
  -- action of transporting at Loop n A -

  mutual
    rebase : ∀ n → ∀ {A a a'} (α : a ≃ a') -> Loop n A a → Loop n A a'
    rebase One α l = α ∘ l ∘ ! α
    rebase (S n) α l = adjust (rebase-id n α) (ap (rebase n α) l)

    rebase-id : ∀ n → ∀ {A} {a a' : A} (α : a ≃ a') -> rebase n α (id^ n) ≃ id^ n
    rebase-id One α = !-inv-with-middle-r α id
    rebase-id (S n) α = !-inv-with-middle-r (rebase-id n α) id
  
  rebase-idpath : ∀ n → {A : Type} {a : A} -> rebase n (id{_}{a}) ≃ \ x -> x
  rebase-idpath One = λ≃ (λ x → ∘-unit-l x)
  rebase-idpath (S n) = λ≃ (λ x → (rebase-id n id ∘ ap (rebase n id) x ∘ ! (rebase-id n id)) ≃〈 ! (adj-def (rebase-id n id) _) 〉
                                  adj _ (ap (rebase n id) x) ≃〈 adj-bind (ap-loop-by-equals {f = rebase n id} {g = λ x → x} (λ _ → ap≃ (! (rebase-idpath n))) x) 〉
                                  adj _ (ap (λ x → x) x) ≃〈 ap (adj _) (ap-id x) 〉
                                  adj _ x ≃〈 adj-eq-loop n _ _ _ _ id 〉
                                  adj id x ≃〈 ! (adj-id x) 〉
                                  x ∎)

  -- should be true but didn't end up needing it
  -- rebase-S' : ∀ n {A a a'} (α : a ≃ a') (l : Loop (S n) A a) → rebase (S n) α l ≃ loopN1S n (rebase n (!-inv-with-middle-r α id) (ap^ n (λ β → α ∘ β ∘ ! α) (loopSN1 n l)))

  transport-Loop-base : ∀ n → ∀ {A a a'} (α : a ≃ a') →
                        transport (Loop n A) α ≃ rebase n α
  transport-Loop-base n id = ! (rebase-idpath n)

  -- properties of n-functors

  abstract
    ap^-S' : ∀ {A B} → (n : _) → (f : A → B) → {a : A} 
                    (α : Loop (S n) A a)
                  → ap^ (S n) f α ≃ loopN1S n (ap^ n (ap f) (loopSN1 n α))
    ap^-S' One f α = ap^ (S One) f α ≃〈 ! (adj-def (ap^-id One f) _) 〉
                     adj _ (ap (ap f) α) ≃〈 adj-eq _ _ _ _ id 〉 
                     adj _ (ap (ap f) α) ≃〈 ! (adj-id _) 〉 
                     (ap (ap f) α) ≃〈 id 〉 
                     (ap (ap f) (loopSN1 One α)) ≃〈 id 〉 
                     (ap^ One (ap f) (loopSN1 One α)) ≃〈 id 〉 
                     (loopN1S One (ap^ One (ap f) (loopSN1 One α)) ∎)
    ap^-S' (S n) f α = ap^ (S (S n)) f α ≃〈 ! (adj-def (ap^-id (S n) f) _) 〉 
                        -- note : could avoid having to mention (ap^-id ...) by defining
                        -- ap^ with adj, but then we'd lose definitional behavior, so this seems better
                       adj _ (ap (ap^ (S n) f) α)                                       ≃〈 adj-bind (ap-loop-by-equals (λ x → ! (ap^-S' n f x)) α) 〉
                       adj _ (ap (\ α' -> loopN1S n (ap^ n (ap f) (loopSN1 n α'))) α)   ≃〈 ap (adj _) (ap-o (loopN1S n) (λ α' → ap^ n (ap f) (loopSN1 n α')) α) 〉
                       adj _ (ap (loopN1S n) (ap (λ α → ap^ n (ap f) (loopSN1 n α)) α)) ≃〈 ap (adj _ o (ap (loopN1S n))) (ap-o (ap^ n (ap f)) (loopSN1 n) α) 〉
                       adj _ (ap (loopN1S n) (ap (ap^ n (ap f)) (ap (loopSN1 n) α)))    ≃〈 adj-eq _ _ _ _ id 〉
                       -- expand back to other side
                       adj _ (ap (loopN1S n) (ap (ap^ n (ap f)) (ap (loopSN1 n) α)))    ≃〈 ! (adj-bind (ap-adj (loopN1S n) _ _)) 〉
                       adj _ (ap (loopN1S n) (adj _ (ap (ap^ n (ap f)) (ap (loopSN1 n) α)))) ≃〈 ap (adj _) (ap (\ x -> ap (loopN1S n) x) (! (ap-adj (ap^ n (ap f)) _ _)))  〉
                       adj _ (ap (loopN1S n) (ap (ap^ n (ap f)) (adj _ (ap (loopSN1 n) α)))) ≃〈 ap (adj _) (ap (\ x -> ap (loopN1S n) (ap (ap^ n (ap f)) x)) ((adj-def (LoopPath.loopSN1-id n) _)))  〉
                                                                                               -- agda has trouble with the (adj _)'s when they occur under a binder
                       adj _ (ap (loopN1S n) (ap (ap^ n (ap f)) (loopSN1 (S n) α))) ≃〈 ! (adj-bind (ap-adj (loopN1S n) _ _))  〉
                       adj _ (ap (loopN1S n) (adj _ (ap (ap^ n (ap f)) (loopSN1 (S n) α)))) ≃〈 ap (adj _ o (ap (loopN1S n))) (adj-def (ap^-id n (ap f)) _)  〉
                       adj _ (ap (loopN1S n) (ap^ (S n) (ap f) (loopSN1 (S n) α)))  ≃〈 (adj-def (LoopPath.loopN1S-id n) _) 〉 
                       loopN1S (S n) (ap^ (S n) (ap f) (loopSN1 (S n) α)) ∎
    
    -- ap^-S' with coercions moved around
    ap^-ap-assoc : ∀ {A B} → (n : _) → (f : A → B) → {a : A} 
                    (α : Loop n (Path a a) id)
                 → (ap^ n (ap f) α) ≃ loopSN1 n (ap^ (S n) f (loopN1S n α))
    ap^-ap-assoc n f α = 
                       ! (ap (loopSN1 n) (ap^-S' n f (loopN1S n α))) 
                     ∘ ap (λ x → loopSN1 n (loopN1S n (ap^ n (ap f) x))) (! (LoopPath.η n _))
                     ∘ ! (LoopPath.η n _)
    
    ap^-by-equals : ∀ n {A} {B} {f g : A → B} (α : f ≃ g) {a : A} (β : Loop n A a) 
                  → ap^ n f β ≃ rebase n (ap≃ (! α)) (ap^ n g β)
    ap^-by-equals n {f = f} id β = ! (ap≃ (rebase-idpath n) {ap^ n f β})
    
    ap^-by-equals-pointwise : ∀ n {A} {B} {f g : A → B} (α : (x : A) → g x ≃ f x) {a : A} (β : Loop n A a) 
                  → ap^ n f β ≃ rebase n (α a) (ap^ n g β)
    ap^-by-equals-pointwise n {f = f} {g = g} α β = ap (λ x → rebase n x (ap^ n g β)) (Π≃β α ∘ ap (ap (λ f → f _)) (!-invol (λ≃ α))) ∘ ap^-by-equals n (! (λ≃ α)) β
    
    ap^-idfunc : ∀ {A} {a : A} → (n : _) (α : Loop n A a) → ap^ n (\ (x : A) -> x) α ≃ α
    ap^-idfunc One α = ap-id α
    ap^-idfunc (S n) α = ap^ (S n) (λ x → x) α  ≃〈 ap^-S' n (λ x → x) α 〉
                         loopN1S n (ap^ n (ap (λ x → x)) (loopSN1 n α)) ≃〈 ap (loopN1S n) (ap^-by-equals n (λ≃ ap-id) (loopSN1 n α)) 〉
                         loopN1S n (rebase n (ap≃ (! (λ≃ ap-id))) (ap^ n (λ x → x) (loopSN1 n α))) ≃〈 ap (loopN1S n o rebase n (ap≃ (! (λ≃ ap-id)))) (ap^-idfunc n _) 〉
                         loopN1S n (rebase n (ap≃ (! (λ≃ ap-id))) (loopSN1 n α)) ≃〈 ap (λ x → loopN1S n (rebase n x (loopSN1 n α))) (ap-! (\ f -> f id) (λ≃ ap-id)) 〉
                         loopN1S n (rebase n (! (ap≃ (λ≃ ap-id))) (loopSN1 n α)) ≃〈 ap (λ x → loopN1S n (rebase n (! x) (loopSN1 n α))) (Π≃β ap-id) 〉
                         loopN1S n (rebase n id (loopSN1 n α)) ≃〈 ap (loopN1S n) (ap≃ (rebase-idpath n)) 〉
                         loopN1S n (loopSN1 n α) ≃〈 LoopPath.β n _ 〉
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

