
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
open import lib.loopspace.Groupoid
open import lib.loopspace.Types
open import lib.loopspace.Truncation

module lib.loopspace.OverTypes where

{- not needed right now but good stuff; don't delete

  module LoopOver-idloop where

   mutual
    deover : (n : Positive) {A : Type} {a : A} {B : A → Type} {b : B a}
           ->  LoopOver n (id^ n) B b → Loop n (B a) b
    deover One lo = lo
    deover (S n) {B = B} {b = b} lo = adjust (deover-id n B b) (ap (deover n) lo)

    deover-id : (n : Positive) {A : Type} {a : A} (B : A → Type) (b : B a)
              -> deover n (idOver n B b) ≃ id^ n
    deover-id One B b = id
    deover-id (S n) B b = !-inv-with-middle-r (deover-id n B b) id

   mutual
    over : (n : Positive) {A : Type} {a : A} {B : A → Type} {b : B a}
           -> Loop n (B a) b → LoopOver n (id^ n) B b 
    over One lo = lo
    over (S n) {B = B} {b = b} lo = adjust (over-id n B b) (ap (over n) lo)

    over-id : (n : Positive) {A : Type} {a : A} (B : A → Type) (b : B a)
              -> over n (id^ n) ≃ idOver n B b
    over-id One B b = id
    over-id (S n) B b = !-inv-with-middle-r (over-id n B b) id

   path : (n : Positive) {A : Type} {a : A} (B : A → Type) (b : B a) 
                  ->  Loop n (B a) b ≃ LoopOver n (id^ n) B b 
   path n B b = ua (improve (hequiv (over n) (deover n) {!!} {!!}))

  open LoopOver-idloop using (deover; over) 



  mutual
    -- more computational version of transport at LoopOver n - B b
    rebaseOver : (n : Positive) {A : Type} {a : A} {α α' : Loop n A a}
               → (B : A -> Type) (b : B a)
               → (p : Path α α') -> LoopOver n α B b -> LoopOver n α' B b
    rebaseOver One B b p l = l ∘ ! (ap (λ x → transport B x b) p)
    rebaseOver (S n) {α = α} {α' = α'} B b p l = 
       l
     ∘ ! (transport-LoopOver n α (idOver n B b))
     ∘ (! (ap (\ x -> rebaseOver n B b x (idOver n B b)) p))
     ∘ transport-LoopOver n α' (idOver n B b) 
      {- so you can see what's going on:
      transport (λ x → LoopOver n x B b) α' (idOver n B b) ≃〈 transport-LoopOver n α' (idOver n B b) 〉
      rebaseOver n α' (idOver n B b) ≃〈 (! (ap (\ x -> rebaseOver n x (idOver n B b)) p)) 〉
      rebaseOver n α  (idOver n B b) ≃〈 ! (transport-LoopOver n α (idOver n B b)) 〉
      transport (\ x -> LoopOver n x B b) α  (idOver n B b) ≃〈 l 〉
      (idOver n B b ∎)
      -}

    rebaseOver-idpath : (n : Positive) {A : Type} {a : A} {α : Loop n A a}
               → {B : A -> Type} {b : B a} (l : LoopOver n α B b)
               -> rebaseOver n B b id l ≃ l
    rebaseOver-idpath One l = id
    rebaseOver-idpath (S n) {α = α} {B = B} {b = b} l = 
      ap (λ x → l ∘ x) (!-inv-with-middle-l (transport-LoopOver n α (idOver n B b)) id)

    transport-LoopOver : (n : Positive) {A : Type} {a : A} {α α' : Loop n A a}
               {B : A -> Type} {b : B a} 
               (p : Path α α') (l : LoopOver n α B b)
               → transport (\ x -> LoopOver n x B b) p l ≃ rebaseOver n B b p l
    transport-LoopOver n id l = ! (rebaseOver-idpath n l)
-}


  {-
  postulate
    add-!-≃ : ∀ {A} {M : A} (p : Path M M) → (! p ≃ id) ≃ (p ≃ id)

  -- add-!-≃' : ∀ {A} {M N P : A} (p : Path M N) (q : Path N M) → (! p ≃ q) ≃ (p ≃ ! q)
  -- add-!-≃' id = {!!}

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
  -}


  LoopOverS :  (n : Positive) {A : Type} {a : A} (α : Loop (S n) A a) 
             → (B : A -> Type) (b : B a) → Type
  LoopOverS n {A}{a} α B b = 
    Path{Loop n (B a) b} 
        (apt n (ap^ (S n) B α) b)
        (id^ n)

{- maybe needed? 
  idOverS : ∀ n {A} {a} (B : A → Type) (b : B a) → LoopOverS n id B b
  idOverS n B b = apt n (ap^ (S n) B id) b ≃〈 ap (λ x → apt n x b) (ap^-id (S n) B) 〉
                  apt n id b ≃〈 apt-id n b 〉
                  id^ n ∎

  transport-≃Paths : ∀ {A} {B} → {f g : A → B} (P : A → Type) (α : (a : A) → P a ≃ (f a ≃ g a)) {a b : A} (p : a ≃ b) (u : P a) → transport P p u ≃ coe (! (α b)) (ap g p ∘ coe (α a) u ∘ ! (ap f p))
  transport-≃Paths P α id u = {!!}
-}


  ap-Path-1 : ∀ {A B} (f : A → B) (b : B) {M N : A} (α : M ≃ N) -> ap (\ x -> f x ≃ b) α ≃ ap (\ x -> Id x b) (ap f α)
  ap-Path-1 f g id = id

  LoopOver-is-S : (n : Positive) {A : Type} {a : A} (α : Loop (S n) A a) → (B : A -> Type) (b : B a) 
                 → LoopOver (S n) α B b ≃ LoopOverS n α B b 
  LoopOver-is-S One α B b = {!!}
{-
    LoopOver-is-S One α B b = add-!-≃
                                  (apt One (id ∘ ap (λ l → ap B l) α) b)
                                  ∘ ap (λ x → Id x id) 
                                       (transport (λ x → Id (transport B x b) b) α id ≃〈 {!!} 〉
                                        ap (\_ -> b) α ∘ id ∘ ! (ap (\ x -> transport B x b) α) ≃〈 {!!} 〉 
                                        id ∘ id ∘ ! (ap (\ x -> transport B x b) α) ≃〈 {!!} 〉 
                                        ! (ap (\ x -> transport B x b) α) ≃〈 {!!} 〉
                                        ! (ap (\ x -> coe (ap B x) b) α) ≃〈 {!!} 〉  
                                        ! (ap (\ x -> coe x b) (ap (ap B) α)) ≃〈 id 〉 
                                        ! (ap^ One (\ x -> coe x b) (ap (ap B) α)) ≃〈 {!!} 〉 
                                        ! ((apt One (ap (ap B) α) b)) ≃〈 {!!} 〉
                                        (! (apt One (id ∘ ap (ap B) α) b) ∎))
-}
  LoopOver-is-S (S n) α B b = 
    (transport (λ x → LoopOver (S n) x B b) α id ≃ id) ≃〈 ap (λ x → x ≃ id) (ap≃ (transport-ap-assoc (λ x → LoopOver (S n) x B b) α)) 〉 
    (coe (ap (λ x → LoopOver (S n) x B b) α) id ≃ id) ≃〈 ap (λ x → coe x id ≃ id) (ap-loop-by-equals {f = λ x → LoopOver (S n) x B b} {g = λ x → LoopOverS n x B b} (λ x → ! (LoopOver-is-S n x B b)) α) 〉 
    (coe (adj _ (ap (λ x → LoopOverS n x B b) α)) id ≃ id) ≃〈 id 〉 
    (coe (adj _ (ap (λ x → Path{Loop n (B _) b} 
                               (apt n (ap^ (S n) B x) b)
                               (id^ n))
                    α)) id ≃ id) ≃〈 ap (λ x → coe x id ≃ id) (ap (adj _) (ap-Path-1 (λ x → apt n (ap^ (S n) B x) b) (id^ n) α)) 〉 
    (coe (adj _ (ap (\ x -> Path x (id^ n)) (ap (\ x -> (apt n (ap^ (S n) B x) b)) α))) id ≃ id) ≃〈 id 〉 

    (coe (adj (! (LoopOver-is-S n id B b)) ((ap (\ x -> Path x (id^ n)) 
                                                (ap (\ x -> (apt n (ap^ (S n) B x) b)) α))))
          id ≃ id) ≃〈 {!!} 〉 

    (coe (! (LoopOver-is-S n id B b))
     (coe ((ap (\ x -> Path x (id^ n)) (ap (\ x -> (apt n (ap^ (S n) B x) b)) α))) 
          (coe (LoopOver-is-S n id B b) id))
     ≃ id) ≃〈 {!!} 〉 

    (coe ((ap (\ x -> Path x (id^ n)) (ap (\ x -> (apt n (ap^ (S n) B x) b)) α))) 
          (coe (LoopOver-is-S n id B b) id))
    ≃ (coe (LoopOver-is-S n id B b) id) ≃〈 {!!} 〉 

    ((coe (LoopOver-is-S n id B b) id) ∘ ! (ap (\ x -> (apt n (ap^ (S n) B x) b)) α))
    ≃ (coe (LoopOver-is-S n id B b) id) ≃〈 {!!} 〉 

    (! (ap (\ x -> (apt n (ap^ (S n) B x) b)) α))
    ≃ id ≃〈 {!!} 〉 

    (ap (\ x -> (apt n (ap^ (S n) B x) b)) α) ≃ id ≃〈 {!!} 〉 

    (apt (S n) (ap^ (S (S n)) B α) b ≃ id) ∎

    where lemma : apt (S n) (ap^ (S (S n)) B α) b ≃ {!!} 
          lemma = apt (S n) (ap^ (S (S n)) B α) b ≃〈 {!!} 〉 
                  ap^ (S n) (\ p -> coe p b) (loopSN1 (S n) (ap^ (S (S n)) B α)) ≃〈 {!!} 〉 
                  ap^ (S n) (\ p -> coe p b) (loopSN1 (S n) (ap^ (S (S n)) B α)) ≃〈 {!!} 〉 
                  {!!} ∎

          lemma' : (ap (\ x -> (apt n (ap^ (S n) B x) b)) α) ≃ {!!} 
          lemma' = (ap (\ x -> (apt n (ap^ (S n) B x) b)) α) ≃〈 id 〉 
                   (ap (\ x -> (ap^ n (\f -> f b) (ap^ n coe (loopSN1 n (ap^ (S n) B x))))) α) ≃〈 {!!} 〉 
                   (adj _ (ap (\ x -> (ap^ n (\p -> coe p b) (loopSN1 n (ap^ (S n) B x)))) α)) ≃〈 {!!} 〉 
                   (adj _ (ap (\ x -> (ap^ n (\p -> coe p b) (loopSN1 n (ap^ (S n) B x)))) α)) ≃〈 {!!} 〉 
                   (adj _ (ap (ap^ n (\p -> coe p b)) (ap (\ x -> loopSN1 n (ap^ (S n) B x)) α))) ≃〈 {!!} 〉 
                   (adj _ (ap (ap^ n (\p -> coe p b)) (ap (loopSN1 n) (ap (ap^ (S n) B) α)))) ≃〈 {!!} 〉 
--                   (adj _ (ap^ (S n) (\p -> coe p b) (ap (\ x -> loopSN1 n (ap^ (S n) B x)) α))) ≃〈 {!!} 〉 
                   {!!} ∎


{-
    (rebaseOver (S n) B b α id ≃ id) ≃〈 {!!} 〉 
    (id
     ∘ ! (transport-LoopOver n id (idOver n B b))
     ∘ (! (ap (\ x -> rebaseOver n B b x (idOver n B b)) α))
     ∘ transport-LoopOver n id (idOver n B b) ≃ id) ≃〈 {!!} 〉   
    ((ap (\ x -> rebaseOver n B b x (idOver n B b)) α) ≃ id) ≃〈 {!!} 〉   
    ((ap (\ x -> transport (\ x' -> LoopOver n x' B b) x (idOver n B b)) α) ≃ id) ≃〈 {!!} 〉  -- adjustments?
    ((ap (\ x -> transport (\ x' -> LoopOver n x' B b) x (idOver n B b)) α) ≃ id) ≃〈 {!!} 〉  -- adjustments?
-}

{-
   (transport (λ x → LoopOver (S (S n)) x B b) α id ≃ id) ≃〈 {!!} 〉 
    (rebaseOver (S (S n)) B b α id ≃ id) ≃〈 {!!} 〉 
    (id
     ∘ ! (transport-LoopOver (S n) id (idOver (S n) B b))
     ∘ (! (ap (\ x -> rebaseOver (S n) B b x (idOver (S n) B b)) α))
     ∘ transport-LoopOver (S n) id (idOver (S n) B b) ≃ id) ≃〈 {!!} 〉   
    ((ap (\ x -> rebaseOver (S n) B b x (idOver (S n) B b)) α) ≃ id) ≃〈 {!!} 〉   
    ((ap (\ x -> transport (\ x' -> LoopOver (S n) x' B b) x (idOver (S n) B b)) α) ≃ id) ≃〈 {!!} 〉  -- adjustments?
    (apt (S (S n)) (ap^ (S (S (S n))) B α) b ≃ id^ (S (S (n)))) ∎
-}

{-
-}

  {-
  mutual
    LoopOver-is-S : (n : Positive) {A : Type} {a : A} (α : Loop (S n) A a) → (B : A -> Type) (b : B a) 
                    → LoopOver (S n) α B b ≃ LoopOverS n α B b 
    -- One case should be done
    LoopOver-is-S One α B b = add-!-≃
                                  (apt One (id ∘ ap (λ l → ap B l) α) b)
                                  ∘ ap (λ x → Id x id) 
                                       (transport (λ x → Id (transport B x b) b) α id ≃〈 {!!} 〉
                                        ap (\_ -> b) α ∘ id ∘ ! (ap (\ x -> transport B x b) α) ≃〈 {!!} 〉 
                                        id ∘ id ∘ ! (ap (\ x -> transport B x b) α) ≃〈 {!!} 〉 
                                        ! (ap (\ x -> transport B x b) α) ≃〈 {!!} 〉
                                        ! (ap (\ x -> coe (ap B x) b) α) ≃〈 {!!} 〉  
                                        ! (ap (\ x -> coe x b) (ap (ap B) α)) ≃〈 id 〉 
                                        ! (ap^ One (\ x -> coe x b) (ap (ap B) α)) ≃〈 {!!} 〉 
                                        ! ((apt One (ap (ap B) α) b)) ≃〈 {!!} 〉
                                        (! (apt One (id ∘ ap (ap B) α) b) ∎))
    LoopOver-is-S (S n) α B b = (transport (λ x → LoopOver (S n) x B b) α id ≃ id) ≃〈 {!!} 〉
                                (coe (! (LoopOver-is-S n id B b)) (ap (λ _ → id^ n) α ∘ coe (LoopOver-is-S n id B b) id ∘ ! (ap (λ x → apt n (ap^ (S n) B x) b) α)) ≃ id) ≃〈 {!!} 〉
                                (coe (! (LoopOver-is-S n id B b)) (coe (LoopOver-is-S n id B b) id ∘ ! (ap (λ x → apt n (ap^ (S n) B x) b) α)) ≃ id) ≃〈 {!!} 〉
                                (coe (! (LoopOver-is-S n id B b)) (idOverS n B b ∘ ! (ap (λ x → apt n (ap^ (S n) B x) b) α)) ≃ id) ≃〈 {!!} 〉
                                (coe (! (LoopOver-is-S n id B b)) (idOverS n B b ∘ ! (adj _ (ap ((ap^ n (λ x → coe x b)) o (loopSN1 n) o (ap^ (S n) B)) α))) ≃ id) ≃〈 {!!} 〉
                                -- (coe (ap (λ x → LoopOver (S n) x B b) α) id ≃ id) ≃〈 {!!} 〉
                                -- (coe (adj _ (ap (λ x → (apt n (ap^ (S n) B x) b ≃ id^ n)) α)) id ≃ id) ≃〈 {!!} 〉
                                -- (coe (adj _ (ap (λ x → ap^ n (λ x' → coe x' b) (loopSN1 n (ap^ (S n) B x)) ≃ id^ n) α)) id ≃ id) ≃〈 {!!} 〉
  
                                -- (transport (λ x → transport (λ x' → LoopOver n x' B b) x (idOver n B b) ≃ idOver n B b) α id ≃ id) ≃〈 {!!} 〉
                                -- (ap (λ x → idOver n B b) α ∘ id ∘ ! (ap (λ x → transport (λ x' → LoopOver n x' B b) x (idOver n B b)) α) ≃ id) ≃〈 {!!} 〉
                                -- (! (ap (λ x → transport (λ x' → LoopOver n x' B b) x (idOver n B b)) α) ≃ id) ≃〈 {!!} 〉
                                -- (ap (λ x → transport (λ x' → LoopOver n x' B b) x (idOver n B b)) α ≃ id) ≃〈 {!!} 〉
                                -- (ap (λ p → coe p (idOver n B b)) (ap (ap (λ x' → LoopOver n x' B b)) α) ≃ id) ≃〈 {!!} 〉
  
  -- apt n α a = ap^ n (\ x -> coe x a) (loopSN1 n α)
                                (adj _ (ap ((ap^ n (λ p → coe p b)) o (loopSN1 n) o (ap^ (S n) B)) α) ≃ id)    ≃〈 {!!} 〉
                                (adj _ (ap (ap^ n (λ p → coe p b)) (ap (loopSN1 n) (ap (ap^ (S n) B) α))) ≃ id)    ≃〈 {!!} 〉
                                (adj _ (ap (ap^ n (λ p → coe p b)) (adj _ (ap (loopSN1 n) (ap^ (S (S n)) B α)))) ≃ id)    ≃〈 ap (λ y → y ≃ id) (ap (adj _) (ap (λ x → ap (ap^ n (λ p → coe p b)) x) (adj-def (LoopPath.loopSN1-id n) _))) 〉
                                (adj _ (ap (ap^ n (λ p → coe p b)) (loopSN1 (S n) (ap^ (S (S n)) B α))) ≃ id)             ≃〈 ap (λ x → x ≃ id) (adj-def (ap^-id n (λ p → coe p b) {id}) _)〉
                                (ap^ (S n) (λ p → coe p b) (loopSN1 (S n) (ap^ (S (S n)) B α)) ≃ id)                      ≃〈 {!!} 〉
                                (apt (S n) (ap^ (S (S n)) B α) b ≃ id^ (S n)) ∎  where
      f : (transport (λ x → LoopOver (S n) x B b) α (idOver (S n) B b) ≃ idOver (S n) B b)
          → (apt (S n) (ap^ (S (S n)) B α) b ≃ id^ (S n))
      f p = apt (S n) (ap^ (S (S n)) B α) b ≃〈 {!!} 〉
            id ∎
{-
      g : transport (λ x → LoopOver (S n) x B b) α id ≃ apt (S n) (ap^ (S (S n)) B α) b
      g = {!!}
-}  
    LoopOver-is-S-id : ∀ n {A} {a} (B : A → Type) (b : B a) → coe (LoopOver-is-S n id B b) id ≃ idOverS n B b
    LoopOver-is-S-id One B b = {!!}
    LoopOver-is-S-id (S n) B b = {!!}
  -}

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


  -- FIXME: should be able to derive these compositionally from a rule for 
  -- truncation and a rule for Path in general

  -- intended to to be "α ∘ β"
  LoopTypeTruncPathPost : ∀ n {A} {a : A} (α : Loop (S n) A a) (a0 : A) 
                   → Loop (S n) Type (Trunc (tlp n)(Path{A} a0 a))
  LoopTypeTruncPathPost n α a0 = λt n (Trunc-elim (λ tβ → Loop n (Trunc (tlp n) (Path a0 _)) tβ) 
                                                  (λ _ → IsNTrunc-Loop n Trunc-is) 
                                                  (λ β → ap^ n [_]
                                                        (rebase n (∘-unit-l β)
                                                           (ap^ n (λ x → x ∘ β) (loopSN1 n α)))))

  postulate
    ap^TruncPathPost : ∀ n {A} {a : A} (α : Loop (S n) A a) (a0 : A)
                → 
                Path{Loop (S n) Type (Trunc (tlp n) (Path{A} a0 a))}
                    (ap^ (S n) (\ x -> Trunc (tlp n) (Path a0 x)) α)
                    (LoopTypeTruncPathPost n α a0)


