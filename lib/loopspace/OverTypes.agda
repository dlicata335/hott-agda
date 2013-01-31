
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
open import lib.TypeEquivalence
open import lib.Prods
open import lib.HigherHomotopyAbelian

open import lib.loopspace.Basics
open import lib.loopspace.Groupoid
open import lib.loopspace.Types
open import lib.loopspace.Truncation

module lib.loopspace.OverTypes where

  -- ENH: what is going on here?
  -- where does this lemma come from?
  -- why do we have it only for a path type,
  -- whereas for all types there is LoopOverS≃ plus equations for (ap^ n B α)

  -- note: non-dependent
  LoopPathOver : (n : Positive) {A : Type} {a : A} (α : Loop n A a) 
              → {B : Type} (f g : A → B) (β : Path {B} (f a) (g a))
              →   (Path {Loop n B (g a)} (rebase n β (ap^ n f α)) (ap^ n g α))
                ≃ (LoopOver n α (\ x -> f x ≃ g x) β)
  LoopPathOver One α f g β = (β ∘ ap f α ∘ ! β  ≃  ap g α) ≃〈 rotate3≃ β (ap f α) β (ap g α) 〉
                             (ap g α ∘ β ∘ ! (ap f α) ≃ β) ≃〈 ap (λ x → x ≃ β) (! (transport-Path f g α β)) 〉
                             (transport (λ x → f x ≃ g x) α β ≃ β) ∎  
  LoopPathOver (S n) {A}{a} α{B} f g β = 
       (rebase (S n) β (ap^ (S n) f α)) ≃ (ap^ (S n) g α) ≃〈 ap (BackPath _) (! (adj-def (rebase-id n β) _)) 〉

       (adj  _ (ap (rebase n β) (ap^ (S n) f α))) ≃ (ap^ (S n) g α) ≃〈 ap (BackPath _) (ap (adj _) (ap (ap (rebase n β)) (! (adj-def (ap^-id n f) _)))) 〉

       (adj  _ (ap (rebase n β) (adj _ (ap (ap^ n f) α)))) ≃ (ap^ (S n) g α) ≃〈 ap (_≃_ _) (! (adj-def (ap^-id n g) _)) 〉

       (adj  _ (ap (rebase n β) (adj _ (ap (ap^ n f) α)))) ≃ (adj _ (ap (ap^ n g) α))  ≃〈 ap (BackPath _) (adj-bind (ap-adj (rebase n β) _ _)) 〉

       (adj  _ (ap (rebase n β) (ap (ap^ n f) α))) ≃ (adj _ (ap (ap^ n g) α))  ≃〈 flip≃ 〉

       (adj  _ (ap (ap^ n g) α)) ≃ (adj _ (ap (rebase n β) (ap (ap^ n f) α)))  ≃〈 move-adj≃ _ _ 〉

       (ap (ap^ n g) α) ≃ (adj _ (ap (rebase n β) (ap (ap^ n f) α)))  ≃〈 ap (Path _) (adj-eq-loop n _ _ (coe (! (LoopPathOver n (id^ n) f g β)) (idOver n (λ x → f x ≃ g x) β)) _ id) 〉
         
       ap (ap^ n g) α 
       ≃ adj _ (ap (rebase n β) (ap (ap^ n f) α))
         ≃〈 ap (Path _) (ap (adj _) (! (ap-o (rebase n β) (ap^ n f) _))) 〉

       ap (ap^ n g) α 
       ≃ adj _ (ap (\ x -> rebase n β (ap^ n f x)) α)
         ≃〈 ap (Path _) (adj-def _ _) 〉

       ap (ap^ n g) α 
       ≃ adjust (coe (! (LoopPathOver n (id^ n) f g β)) (idOver n (λ x → f x ≃ g x) β))
                (ap (\ x -> rebase n β (ap^ n f x)) α)
         ≃〈 id 〉

       ap (ap^ n g) α 
       ≃ coe (! (LoopPathOver n (id^ n) f g β)) (idOver n (\ x -> f x ≃ g x) β) 
         ∘ (ap (\ x -> rebase n β (ap^ n f x)) α) ∘
         ! (coe (! (LoopPathOver n (id^ n) f g β)) (idOver n (λ x → f x ≃ g x) β))
         ≃〈 ! (rotate3≃-2 _ _ _) 〉

       ap (ap^ n g) α ∘ 
         coe (! (LoopPathOver n (id^ n) f g β)) (idOver n (λ x → f x ≃ g x) β) ∘
         ! (ap (\ x -> rebase n β (ap^ n f x)) α) 
       ≃ coe (! (LoopPathOver n (id^ n) f g β)) (idOver n (\ x -> f x ≃ g x) β) ≃〈 ap (BackPath _) (! (transport-Path (λ x → rebase n β (ap^ n f x)) (λ x → ap^ n g x) α _)) 〉

       (transport (λ x → (rebase n β (ap^ n f x)) ≃ (ap^ n g x)) α 
                    (coe (! (LoopPathOver n (id^ n) f g β)) (idOver n (\ x -> f x ≃ g x) β)))
       ≃ coe (! (LoopPathOver n (id^ n) f g β)) (idOver n (\ x -> f x ≃ g x) β) ≃〈 ap (λ x → transport (λ x' → rebase n β (ap^ n f x') ≃ ap^ n g x') α (coe x  (idOver n (\ x -> f x ≃ g x) β)) ≃ (coe x (idOver n (\ x -> f x ≃ g x) β))) (! (Π≃β (λ x → ! (LoopPathOver n x f g β)))) 〉

       (transport (λ x → (rebase n β (ap^ n f x)) ≃ (ap^ n g x)) α 
                    (coe (ap≃ (λ≃ (λ x → ! (LoopPathOver n x f g β))){id^ n}) (idOver n (\ x -> f x ≃ g x) β)))
       ≃ coe ((ap≃ (λ≃ (λ x → ! (LoopPathOver n x f g β))))) (idOver n (\ x -> f x ≃ g x) β) ≃〈 ! (transport-by-equals≃ α
                                                                 {B = λ x → LoopOver n x (λ x' → f x' ≃ g x') β}
                                                                 {B' = λ x → rebase n β (ap^ n f x) ≃ ap^ n g x} (idOver n (\ x -> f x ≃ g x) β) (idOver n (\ x -> f x ≃ g x) β) (λ≃ (λ x → ! (LoopPathOver n x f g β)))) 〉 

       Path {LoopOver n (id^ n) (\ x -> f x ≃ g x) β} 
            (transport (λ x → LoopOver n x (\ x -> f x ≃ g x) β) α (idOver n (\ x -> f x ≃ g x) β))
            (idOver n (\ x -> f x ≃ g x) β) ≃〈 id 〉 

       LoopOver (S n) α (λ x → f x ≃ g x) β ∎



  -- relate LoopOver (S n) α B b to an equation about (ap^ n B α),
  -- and provide rules for ap^ n B for each B

  LoopOverS :  (n : Positive) {A : Type} {a : A} (α : Loop (S n) A a) 
             → (B : A -> Type) (b : B a) → Type
  LoopOverS n {A}{a} α B b = 
    Path{Loop n (B a) b} 
        (apt n (ap^ (S n) B α) b)
        (id^ n)

  postulate
    LoopOverS≃ : (n : Positive) {A : Type} {a : A} (α : Loop (S n) A a) → (B : A -> Type) (b : B a) 
                 → LoopOver (S n) α B b ≃ LoopOverS n α B b 
  -- LoopOverS≃ One α B b = (move-!≃ (apt One (id ∘ ap (λ l → ap B l) α) b) id)
  --                                 ∘ ap (λ x → Id x id) 
  --                                      (transport (λ x → Id (transport B x b) b) α id ≃〈 transport-Path (λ x → transport B x b) (λ _ → b) α id 〉
  --                                       ap (\_ -> b) α ∘ id ∘ ! (ap (\ x -> transport B x b) α) ≃〈 ap (λ x → x ∘ id ∘ ! (ap (λ x' → transport B x' b) α)) (ap-constant b _) 〉 
  --                                       id ∘ id ∘ ! (ap (\ x -> transport B x b) α) ≃〈 ∘-unit-l (id ∘ ! (ap (\ x -> transport B x b) α)) 〉 
  --                                       id ∘ ! (ap (\ x -> transport B x b) α) ≃〈 ∘-unit-l (! (ap (λ x → transport B x b) α)) 〉 
  --                                       ! (ap (\ x -> transport B x b) α) ≃〈 ap !
  --                                                                               (ap-by-equals {f = λ x → transport B x b}
  --                                                                                {g = (λ f → f b) o coe o ap B} (λ x → ap≃ (transport-ap-assoc B x)) α) 〉
  --                                       ! (id ∘ ap ((\ f -> f b) o coe o (ap B)) α ) ≃〈 ap ! (∘-unit-l (ap ((λ f → f b) o coe o ap B) α)) 〉
  --                                       ! (ap ((\ f -> f b) o coe o (ap B)) α ) ≃〈 ap ! (ap-o3 (λ f → f b) coe (ap B) α) 〉
  --                                       ! (ap (\ f -> f b) (ap coe ((ap (ap B)) α))) ≃〈 id 〉
  --                                       ! ((apt One (ap (ap B) α) b)) ≃〈 ap (λ x → ! (apt One x b)) (! (∘-unit-l (ap (ap B) α))) 〉
  --                                       (! (apt One (id ∘ ap (ap B) α) b) ∎))

  -- LoopOverS≃ (S n){A}{a} α B b = 
  --   transport (λ x → LoopOver (S n) x B b) α id 
  --   ≃ id                                              ≃〈 ap (λ x → x ≃ id) (ap≃ (transport-ap-assoc (λ x → LoopOver (S n) x B b) α)) 〉 

  --   coe (ap (λ x → LoopOver (S n) x B b) α) id 
  --   ≃ id                                              ≃〈 ap (λ x → coe x id ≃ id) (ap-loop-by-equals {f = λ x → LoopOver (S n) x B b} {g = λ x → LoopOverS n x B b} (λ x → ! (LoopOverS≃ n x B b)) α) 〉 

  --   coe (adj _ (ap (λ x → LoopOverS n x B b) α)) id 
  --   ≃ id                                               ≃〈 id 〉 

  --   coe (adj _ (ap (λ x → Path{Loop n (B _) b} 
  --                              (apt n (ap^ (S n) B x) b)
  --                              (id^ n))
  --                   α)) id ≃ id                        ≃〈 ap (λ x → coe x id ≃ id) (ap (adj _) (ap-o (\ x -> Id x (id^ n)) (λ x → apt n (ap^ (S n) B x) b) α)) 〉 

  --   coe (adj _ (ap (\ x -> Path x (id^ n))
  --                  (ap (\ x -> (apt n (ap^ (S n) B x) b)) α))) id 
  --   ≃ id                                                ≃〈 id 〉

  --   coe (adj (! (LoopOverS≃ n id B b))
  --            (ap (\ x -> Path x (id^ n))
  --                (ap (\ x -> (apt n (ap^ (S n) B x) b))
  --                    α)))
  --       id
  --   ≃ id                                                ≃〈 ap (λ x → coe x id ≃ id) (adj-def _ _) 〉 

  --   coe (adjust (! (LoopOverS≃ n id B b)) 
  --               (ap (\ x -> Path x (id^ n)) 
  --                   (ap (\ x -> (apt n (ap^ (S n) B x) b))
  --                       α)))
  --        id
  --   ≃ id                                                ≃〈 ap (λ x → x ≃ id) (ap≃ (transport-∘3 (λ x → x) (! (LoopOverS≃ n id B b)) (ap (λ x → Path x (id^ n)) (ap (λ x → apt n (ap^ (S n) B x) b) α)) (! (! (LoopOverS≃ n id B b))))) 〉 

  --   coe (! (LoopOverS≃ n id B b))
  --       (coe (ap (\ x -> Path x (id^ n))
  --                (ap (\ x -> (apt n (ap^ (S n) B x) b)) α)) 
  --            (coe (! (! (LoopOverS≃ n id B b))) id))
  --   ≃ id                                                ≃〈 move-transport-right-!≃ (λ x → x) (LoopOverS≃ n id B b)〉 

  --   coe ((ap (\ x -> Path x (id^ n)) (ap (\ x -> (apt n (ap^ (S n) B x) b)) α))) 
  --        (coe (! (! (LoopOverS≃ n id B b))) id)
  --   ≃ coe (LoopOverS≃ n id B b) id                  ≃〈 ap (λ x → coe (ap (λ x' → Path x' (id^ n)) (ap (λ x' → apt n (ap^ (S n) B x') b) α)) (coe x id) ≃ coe (LoopOverS≃ n id B b) id) (!-invol (LoopOverS≃ n id B b)) 〉 

  --   coe (ap (\ x -> Path x (id^ n)) (ap (\ x -> (apt n (ap^ (S n) B x) b)) α))
  --         (coe (LoopOverS≃ n id B b) id)
  --   ≃ coe (LoopOverS≃ n id B b) id                   ≃〈 ap (λ x → x ≃ (coe (LoopOverS≃ n id B b) id)) (ap≃ (! (transport-ap-assoc' (λ x → x) (λ x → Path x (id^ n)) (ap (λ x → apt n (ap^ (S n) B x) b) α)))) 〉

  --   transport (\ x -> Path x (id^ n)) (ap (\ x -> (apt n (ap^ (S n) B x) b)) α) 
  --         (coe (LoopOverS≃ n id B b) id)
  --   ≃ coe (LoopOverS≃ n id B b) id                  ≃〈 ap (λ x → x ≃ coe (LoopOverS≃ n id B b) id) (transport-Path-pre (ap (λ x → apt n (ap^ (S n) B x) b) α) (coe (LoopOverS≃ n id B b) id)) 〉
 
  --   (coe (LoopOverS≃ n id B b) id) ∘ ! (ap (\ x -> (apt n (ap^ (S n) B x) b)) α)
  --   ≃ coe (LoopOverS≃ n id B b) id                  ≃〈 cancel-left≃ (coe (LoopOverS≃ n id B b) id) (! (ap (λ x → apt n (ap^ (S n) B x) b) α)) 〉 

  --   ! (ap (\ x -> (apt n (ap^ (S n) B x) b)) α)
  --   ≃ id                                                ≃〈 move-!≃ (ap (λ x → apt n (ap^ (S n) B x) b) α) id 〉 

  --   (ap (\ x -> (apt n (ap^ (S n) B x) b)) α)
  --   ≃ id                                                ≃〈 id 〉 

  --   (ap (\ x -> (ap^ n (\f -> f b) (ap^ n coe (loopSN1 n (ap^ (S n) B x))))) α)
  --   ≃ id                                                ≃〈 ap (\ x -> x ≃ id) (ap-o4 (ap^ n (\f -> f b)) (ap^ n coe) (loopSN1 n) (ap^ (S n) B) α) 〉 

  --   (ap (ap^ n (λ f → f b)) (ap (ap^ n coe) (ap (loopSN1 n) (ap (ap^ (S n) B) α))))
  --   ≃ id                                                ≃〈 adj-middle-id _ (ap (ap^ n (λ f → f b)) (ap (ap^ n coe) (ap (loopSN1 n) (ap (ap^ (S n) B) α)))) 〉 
  --   adj _
  --    (ap (ap^ n (λ f → f b)) (ap (ap^ n coe) (ap (loopSN1 n) (ap (ap^ (S n) B) α))))
  --   ≃ id                                                ≃〈 ap (\ x -> x ≃ id) (! lemma) 〉

  --   apt (S n) (ap^ (S (S n)) B α) b ≃ id ∎

  --   where lemma : apt (S n) (ap^ (S (S n)) B α) b ≃ adj
  --                                                     _
  --                                                     (ap (ap^ n (λ f → f b))
  --                                                      (ap (ap^ n coe) (ap (loopSN1 n) (ap (ap^ (S n) B) α)))) 
  --         lemma = apt (S n) (ap^ (S (S n)) B α) b                                                       ≃〈 id 〉 
  --                 ap^ (S n) (\ f -> f b) (ap^ (S n) coe (loopSN1 (S n) (ap^ (S (S n)) B α)))            ≃〈 ! (adj-def (ap^-id n (λ f → f b) {coe id}) (ap (ap^ n (\ f -> f b)) (ap^ (S n) coe (loopSN1 (S n) (ap^ (S (S n)) B α))))) 〉 
  --                 (adj _ (ap (ap^ n (\ f -> f b)) (ap^ (S n) coe (loopSN1 (S n) (ap^ (S (S n)) B α))))) ≃〈 ap (adj _ o ap (ap^ n (λ f → f b))) (! (adj-def (ap^-id n coe {id}) (ap (ap^ n coe) (loopSN1 (S n) (ap^ (S (S n)) B α))))) 〉 
  --                 (adj _ (ap (ap^ n (\ f -> f b)) (adj _ (ap (ap^ n coe) (loopSN1 (S n) (ap^ (S (S n)) B α)))))) ≃〈 adj-bind (ap-adj (ap^ n (λ f → f b)) (ap (ap^ n coe) (loopSN1 (S n) (ap^ (S (S n)) B α))) _) 〉 
  --                 (adj _ (ap (ap^ n (\ f -> f b)) (ap (ap^ n coe) (loopSN1 (S n) (ap^ (S (S n)) B α))))) ≃〈 ap (adj _  o (ap (ap^ n (\ f -> f b))) o ap (ap^ n coe)) (! (adj-def (LoopPath.loopSN1-id n) (ap (loopSN1 n) (ap^ (S (S n)) B α)))) 〉
  --                 (adj _ (ap (ap^ n (\ f -> f b)) (ap (ap^ n coe) (adj _ (ap (loopSN1 n) (ap^ (S (S n)) B α)))))) ≃〈 ap (adj _ o (ap (ap^ n (\ f -> f b)))) (ap-adj (ap^ n coe) (ap (loopSN1 n) (ap^ (S (S n)) B α)) _)  〉
  --                 (adj _ (ap (ap^ n (\ f -> f b)) (adj _ (ap (ap^ n coe) (ap (loopSN1 n) (ap^ (S (S n)) B α)))))) ≃〈 adj-bind (ap-adj (ap^ n (λ f → f b)) (ap (ap^ n coe) (ap (loopSN1 n) (ap^ (S (S n)) B α))) _) 〉
  --                 (adj _ (ap (ap^ n (\ f -> f b)) (ap (ap^ n coe) (ap (loopSN1 n) (ap^ (S (S n)) B α))))) ≃〈 ap (adj _) (ap (λ x → ap (ap^ n (λ f → f b)) (ap (ap^ n coe) (ap (loopSN1 n) x))) (! (adj-def (ap^-id (S n) B {a}) (ap (ap^ (S n) B) α)))) 〉
  --                 (adj _ (ap (ap^ n (\ f -> f b)) (ap (ap^ n coe) (ap (loopSN1 n) (adj _ (ap (ap^ (S n) B) α)))))) ≃〈 ap (adj _) (ap (\ x -> (ap (ap^ n (\ f -> f b)) (ap (ap^ n coe) x))) (ap-adj (loopSN1 n) (ap (ap^ (S n) B) α) _)) 〉
  --                 (adj _ (ap (ap^ n (\ f -> f b)) (ap (ap^ n coe) (adj _ (ap (loopSN1 n) (ap (ap^ (S n) B) α)))))) ≃〈 ap (adj _) (ap (ap (ap^ n (λ f → f b))) (ap-adj (ap^ n coe) (ap (loopSN1 n) (ap (ap^ (S n) B) α)) _)) 〉
  --                 (adj _ (ap (ap^ n (\ f -> f b)) (adj _ (ap (ap^ n coe) (ap (loopSN1 n) (ap (ap^ (S n) B) α)))))) ≃〈 adj-bind (ap-adj (ap^ n (λ f → f b)) (ap (ap^ n coe) (ap (loopSN1 n) (ap (ap^ (S n) B) α))) _) 〉
  --                 (adj _ (ap (ap^ n (\ f -> f b)) (ap (ap^ n coe) (ap (loopSN1 n) (ap (ap^ (S n) B) α))))) ∎



  ap2-ap-assoc : ∀ {A B C D} {a b : A} (f : B → C → D) (g1 : A → B) (g2 : A → C) (α : a ≃ b) → ap (λ a → f (g1 a) (g2 a)) α ≃ ap2 f (ap g1 α) (ap g2 α)
  ap2-ap-assoc f g1 g2 id = id

  ex : ∀ n {A a} {α α' β β' : Loop n A a} (p : α ≃ α') (q : β ≃ β') → ap2 (∘^ n) p q ≃ ap (λ x → ∘^ n x β') p ∘ ap (∘^ n α) q
  ex n id id = id

  -- rule for functions

  ap^-of-o3 : ∀ n {A B2 B3} {a : A} {α : Loop n A a}
              (g1 : A → B2 → B2) (f : B2 -> B3) (g2 : A -> B3 -> B3)
            -> ap^ n (\ a -> g2 a o f o g1 a) α ≃
               λl n (λ x → ∘^ n (ap^ n (λ a' → g2 a' (f (g1 a x))) α) (ap^ n (λ a' → g2 a (f (g1 a' x))) α))
  ap^-of-o3 n {a = a} {α = α} g1 f g2 = LoopΠ.ext n _ _ (λ x → ! (ap≃ (LoopΠ.β n (λ x → ∘^ n (ap^ n (λ a' → g2 a' (f (g1 a x))) α) (ap^ n (λ a' → g2 a (f (g1 a' x))) α))))
                                                              ∘ lemma n a α (λ t → f (g1 t x)) g2 ∘ ! (ap^-o n (λ f → f x) (λ a x₁ → g2 a (f (g1 a x₁))) α)) where
    lemma : ∀ n {A B C} (a : A) (α : Loop n A a) (f : A → B) (g : A → B → C) →
          ap^ n (λ a → g a (f a)) α ≃ (∘^ n (ap^ n (λ t → g t (f a)) α)
                                            (ap^ n (λ t → g a (f t)) α))
    lemma One a α f g = (! (ap∘ (ap-o (λ x → x (f a)) g α) (ap-o (g a) f α)) ∘ ap2-aps-1 (λ f x → f x) (ap g α) (ap f α)) ∘ ap2-ap-assoc (λ f x → f x) g f α
    lemma (S n) a α f g = ap^ (S n) (λ a₁ → g a₁ (f a₁)) α ≃〈 ! (adj-def (ap^-id n (λ a₁ → g a₁ (f a₁))) _) 〉
                          adj _ (ap (ap^ n (λ a₁ → g a₁ (f a₁))) α) ≃〈 adj-bind (ap-loop-by-equals {f = (ap^ n (λ a₁ → g a₁ (f a₁)))} {g = (λ β → ∘^ n (ap^ n (λ t → g t (f a)) β) (ap^ n (λ t → g a (f t)) β))} (λ x → ! (lemma n a x f g)) α) 〉
                          adj _ (ap (λ β → ∘^ n (ap^ n (λ t → g t (f a)) β)
                                                (ap^ n (λ t → g a (f t)) β)) α) ≃〈 ap (adj _) (ap2-ap-assoc (∘^ n) (ap^ n (λ t → g t (f a))) (ap^ n (λ t → g a (f t))) α) 〉
                          adj _ (ap2 (∘^ n) (ap (ap^ n (λ t → g t (f a))) α) (ap (ap^ n (λ t → g a (f t))) α)) ≃〈 ap (adj _) (ex n (ap (ap^ n (λ t → g t (f a))) α) (ap (ap^ n (λ t → g a (f t))) α)) 〉
                          adj _ (ap (λ x → ∘^ n x (ap^ n (λ t → g a (f t)) (id^ n))) (ap (ap^ n (λ t → g t (f a))) α) ∘ ap (∘^ n (ap^ n (λ t → g t (f a)) (id^ n))) (ap (ap^ n (λ t → g a (f t))) α))
                                ≃〈 ap (adj _) (ap∘ (ap-loop-by-equals {f = (λ x → ∘^ n x (ap^ n (λ t → g a (f t)) (id^ n)))} {g = λ x → x} (λ x → ap (∘^ n x) (! (ap^-id n (λ t → g a (f t)))) ∘ ! (∘^-unit-r n x)) (ap (ap^ n (λ t → g t (f a))) α)) (ap-loop-by-equals {f = (∘^ n (ap^ n (λ t → g t (f a)) (id^ n)))} {g = λ x → x} (λ x → ap (λ t → ∘^ n t x) (! (ap^-id n (λ t → g t (f a)))) ∘ ! (∘^-unit-l n x)) (ap (ap^ n (λ t → g a (f t))) α))) 〉
                          adj _ (adj _ (ap (λ x → x) (ap (ap^ n (λ t → g t (f a))) α)) ∘ adj _ (ap (λ x → x) (ap (ap^ n (λ t → g a (f t))) α))) ≃〈 {!!} 〉
                          adj _ (adj _ (ap (ap^ n (λ t → g t (f a))) α) ∘ adj _ (ap (ap^ n (λ t → g a (f t))) α)) ≃〈 {!!} 〉
                          (adj _ (ap (ap^ n (λ t → g t (f a))) α)) ∘ (adj _ (ap (ap^ n (λ t → g a (f t))) α)) ≃〈 {!!} 〉
                          (ap^ (S n) (λ t → g t (f a)) α) ∘ (ap^ (S n) (λ t → g a (f t)) α) ∎


  LoopType→ : ∀ n {A B} → (Loop (S n) Type A) -> Loop (S n) Type B -> Loop (S n) Type (A → B)
  LoopType→ n {A} {B} lA lB = λt n (λ (f : A → B) →
                                      λl n (λ (x : A) →
                                              ∘^ n (apt n lB (f x)) 
                                                   (ap^ n f (apt n (!^ (S n) lA) x))))
  ap^→ : ∀ {A} → (n : _) → (C D : A → Type) → {base : A} (α : Loop (S n) A base) →
           ap^ (S n) (\ x -> C x → D x) α 
         ≃ LoopType→ n (ap^ (S n) C α) (ap^ (S n) D α)
  ap^→ n C D α = LoopSType.ext n (λ f → 
    apt n (ap^ (S n) (λ x → C x → D x) α) f ≃〈 apt-apS n (λ x → C x → D x) _ _ 〉

    ap^ n (\ a -> transport (λ x → C x → D x) a f) (loopSN1 n α) ≃〈 ap^-by-equals-pointwise n {f = \ a -> transport (λ x → C x → D x) a f} {g = \ a -> transport D a o f o transport C (! a)} (λ x → ! (transport-→ C D x f)) (loopSN1 n α) 〉

    rebase n id (ap^ n (\ a -> transport D a o f o transport C (! a)) (loopSN1 n α)) ≃〈 ap≃ (rebase-idpath n) 〉

    (ap^ n (\ a -> transport D a o f o transport C (! a)) (loopSN1 n α)) ≃〈 ap^-of-o3 n {α = loopSN1 n α} (transport C o !) f (transport D) 〉
    (λl n (λ x → ∘^ n (ap^ n (\ a -> transport D a (f x)) (loopSN1 n α))
                      (ap^ n (\ a -> f (transport C (! a) x)) (loopSN1 n α)))) ≃〈 ap (λl n) (λ≃ (λ x → ap (∘^ n (ap^ n (\ a -> transport D a (f x)) (loopSN1 n α))) (ap^-o n (λ a → f (transport C a x)) ! (loopSN1 n α)))) 〉 

    (λl n (λ x → ∘^ n (ap^ n (\ a -> transport D a (f x)) (loopSN1 n α))
                      (ap^ n (\ a -> f (transport C a x)) (ap^ n ! (loopSN1 n α))))) ≃〈 ap (λl n) (λ≃ (λ x → ap (∘^ n (ap^ n (\ a -> transport D a (f x)) (loopSN1 n α))) (ap (ap^ n (\ a -> f (transport C a x))) (! (!^-ap^! n (loopSN1 n α)))))) 〉 

    (λl n (λ x → ∘^ n (ap^ n (\ a -> transport D a (f x)) (loopSN1 n α))
                      (ap^ n (\ a -> f (transport C a x)) (!^ n (loopSN1 n α))))) ≃〈 ap (λl n) (λ≃ (λ x → ap (∘^ n (ap^ n (\ a -> transport D a (f x)) (loopSN1 n α))) (ap^-o n f (λ a → transport C a x) (!^ n (loopSN1 n α))))) 〉 

    (λl n (λ x → ∘^ n (ap^ n (\ a -> transport D a (f x)) (loopSN1 n α))
                      (ap^ n f (ap^ n (\ a -> transport C a x) (!^ n (loopSN1 n α)))))) ≃〈 ap (λl n) (λ≃ (λ x → ap (∘^ n (ap^ n (\ a -> transport D a (f x)) (loopSN1 n α))) (ap (ap^ n f) (ap^-! n (λ a → transport C a x) (loopSN1 n α))))) 〉 

    (λl n (λ x → ∘^ n (ap^ n (\ a -> transport D a (f x)) (loopSN1 n α))
                      (ap^ n f (!^ n (ap^ n (\ a -> transport C a x) (loopSN1 n α)))))) ≃〈  ap (λl n) (λ≃ (λ x → ap (∘^ n (ap^ n (\ a -> transport D a (f x)) (loopSN1 n α))) (ap (ap^ n f) (ap (!^ n) (! (apt-apS n C α x)))))) 〉 

    (λl n (λ x → ∘^ n (ap^ n (\ a -> transport D a (f x)) (loopSN1 n α))
                      (ap^ n f (!^ n (apt n (ap^ (S n) C α) x))))) ≃〈 ap (λl n) (λ≃ (λ x → ap (λ t → ∘^ n t (ap^ n f (!^ n (apt n (ap^ (S n) C α) x)))) (! (apt-apS n D α (f x))))) 〉 

    (λl n (λ x → ∘^ n (apt n (ap^ (S n) D α) (f x))
                      (ap^ n f (!^ n (apt n (ap^ (S n) C α) x))))) ≃〈 ap (λl n) (λ≃ (λ x → ap (∘^ n (apt n (ap^ (S n) D α) (f x))) (ap (ap^ n f) (! (apt-! n (ap^ (S n) C α) x))))) 〉 

    (λl n (λ x → ∘^ n (apt n (ap^ (S n) D α) (f x))
                      (ap^ n f (apt n (!^ (S n) (ap^ (S n) C α)) x)))) ≃〈 ! (LoopSType.β n _ _) 〉 
    apt n (LoopType→ n (ap^ (S n) C α) (ap^ (S n) D α)) f ∎)

  -- corollary: 
  -- could just use LoopOverS≃ and ap^→ in clients, but
  -- this wrapper builds in a little β/η
  Loop→OverS : (n : Positive) {A : Type} {a : A} (α : Loop (S n) A a) 
              → {B C : A → Type} (f : B a → C a)
              →   Path {Loop n (B a → C a) f}
                    (λl n
                     (λ x →
                        ∘^ n (apt n (ap^ (S n) C α) (f x))
                             (ap^ n f (apt n (!^ (S n) (ap^ (S n) B α)) x))))
                    (λl n (λ x → id^ n))
                ≃ (LoopOver (S n) α (\ x -> B x → C x) f)
  Loop→OverS n α{B}{C} f = ! (LoopOverS≃ n α (λ x → B x → C x) f) 
                          ∘ ap (λ x → Id (apt n x f) (id^ n)) (! (ap^→ n B C {_} α)) 
                          ∘ ap (λ x → Id x (id^ n)) (! (LoopSType.β n _ _))
                          ∘ ap (Id _) (LoopΠ.η n (id^ n) ∘ ap (λl n) (λ≃ (λ x → ! (ap^-id n (λ f' → f' x)))))


  -- rule for truncations

  ap^-Trunc : ∀ n k {A} (α : Loop (S n) Type A) → 
              ap^ (S n) (\ A -> Trunc k A) α ≃ λt n (Trunc-elim (λ tβ → Loop n (Trunc k A) tβ)
                                                    (λ _ → IsKTrunc-Loop n k Trunc-is) 
                                                    (λ x → ap^ n [_] (apt n α x))) 
  ap^-Trunc n k α = LoopSType.ext n (λ x → apt n (ap^ (S n) (Trunc k) α) x ≃〈 STS x 〉
                                           (Trunc-elim (Loop n (Trunc k _)) (λ z → IsKTrunc-Loop n k Trunc-is)
                                                (λ x' → ap^ n [_] (apt n α x'))
                                              x) ≃〈 ! (LoopSType.β n _ _)〉 
                                           (apt n
                                              (λt n
                                               (Trunc-elim (Loop n (Trunc k _)) (λ z → IsKTrunc-Loop n k Trunc-is)
                                                (λ x' → ap^ n [_] (apt n α x'))))
                                              x
                                              ∎)) where 
            STS : ∀ x -> apt n (ap^ (S n) (Trunc k) α) x ≃
                           (Trunc-elim (Loop n (Trunc k _)) (λ z → IsKTrunc-Loop n k Trunc-is)
                                       (λ x' → ap^ n [_] (apt n α x'))
                                       x) 
            STS = Trunc-elim _ (λ x → path-preserves-IsTrunc (IsKTrunc-Loop n k Trunc-is)) 
                               (STS1) where
               STS1 : ∀ x' -> apt n (ap^ (S n) (Trunc k) α) [ x' ] ≃
                              ap^ n [_] (apt n α x')
               STS1 x' = apt n (ap^ (S n) (Trunc k) α) [ x' ]                       ≃〈 apt-apS n (Trunc k) α [ x' ] 〉 
                         ap^ n (λ a → transport (Trunc k) a [ x' ]) (loopSN1 n α)   ≃〈 ap^-by-equals n {f = λ a → transport (Trunc k) a [ x' ]} {g = λ a → [ coe a x' ]} (λ≃ (λ a → transport-Trunc' (λ x → x) a [ x' ])) (loopSN1 n α) 〉
                         rebase n _ (ap^ n (λ a → [ coe a x' ]) (loopSN1 n α))      ≃〈 ap (λ x → rebase n x (ap^ n (λ a → [ coe a x' ]) (loopSN1 n α))) ((ap {M = ap (λ f → f id) (λ≃ (λ a → transport-Trunc'{k} (λ x → x) a [ x' ]))} {N = id} ! (Π≃β (λ a → transport-Trunc' {k} (λ x → x) a [ x' ]){id})) ∘ ap-! (λ f → f id) (λ≃ (λ a → transport-Trunc' {k} (λ x → x) a [ x' ]))) 〉 
                         rebase n id (ap^ n (λ a → [ coe a x' ]) (loopSN1 n α))      ≃〈 ap≃ (rebase-idpath n) 〉 
                         ap^ n (λ a → [ coe a x' ]) (loopSN1 n α)                    ≃〈 ap^-o n [_] (λ p → coe p x') (loopSN1 n α) 〉
                         ap^ n [_] (ap^ n (\ p -> coe p x') (loopSN1 n α))          ≃〈 ap (ap^ n [_]) (! (LoopSType.apt-def n α x'))  〉
                         (ap^ n [_] (apt n α x') ∎)
 

  -- rule for paths

  ap^-Path : (n : Positive) {A : Type} {a : A} (α : Loop (S n) A a) 
           → {B : Type} (f g : A → B) 
           → (ap^ (S n) (\ x -> f x ≃ g x) α) ≃ λt n (λ p → rebase n (∘-unit-l p)
                                                            (ap^ n (λ x → ap g x ∘ p ∘ ! (ap f x))
                                                                   (loopSN1 n α)))
  ap^-Path n α f g = LoopSType.ext n (λ x →
    apt n (ap^ (S n) (λ x₁ → f x₁ ≃ g x₁) α) x ≃〈 apt-apS n (λ x → f x ≃ g x) α x 〉
    ap^ n (λ y → transport (λ x → f x ≃ g x) y x) (loopSN1 n α) ≃〈 ap^-by-equals-pointwise n {f = (λ y → transport (λ x → f x ≃ g x) y x)} {g = (λ x₁ → ap g x₁ ∘ x ∘ ! (ap f x₁))} (λ z → ! (transport-Path f g z x)) (loopSN1 n α) 〉
    rebase n (! (! (∘-unit-l x)))
      (ap^ n (λ z → ap g z ∘ x ∘ ! (ap f z)) (loopSN1 n α)) ≃〈 ap (λ t → rebase n t (ap^ n (λ z → ap g z ∘ x ∘ ! (ap f z)) (loopSN1 n α))) (!-invol (∘-unit-l x)) 〉
    rebase n (∘-unit-l x) (ap^ n (λ x₁ → ap g x₁ ∘ x ∘ ! (ap f x₁)) (loopSN1 n α)) ≃〈 ! (LoopSType.β n _ x) 〉
    apt n
      (λt n
        (λ p →
          rebase n (∘-unit-l p)
          (ap^ n (λ x₁ → ap g x₁ ∘ p ∘ ! (ap f x₁)) (loopSN1 n α))))
      x ∎)

  -- corollary
  ap^-Path-post : (n : Positive) {A : Type} {a : A} (α : Loop (S n) A a) (a0 : A) 
           → (ap^ (S n) (\ x -> a0 ≃ x) α) ≃ λt n (λ p → rebase n (∘-unit-l p)
                                                            (ap^ n (λ x → x ∘ p)
                                                                   (loopSN1 n α)))
  ap^-Path-post n α a0 = ap^ (S n) (\ x -> a0 ≃ x) α ≃〈 ap^-Path n α (λ _ → a0) (λ x → x) 〉
                         λt n (λ p → rebase n (∘-unit-l p) (ap^ n (λ x → ap (λ x → x) x ∘ p ∘ ! (ap (λ _ → a0) x)) (loopSN1 n α))) ≃〈 ap (λt n) (λ≃ (λ p → ap (rebase n (∘-unit-l p)) (ap^-by-equals-pointwise n {f = (λ x → ap (λ x₁ → x₁) x ∘ p ∘ ! (ap (λ _ → a0) x))} {g = (λ x → x ∘ p)} (λ q → ap∘ (! (ap-id q)) (ap (λ q → p ∘ (! q)) (! (ap-constant a0 q)))) (loopSN1 n α)))) 〉
                         λt n (λ p → rebase n (∘-unit-l p) (rebase n id (ap^ n (λ x → x ∘ p) (loopSN1 n α)))) ≃〈 ap (λt n) (λ≃ (λ p → ap (rebase n (∘-unit-l p)) (ap≃ (rebase-idpath n)))) 〉
                         λt n (λ p → rebase n (∘-unit-l p) (ap^ n (λ x → x ∘ p) (loopSN1 n α))) ∎


  -- composite of ap^-Trunc and ap^-Path

  -- higher-dimensional "[ α ∘ β ]"
  LoopTypeTruncPathPost : ∀ n k {A} {a : A} (α : Loop (S n) A a) (a0 : A) 
                   → Loop (S n) Type (Trunc k (Path{A} a0 a))
  LoopTypeTruncPathPost n k α a0 = λt n (Trunc-elim (λ tβ → Loop n (Trunc k (Path a0 _)) tβ) 
                                                    (λ _ → IsKTrunc-Loop n k Trunc-is) 
                                                    (λ β → ap^ n [_]
                                                    (rebase n (∘-unit-l β) (ap^ n (λ x → x ∘ β) (loopSN1 n α)))))

  ap^TruncPathPost : ∀ n k {A} {a : A} (α : Loop (S n) A a) (a0 : A)
              → Path{Loop (S n) Type (Trunc k (Path{A} a0 a))}
                  (ap^ (S n) (\ x -> Trunc k (Path a0 x)) α)
                  (LoopTypeTruncPathPost n k α a0)
  ap^TruncPathPost n k α a0 = ap^ (S n) (λ x → Trunc k (Path a0 x)) α ≃〈 ap^-o (S n) (Trunc k) (Path a0) α 〉
                              ap^ (S n) (Trunc k) (ap^ (S n) (Path a0) α) ≃〈 ap (ap^ (S n) (Trunc k)) (ap^-Path-post n α a0) 〉
                              ap^ (S n) (Trunc k) (λt n (λ p → rebase n (∘-unit-l p)
                                                              (ap^ n (λ x → x ∘ p)
                                                                     (loopSN1 n α)))) ≃〈 ap^-Trunc n k _ 〉
                              λt n (Trunc-elim (λ tβ → Loop n (Trunc k _) tβ)
                                                    (λ _ → IsKTrunc-Loop n k Trunc-is) 
                                                    (λ x → ap^ n [_] (apt n (λt n (λ p → rebase n (∘-unit-l p)
                                                              (ap^ n (λ x → x ∘ p)
                                                                     (loopSN1 n α)))) x))) ≃〈 ap (λt n o (Trunc-elim (λ tβ → Loop n (Trunc k _) tβ) (λ _ → IsKTrunc-Loop n k Trunc-is))) (λ≃ (λ x → ap (ap^ n [_]) (LoopSType.β n _ _))) 〉
                              LoopTypeTruncPathPost n k α a0 ∎


{- not needed right now but possibly good stuff; don't delete

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

  ap^Loop : ∀ n k {A} {a : A} (α : Loop (S n) A a) → ap^ (S n) (λ x → Loop k A x) α ≃ λt n (λ x → rebase n (ap≃ (rebase-idpath k)) (ap^ n (λ p → rebase k p x) (coe (LoopPath {n}) α)))
  ap^Loop n k α = {!!}
-}


