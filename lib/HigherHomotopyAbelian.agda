{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open import lib.Functions
open Paths
open import lib.AdjointEquiv
open import lib.Univalence

module lib.HigherHomotopyAbelian (A : Set) (base : A) where

  Ω1 : Set
  Ω1 = base ≃ base

  Ω2 : Set
  Ω2 = Path{Ω1} id id 

  _⊙_ : Ω2 → Ω2 → Ω2 
  a ⊙ b =  ap∘ a b

  ⊙-unit-l : (p : Ω2) → (id ⊙ p) ≃ p
  ⊙-unit-l p = ∘-unit-l p ∘ ap∘-unit-l p -- because we know the base is id, the adjustment cancels

  ⊙-unit-r : (a : Ω2) → (a ⊙ id) ≃ a
  ⊙-unit-r a = ap∘-unit-r a 

  interchange : (a b c d : _) → ((a ∘ b) ⊙ (c ∘ d)) ≃ ((a ⊙ c)  ∘ (b ⊙ d))
  interchange a b c d = ichange-type d c b a

  same : (a b : Ω2) → (a ∘ b) ≃ (a ⊙ b)
  same a b = (( a         ∘ b)          ≃〈 ap (λ x → x ∘ b) (! (⊙-unit-r a)) 〉 
              ((a ⊙ id) ∘ b)          ≃〈 ap (λ x → (a ⊙ id) ∘ x) (! (⊙-unit-l b)) 〉 
              ((a ⊙ id) ∘ (id ⊙ b)) ≃〈 ! (interchange a id id b) 〉 
              ((a ∘ id) ⊙ (id ∘ b))  ≃〈 ap (λ x → x ⊙ (id ∘ b)) (∘-unit-r a) 〉 
              (a ⊙ (id ∘ b))           ≃〈 ap (λ x → a ⊙ x) (∘-unit-l b) 〉 
              (a ⊙ b) 
              ∎)

  abelian : (a b : Ω2) → (a ∘ b) ≃ (b ∘ a)
  abelian a b = (a ∘ b) ≃〈 ap (λ x → x ∘ b) (! (⊙-unit-l a)) 〉 
                   ((id ⊙ a) ∘ b)          ≃〈 ap (λ x → (id ⊙ a) ∘ x) (! (⊙-unit-r b)) 〉 
                   ((id ⊙ a) ∘ (b ⊙ id)) ≃〈 ! (interchange id b a id) 〉 
                   ((id ∘ b) ⊙ (a ∘ id)) ≃〈 ap (λ x → x ⊙ (a ∘ id)) (∘-unit-l b) 〉 
                   (b         ⊙ (a ∘ id)) ≃〈 ap (λ x → b ⊙ x) (∘-unit-r a) 〉 
                   (b ⊙ a)                   ≃〈 ! (same b a) 〉 
                   (b ∘ a) 
                   ∎

  -- ----------------------------------------------------------------------
  -- some consequences about inverses
  
  ⊙-inv-l : (p : Ω2) → (ap ! p ⊙ p) ≃ id
  ⊙-inv-l p = ap ! p ⊙ p ≃〈 ap2-ap-assoc-1 _∘_ ! p p  〉 
              ap2 (λ x y → ! x ∘ y) p p ≃〈 ap2-same-is-ap (λ x y → ! x ∘ y) p 〉 
              ap (\ x -> ! x ∘ x) p ≃〈 ap-by-equals !-inv-l p 〉 
              id ∘ ap (\ x -> id) p ≃〈 ∘-unit-l _ 〉 
              ap (\ x -> id) p ≃〈 ap-constant id p 〉 
              id ∎
  {- TODO
  ⊙-inv-r : (a : Ω2) → (a ⊙ ap ! a) ≃ id
  ⊙-inv-r a = {!!}
  -}

  ⊙-inv-r-! : (a : Ω2) -> a ⊙ (! a) ≃ id 
  ⊙-inv-r-! a = !-inv-r a ∘ ! (same a (! a))
  
  ⊙-inv-l-! : (a : Ω2) -> (! a) ⊙ a ≃ id 
  ⊙-inv-l-! a = !-inv-l a ∘ ! (same (! a) a)

  inverse-same : (a : Ω2) → ! a ≃ ap ! a
  inverse-same a = ! (cancels-is-inverse (ap ! a ∘ a ≃〈 same _ _ 〉 
                                          ap ! a ⊙ a ≃〈 ⊙-inv-l _ 〉 
                                          id ∎))


  -- ----------------------------------------------------------------------
  -- some consequences about canceling wrappers

  -- these next two are an instance of equate-wrappers below,
  -- but they're useful for proving rebase, which is useful for proving the
  -- more general form
  equate-wrappers' : ∀ {l} (α1 α2 : Path{Path{A} base base} id l) (β : Path{Path{A} base base} l l) 
                  -> ! α1 ∘ β ∘ α1 ≃ ! α2 ∘ β ∘ α2
  equate-wrappers'{l} = path-induction (\ l α1 -> (α2 : Path{Ω1} id l) (β : Path{Ω1} l l) -> ! α1 ∘ β ∘ α1 ≃ ! α2 ∘ β ∘ α2)
                                      (λ α2 β → ! (! α2 ∘ β ∘ α2 ≃〈 ap (λ x → ! α2 ∘ x) (abelian β α2) 〉 
                                                   ! α2 ∘ α2 ∘ β ≃〈 ∘-assoc (! α2) α2 β 〉
                                                   (! α2 ∘ α2) ∘ β ≃〈 ap (λ x → x ∘ β) (!-inv-l α2) 〉  
                                                   id ∘ β ∎))

  equate-wrappers-!R' : ∀ {l} (α1 α2 : Path{Path{A} base base} l id) (β : Path{Path{A} base base} l l ) 
                    -> α1 ∘ β ∘ ! α1 ≃ α2 ∘ β ∘ ! α2
  equate-wrappers-!R' α1 α2 β = ap (λ x → x ∘ β ∘ ! α2) (!-invol α2) ∘ equate-wrappers' (! α1) (! α2) β ∘ ! (ap (λ x → x ∘ β ∘ ! α1) (!-invol α1))

  rebase-PathPath : (l : Ω1) → Equiv (Path{Path{A} base base} id id) (Path{Path{A} base base} l l)
  rebase-PathPath l = improve (hequiv (ap (λ x → l ∘ x))
                                      (λ α → !-inv-l l ∘ ap (λ x → ! l ∘ x) α ∘ ! (!-inv-l l))
                                      (λ x → !-inv-l l ∘ ap (λ x' → ! l ∘ x') (ap (λ x' → l ∘ x') x) ∘ ! (!-inv-l l) ≃〈 ap (λ x' → !-inv-l l ∘ x' ∘ ! (!-inv-l l)) (! (ap-o (λ x' → ! l ∘ x') (λ x' → l ∘ x') x)) 〉 
                                             !-inv-l l ∘ ap (λ x' → ! l ∘ l ∘ x') x ∘ ! (!-inv-l l) ≃〈 ap (λ x' → !-inv-l l ∘ x' ∘ ! (!-inv-l l)) (ap-by-id{f = \ x' -> (! l ∘ l ∘ x')}  (λ x' → ! (∘-assoc (! l) l x') ∘ ! (ap (λ z → z ∘ x') (!-inv-l l)) ∘ ! (∘-unit-l x')) x) 〉 
                                             !-inv-l l ∘ ((! (∘-assoc (! l) l id) ∘ ! (ap (λ z → z) (!-inv-l l))) ∘ x ∘ ! (! (∘-assoc (! l) l id) ∘ ! (ap (λ z → z) (!-inv-l l)))) ∘ ! (!-inv-l l) ≃〈 FIXME _ 〉 
                                              (!-inv-l l ∘ (! (∘-assoc (! l) l id)) ∘ ! (ap (λ z → z) (!-inv-l l))) 
                                             ∘ x 
                                             ∘ ! (!-inv-l l ∘ ! (∘-assoc (! l) l id) ∘ ! (ap (λ z → z) (!-inv-l l))) ≃〈 equate-wrappers-!R' (!-inv-l l ∘ ! (∘-assoc (! l) l id) ∘ ! (ap (λ z → z) (!-inv-l l))) id x 〉 
                                             id ∘ x ∘ id ≃〈 ∘-unit-l x 〉 
                                             x ∎)
                                      (λ x → ap (λ x' → l ∘ x') (!-inv-l l ∘ ap (λ x' → ! l ∘ x') x ∘ ! (!-inv-l l)) ≃〈 FIXME _ 〉 
                                             (ap (λ x' → l ∘ x') (!-inv-l l) ∘ ap (λ x' → l ∘ x') (ap (λ x' → ! l ∘ x') x) ∘ ap (λ x' → l ∘ x') (! (!-inv-l l))) ≃〈 FIXME _ 〉 
                                             (ap (λ x' → l ∘ x') (!-inv-l l) ∘ ap (λ x' → l ∘ (! l ∘ x')) x ∘ ap (λ x' → l ∘ x') (! (!-inv-l l))) ≃〈 FIXME _ 〉 
                                             -- (ap (λ x' → l ∘ x') (!-inv-l l) ∘ ap (λ x' → l ∘ (! l ∘ x')) x ∘ ap (λ x' → l ∘ x') (! (!-inv-l l))) ≃〈 {!!} 〉 
                                             x ∎)) where
                  postulate FIXME : (A : Type) → A

  postulate -- FIXME just need to fill in the proof term
    rebase-PathPath-∘-back : ∀ {l} (α β : _) -> coe (! (ua (rebase-PathPath l))) (α ∘ β) ≃ coe (! (ua (rebase-PathPath l))) α ∘ coe (! (ua (rebase-PathPath l))) β
  -- rebase-PathPath-∘-back{l} α β = coe (! (ua (rebase-PathPath l))) (α ∘ β) ≃〈 ap≃ (transport-ua-back (rebase-PathPath l)) 〉 
  --                                (!-inv-l l ∘ ap (λ x → ! l ∘ x) (α ∘ β) ∘ ! (!-inv-l l)) ≃〈 {!!} 〉
  --                                (!-inv-l l ∘ (ap (λ x → ! l ∘ x) α ∘ ap (λ x → ! l ∘ x) β) ∘ ! (!-inv-l l)) ≃〈 {!!} 〉
  --                                ((!-inv-l l ∘ ap (λ x → ! l ∘ x) α ∘ ! (!-inv-l l)) ∘
  --                                 (!-inv-l l ∘ ap (λ x → ! l ∘ x) β ∘ ! (!-inv-l l))) ≃〈 {!!} 〉 
  --                                (coe (! (ua (rebase-PathPath l))) α ∘
  --                                    coe (! (ua (rebase-PathPath l))) β ∎)

  -- works for any l
  abelian-gen : ∀ {l} (a b : Path{Ω1} l l) → (a ∘ b) ≃ (b ∘ a)
  abelian-gen{l} a b = (coe-inv-2 (ua (rebase-PathPath l)) ∘
                          ap (λ x → coe (ua (rebase-PathPath l)) x)
                          (! (rebase-PathPath-∘-back b a))) ∘
                         ap (coe (ua (rebase-PathPath l)))
                         (abelian (coe (! (ua (rebase-PathPath l))) a)
                          (coe (! (ua (rebase-PathPath l))) b))
                         ∘ ! (coe-inv-2 (ua (rebase-PathPath l)) ∘
                              ap (λ x → coe (ua (rebase-PathPath l)) x)
                              (! (rebase-PathPath-∘-back a b)))

  equate-wrappers : ∀ {l1 l2} (α1 α2 : Path{Path{A} base base} l1 l2) (β : Path{Path{A} base base} l2 l2) 
                         -> ! α1 ∘ β ∘ α1 ≃ ! α2 ∘ β ∘ α2
  equate-wrappers{l1} {l2} = path-induction (\ l2 α1 -> (α2 : Path{Ω1} l1 l2) (β : Path{Ω1} l2 l2) -> ! α1 ∘ β ∘ α1 ≃ ! α2 ∘ β ∘ α2)
                                      (λ α2 β → ! (! α2 ∘ β ∘ α2 ≃〈 ap (λ x → ! α2 ∘ x) (abelian-gen β α2) 〉 
                                                   ! α2 ∘ α2 ∘ β ≃〈 ∘-assoc (! α2) α2 β 〉
                                                   (! α2 ∘ α2) ∘ β ≃〈 ap (λ x → x ∘ β) (!-inv-l α2) 〉  
                                                   id ∘ β ∎))

  equate-wrappers-!R : ∀ {l1 l2} (α1 α2 : Path{Path{A} base base} l2 l1) (β : Path{Path{A} base base} l2 l2) 
                    -> α1 ∘ β ∘ ! α1 ≃ α2 ∘ β ∘ ! α2
  equate-wrappers-!R α1 α2 β = ap (λ x → x ∘ β ∘ ! α2) (!-invol α2) ∘ equate-wrappers (! α1) (! α2) β ∘ ! (ap (λ x → x ∘ β ∘ ! α1) (!-invol α1))

  {-
      -- for reference, this is the minimal generalization of the IH that goes through
      -- for proving the interchange law
      ichange : (p q : Ω1) 
               → (a : Path p q) (r : Ω1) (b : Path q r) (p' q' : Ω1) 
                 (c : Path p' q') (r' : Ω1) (d : Path q' r') 
               → Path (aptrans (trans a b) (trans c d)) (trans (aptrans a c) (aptrans b d))
      ichange p q a = jay
                        (λ p' q' a' →
                           (r : Ω1) (b : Path q' r) (p0 q0 : Ω1) (c : Path p0 q0) (r' : Ω1)
                           (d : Path q0 r') →
                           Path (aptrans (trans a' b) (trans c d))
                           (trans (aptrans a' c) (aptrans b d)))
                        a
                        (λ pq r b →
                           jay
                           (λ pq' r' b' →
                              (p' q' : Ω1) (c : Path p' q') (r0 : Ω1) (d : Path q' r0) →
                              Path (aptrans (trans id b') (trans c d))
                              (trans (aptrans id c) (aptrans b' d)))
                           b
                           (λ pqr p' q' c →
                              jay
                              (λ p0 q0 c' →
                                 (r' : Ω1) (d : Path q0 r') →
                                 Path (aptrans id (trans c' d))
                                 (trans (aptrans id c') (aptrans id d)))
                              c
                              (λ p'q' r' d →
                                 jay
                                 (λ p'q0 r0 d' →
                                    Path (aptrans id (trans id d'))
                                    (trans id (aptrans id d')))
                                 d (λ _ → id))))
  -}
      
      -- ENH: can you relax the restriction that the base point is identity?
      -- abelian' : {loop : Path base base} {a b : Path loop loop} → Path (trans a b) (trans b a)

  -- shorter proof by Favonia
  module BifunctorLemma where

    bifunctor-lemma : ∀ {A B C : Set} 
                        (f : A -> B -> C)
                        {a a' : A} {b b' : B}
                        (α : a ≃ a') (β : b ≃ b')
                     -> (ap (\ x -> f a' x) β ∘ ap (\ x -> f x b) α)
                      ≃ (ap (\ x -> f x b') α ∘ ap (\ x -> f a x) β)
    bifunctor-lemma f id id = id 

    bifunctor-lemma-∘ : (α β : Ω2)
                     -> (ap (\ x -> id ∘ x) β ∘ ap (\ x -> x ∘ id) α)
                      ≃ (ap (\ x -> x ∘ id) α ∘ ap (\ x -> id ∘ x) β) 
    bifunctor-lemma-∘ α β = bifunctor-lemma _∘_ {id} {id} {id} {id} α β

    commute : (α β : Ω2) -> (α ∘ β) ≃ (β ∘ α)
    commute α β = α ∘ β                                              ≃〈 ap (λ f → f α ∘ β) (! is-id-ap-2) 〉
                  ap (λ x → x ∘ id) α ∘ β                        ≃〈 ap (λ f → ap (λ x → x ∘ id) α ∘ f β) (! is-id-ap-1) 〉
                  ap (λ x → x ∘ id) α ∘ ap (λ x → id ∘ x) β  ≃〈 ! (bifunctor-lemma-∘ α β) 〉 
                  ap (λ x → id ∘ x) β ∘ ap (\ x -> x ∘ id) α ≃〈 ap (λ f → f β ∘ ap (λ x → x ∘ id) α) is-id-ap-1 〉 
                  β ∘ ap (\ x -> x ∘ id) α                       ≃〈 ap (λ f → β ∘ f α) is-id-ap-2 〉 
                  β ∘ α ∎ where
      is-id-ap-1 : ap (\ (x : Ω1) -> id ∘ x) ≃ (\ (x : Ω2) -> x)
      is-id-ap-1 = λ≃ (\ x → ∘-unit-l x ∘ ap-by-id (\ y → ! (∘-unit-l y)) x) 
  
      is-id-ap-2 : ap (\ (x : Ω1) -> x ∘ id) ≃ (\ (x : Ω2) -> x)
      is-id-ap-2 = λ≃ ap-id -- cancels definitionally on this side

 