{-# OPTIONS --type-in-type --without-K #-}

-- pushout of two maps f and g.
-- e.g. S2 = Pushout {S1}{Unit}{Unit} cst cst
--      has north, south, and a circle of points in between

open import lib.First
open import lib.NConnected
open import lib.Prods
open import lib.Sums
open import lib.Functions
open import lib.Paths 
open import lib.NType
open import lib.Universe
open import lib.Truncations
open import lib.WEq
open Truncation
open import lib.cubical.PathOver
open import lib.cubical.Square
open import lib.cubical.Cube

module lib.Pushout where

  module Pushout where

    module P where
      private
        data Pushout' {ZZ X Y : Type} (f : ZZ → X) (g : ZZ → Y) : Type where
          inl' : X → Pushout' f g 
          inr' : Y → Pushout' f g

      Pushout : {ZZ X Y : Type} (f : ZZ → X) (g : ZZ → Y) → Type 
      Pushout = Pushout'

      inl : ∀ {ZZ X Y}{f : ZZ → X}{g : ZZ → Y} → X → Pushout f g
      inl = inl'

      inr : ∀ {ZZ X Y}{f : ZZ → X}{g : ZZ → Y} → Y → Pushout f g
      inr = inr'

      postulate {- HoTT Axiom -}
        glue : ∀ {ZZ X Y} {f : ZZ → X}{g : ZZ → Y} (z : ZZ) → Path{Pushout f g} (inl (f z)) (inr (g z))

      Pushout-rec : {ZZ X Y C : Type} 
                    {f : ZZ → X} {g : ZZ → Y}
                    (b1 : X → C)
                    (b3 : Y → C)
                    (glue' : (z : ZZ) → (b1 (f z)) ≃ b3 (g z))
                  → Pushout f g → C
      Pushout-rec b1 _ _ (inl' x) = b1 x
      Pushout-rec _ b3 _ (inr' y) = b3 y

      postulate {- HoTT Axiom -}
        βglue/rec : {ZZ X Y C : Type}
                    {f : ZZ → X} {g : ZZ → Y}
                    (b1 : X → C)
                    (b2 : Y → C)
                    (glue' : (z : ZZ) → Path (b1 (f z)) (b2 (g z))) →
                    (z : ZZ) → Path (ap (Pushout-rec b1 b2 glue') (glue z)) (glue' z)

      Pushout-elim : {ZZ X Y : Type} 
                    {f : ZZ → X} {g : ZZ → Y}
                    (C : Pushout f g -> Type)
                    (b1 : (x : X) → C (inl x))
                    (b3 : (y : Y) → C (inr y))
                    (glue' : (z : ZZ) → PathOver C (glue z) (b1 (f z)) (b3 (g z)))
                  → (p : Pushout f g) → C p
      Pushout-elim _ b1 _ _ (inl' x) = b1 x
      Pushout-elim _ _ b3 _ (inr' y) = b3 y

    open P public

    oops : {ZZ X Y : Type} (f : ZZ → X) (g : ZZ → Y) → (x x' : X) → Path {Pushout f g} (inl x) (inl x') → x == x'
    oops f g x .x id = id

    Wedge : {A B : Type} (a0 : A) (b0 : B) → Type
    Wedge {A}{B} a0 b0 = Pushout {Unit}{A}{B} (\ _ -> a0) (\ _ -> b0)

    wedge-to-prod : ∀ {A B} {a0 : A} {b0 : B} → (Wedge a0 b0) → A × B
    wedge-to-prod {a0 = a0} {b0 = b0} = Pushout-rec (λ a → a , b0) (λ b → a0 , b) (\ _ -> id) 

    module WedgeToProd {A B : Type} {m n : _} (a0 : A) (b0 : B) (cA : Connected (S m) A) (cB : Connected (S n) B) where

      i = wedge-to-prod {A}{B}{a0}{b0}
    
      private 
        for-fixed-a : A → Type 
        for-fixed-a a = (Extensions.Extensions B b0 (\ b -> Trunc (plus2 m n) (HFiber i (a , b))) [ inl a , id ])
        
        for-fixed-a-level : (a : A) → NType m (for-fixed-a a)
        for-fixed-a-level a = Extensions.level cB b0 (λ b → Trunc (plus2 m n) (HFiber i (a , b)) , Trunc-level) [ inl a , id ]
        
        fix-a0-square-backwards : PathOver (λ x → Path (i x) (a0 , b0)) (glue <>) id id
        fix-a0-square-backwards = (PathOver=.in-PathOver-= (whisker-square id (! (βglue/rec _ _ _ _)) (! (ap-constant _ _)) id (inverses-square id id)))
        
        fix-a0-square : PathOver (λ x → Path (i x) (a0 , b0)) (! (glue <>)) id id
        fix-a0-square = !o fix-a0-square-backwards
        
        fix-a0 : for-fixed-a a0
        fix-a0 = (λ b → [ inr b , id ]) , ap [_] (pair= (! (glue <>)) fix-a0-square)
        
        extend-a : (x : A) → Extensions.Extensions B b0 (λ b → Trunc (plus2 m n) (HFiber i (x , b))) [ inl x , id ]
        extend-a = Connected.everywhere m {A} {a0} cA (\ a → _ , for-fixed-a-level a) fix-a0
        
        extend-a-β : Id (extend-a a0) fix-a0
        extend-a-β = (Connected.β m cA (λ a₁ → Extensions.Extensions B b0 (λ b₁ → Trunc (plus2 m n) (HFiber i (a₁ , b₁))) [ inl a₁ , id ] , for-fixed-a-level a₁) fix-a0)

      -- could also use the UMP and use wedge-elim; this is basically repeating that code
        connected' : ConnectedMap (plus2 m n) i
        connected' (a , b) = ntype (fst (extend-a a) b , 
                                 Trunc-elim _ (λ _ → path-preserves-level Trunc-level) 
                                              (λ hi → path-induction
                                                        (λ ab sndhi →
                                                           Path (fst (extend-a (fst ab)) (snd ab)) [ fst hi , sndhi ])
                                                        (for-wedge (fst hi)) (snd hi))) where
      
         for-wedge : (w : Wedge a0 b0) → Path (fst (extend-a (fst (i w))) (snd (i w))) [ w , id ]
         for-wedge = Pushout-elim _ (λ a → snd (extend-a a)) 
                              (λ b → ap (λ x → fst x b) extend-a-β)
                              (λ <> → over-ap-o -- trick: do a little reassociation dance to reduce the i on glue before introducing the square; makes things much easier
                                        (λ (k : Σ (λ ab → HFiber i ab)) → 
                                           Path {Trunc (plus2 m n) (HFiber i (fst k))} ((λ p → fst (extend-a (fst p)) (snd p)) (fst k)) [ snd k ])
                                        {θ1 = λ z → i z , z , id} (changeover _ red (over-o-ap
                                                                                       (λ k → Path (fst (extend-a (fst (fst k))) (snd (fst k))) [ snd k ])
                                                                                       (PathOver=.in-PathOver-= (fst cohcube))))) where

           coh1 : ∀ {A B} {a0 a1 : A} {f : A → B} (p : f a0 == f a1) 
                → ap (λ (v : B × A) → f (snd v)) (pair= (! p) (in-PathOver-constant id)) == id
           coh1 {f = f} p = ap (ap f) (Σ=β2-ND (! p) id) ∘ ap-o f snd (pair= (! p) (in-PathOver-constant id))
           -- ENH this must be an instance of something
           coh : ∀ {A B} {a0 a1 : A} {f : A → B} (g : a0 == a1) (p : f a0 == f a1) (b1 : ap f g == p)
                 → Path{Path {Σ \ (b : B) → Σ \ (a : A) → f a == b} _ _} 
                        (ap (\ x → f a0 , x) (pair= g (PathOver=.in-PathOver-= (whisker-square id (! b1) (! (ap-constant (f a0) g)) id (inverses-square id p)))))
                        (pair= (! p) (pair=o (in-PathOver-constant id) 
                                             (PathOver=.in-PathOver-= 
                                               (whisker-square id (! (coh1 {f = f} p )) (! (Σ=β1 _ _)) id connection2)))
                         ∘ ap (λ z → f z , z , id) g)
           coh id .id id = id

           red : ap (λ x → (a0 , b0) , x) (pair= (glue <>) fix-a0-square-backwards) == ap (λ z → i z , z , id) (glue <>)
           red = ∘-unit-l (ap (λ z → i z , z , id) (glue <>)) ∘ coh {f = i} (glue <>) id (βglue/rec _ _ _ _)
      
           cohcube : Σ \ s → Cube s (PathOver=.out-PathOver-= (apdo snd extend-a-β))
                                    hrefl-square 
                                    (whisker-square (! (ap-constant _ (pair= (glue <>) fix-a0-square-backwards))) id id id connection) 
                                    (whisker-square id id id (! (ap-constant _ extend-a-β)) 
                                      (disc-to-square ((ap (ap [_]) (!-inv-l (pair= (glue <>) fix-a0-square-backwards)) ∘
                                                       ! (ap (λ x → ap [_] (x ∘ pair= (glue <>) fix-a0-square-backwards)) (!Σ _ fix-a0-square-backwards))) ∘
                                                       ! (ap-∘ [_] (pair= (! (glue <>)) fix-a0-square) (pair= (glue <>) fix-a0-square-backwards))))) 
                                    connection2
           cohcube = fill-cube-left _ _ _ _ _ 

      abstract -- PERF
        connected : ConnectedMap (plus2 m n) i
        connected = connected'
