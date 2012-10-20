{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open Paths
open S¹
open T
open NDPair


module applications.torus2.TS1S1-helpers where

  g : {A B : Set} 
    -> (α : ∀{X} -> (A -> X) ≃ (B -> X))
    -> (A -> B)
  g {A} {B} α = subst (λ x → x) (! (α {B})) (λ (x : B) → x)

  g-o-f-id : {A B : Set} (f : B -> A)
           -> (α : ∀{X} -> (A -> X) ≃ (B -> X)) -- Hom (A, X) = Hom (B, X)
           -> (∀ {X} -> subst (λ x → x) (α {X}) ≃ (λ g' → g' o f))
           -> ((g α) o f ≃ (λ (x : B) → x))
  g-o-f-id {A} {B} f α s = λ≃ (λ b → 
    (g α o f) b
             -- By assumption in premises
             ≃〈 sym (resp (λ f' → f' (g α) b) (s {B})) 〉
    subst (λ x → x) (α {B}) (g α) b
             -- Simple rewrite
             ≃〈 Refl 〉
    subst (λ x → x) (α {B}) (subst (λ x → x) (! (α {B})) (λ x → x)) b 
             -- Fusion of substs
             ≃〈 ((resp (λ y → y (λ x → x) b)
                       (sym (subst-∘ (λ x → x) (α {B}) (! (α {B})))))) 〉
    subst (λ x → x) (α {B} ∘ (! (α {B}))) (λ x → x) b
             -- Cancel the (α {B})'s
             ≃〈 resp (λ y → subst (λ x → x) y (λ z → z) b) (!-inv-r (α {B})) 〉
    b ∎)

  f-o-g-o-f : {A B : Set} (f : B -> A)
            -> (α : ∀{X} -> (A -> X) ≃ (B -> X))
            -> (∀ {X} -> subst (λ x → x) (α {X}) ≃ (λ g' → g' o f))
            -> (f o ((g α) o f) ≃ f)
  f-o-g-o-f {A} {B} f α s = λ≃ (λ b → 
    (f o (g α o f)) b
            -- By g-o-f-id
            ≃〈 resp (λ x → (f o x) b) (g-o-f-id {A} {B} f α s) 〉
    (f b) ∎)

  subst-fg-id : {A B : Set} (f : B -> A)
             -> (α : ∀{X} -> (A -> X) ≃ (B -> X))
             -> (∀ {X} -> subst (λ x → x) (α {X}) ≃ (λ g' → g' o f))
             -> (f o (g α)) o f ≃ f
             -> (subst (λ x → x) (α {A}) (f o (g α)) ≃ subst (λ x → x) (α {A}) (λ (x : A) → x))
  subst-fg-id {A} {B} f α s p = λ≃ (λ b → 
    subst (λ x → x) (α {A}) (f o g α) b 
            -- By assumption
            ≃〈 resp (λ f' → f' (f o g α) b) (s {A}) 〉
    ((f o (g α)) o f) b
            -- By f-o-g-o-f
            ≃〈 resp (λ y → y b) p 〉
    f b
            -- By assumption
            ≃〈 sym (resp (λ f' → f' (λ x → x) b) (s {A})) 〉
    (subst (λ x → x) (α {A}) (λ (x : A) → x) b) ∎)

  f-o-g-id : {A B : Set} (f : B -> A)
           -> (α : ∀ {X} -> (A -> X) ≃ (B -> X))
           -> (∀ {X} -> subst (λ x → x) (α {X}) ≃ (λ g' → g' o f)) 
           -> (f o g α) ≃ (λ (x : A) → x)
  f-o-g-id {A} {B} f α s = λ≃ (λ a → 
    (f o g α) a 
            -- by expanding the Refl (subst C Refl f = f)
            ≃〈 resp (λ p → subst (λ x → x) p (f o g α) a) 
                    (sym (!-inv-l (α {A}))) 〉
    subst (λ x → x) (!(α {A}) ∘ (α {A})) (f o g α) a
            -- unfusion the substs
            ≃〈 resp (λ p → p (f o g α) a) 
                   (subst-∘ (λ x → x) (! (α {A})) (α {A})) 〉
    subst (λ x → x) (! (α {A})) (subst (λ x → x) (α {A}) (f o g α)) a
            -- by subst-fg-id
            ≃〈 resp
                  (λ f' → subst (λ x → x) (! (α {A})) f' a)
                  (subst-fg-id f α s (f-o-g-o-f f α s)) 〉
    subst (λ x → x) (! (α {A})) (subst (λ x → x) (α {A}) (λ (x : A) → x)) a
            -- fusion the subst
            ≃〈 resp (λ p → p (λ x → x) a) 
                    (sym (subst-∘ (λ x → x) (! (α {A})) (α {A}))) 〉
    subst (λ x → x) (!(α {A}) ∘ (α {A})) (λ x → x) a
            -- cancel the (α {A})'s
            ≃〈 resp (λ p → subst (λ x → x) p (λ x → x) a)
                    (!-inv-l (α {A})) 〉
    a ∎)

  precomp-equiv : {A B : Set} (f : B -> A) 
                -> (α : ∀{X} -> (A -> X) ≃ (B -> X))
                -> (∀{X} -> subst (λ x → x) (α {X}) ≃ (λ g → g o f))
                -> A ≃ B
  -- prove that f is an iso, then use Univalence Axiom
  precomp-equiv f α s = sym (ua (isoToAdj (f , isiso (g α) (λ y → app≃ (f-o-g-id f α s))
                                                 (λ x → app≃ (g-o-f-id f α s)))))


  -- This is probably already implemented somewhere, but more practice is good
  -- Basically the proof that (A × B -> C) ≃ (A -> C^B)
  curry : ∀ {A B C : Set} -> (A × B -> C) -> (A -> B -> C)
  curry f = \ x y → f (x , y)

  curry-uncurry-id : ∀ {A B C : Set} -> (f : A -> B -> C)
                  -> (curry o uncurry) f ≃ f
  curry-uncurry-id f = λ≃ (λ x → λ≃ (λ x' → Refl))

  uncurry-curry-id : ∀ {A B C : Set} -> (f : A × B -> C)
                  -> (uncurry o curry) f ≃ f
  uncurry-curry-id f = λ≃ (λ x → Refl)

  curry-iso : ∀ {A B C : Set} -> (A × B -> C) ≃ (A -> B -> C)
  curry-iso = ua (isoToAdj (curry , isiso uncurry curry-uncurry-id uncurry-curry-id))

  -- Generalized associativity proof for dependent sums
  dep-sum-assoc : {X : Set} 
                -> {A : X -> Set}
                -> {B : (Σ[ x ∶ X ] (A x)) -> Set}
                -> (Σ[ p ∶ (Σ[ x ∶ X ] (A x)) ] (B p))
                -> Σ[ x  ∶ X ] (Σ[ l1 ∶ A x ] (B (x , l1)))
  dep-sum-assoc ((fst , snd) , snd') = fst , (snd , snd')

  dep-sum-unassoc : {X : Set}
                 -> {A : X -> Set}
                 -> {B : (Σ[ x ∶ X ] (A x)) -> Set}
                 -> Σ[ x ∶ X ] (Σ[ l1 ∶ A x ] (B (x , l1)))
                 -> (Σ[ p ∶ (Σ[ x ∶ X ] (A x)) ] (B p))
  dep-sum-unassoc (fst , fst' , snd) = (fst , fst') , snd

  dep-sum-assoc-equiv : {X : Set}
                      -> {A : X -> Set}
                      -> {B : (Σ[ x ∶ X ] (A x)) -> Set}
                      -> (Σ[ p ∶ (Σ[ x ∶ X ] (A x)) ] (B p))
                      ≃ (Σ[ x  ∶ X ] (Σ[ l1 ∶ A x ] (B (x , l1))))
  dep-sum-assoc-equiv = ua (isoToAdj (dep-sum-assoc , 
                                      isiso dep-sum-unassoc 
                                            (λ y → Refl) 
                                            (λ x → Refl)))

  -- Isomorphism to perform a resp inside Σ's
  Σ-A-A' : {X : Set}
        -> {A A' : X -> Set}
        -> (c : A ≃ A')
        -> (Σ[ x ∶ X ] A x)
        -> (Σ[ x ∶ X ] A' x)
  Σ-A-A' c (fst , snd) = fst , (subst (λ f' → f' fst) c snd)

  Σ-A-A'-id : {X : Set}
           -> {A A' : X -> Set}
           -> (c : A ≃ A')
           -> (Σ-A-A' c) o (Σ-A-A' (! c)) ≃ (λ x → x)
  Σ-A-A'-id c = λ≃ (λ x → 
    (fst x ,
       subst (λ f' → f' (fst x)) c
       (subst (λ f' → f' (fst x)) (! c) (snd x)))
              ≃〈 resp (λ p → fst x , p (snd x)) 
                      (sym (subst-∘ (λ f' → f' (fst x)) c (! c))) 〉 
    (fst x , subst (λ f' → f' (fst x)) (c ∘ (! c)) (snd x))
              ≃〈 resp (λ p → fst x , subst (λ f' → f' (fst x)) p (snd x)) 
                      (!-inv-r c) 〉
    x ∎)

  Σ-A'-A-id : {X : Set}
           -> {A A' : X -> Set}
           -> (c : A ≃ A')
           -> (Σ-A-A' (! c)) o (Σ-A-A' c) ≃ (λ x → x)
  Σ-A'-A-id c = λ≃ (λ x → 
    (fst x ,
       subst (λ f' → f' (fst x)) (! c)
       (subst (λ f' → f' (fst x)) c (snd x)))
              ≃〈 resp (λ p → fst x , p (snd x)) 
                      (sym (subst-∘ (λ f' → f' (fst x)) (! c) c)) 〉 
    (fst x , subst (λ f' → f' (fst x)) ((! c) ∘ c) (snd x))
              ≃〈 resp (λ p → fst x , subst (λ f' → f' (fst x)) p (snd x)) 
                      (!-inv-l c) 〉
    x ∎)

  Σ-resp : {X : Set}
             -> {A A' : X -> Set}
             -> (c : A ≃ A')
             -> (Σ[ x ∶ X ] A x) ≃ (Σ[ x ∶ X ] A' x)
  Σ-resp c = ua (isoToAdj (Σ-A-A' c , 
                           isiso (Σ-A-A' (! c)) 
                                 (λ y → app≃ (Σ-A-A'-id c)) 
                                 (λ x → app≃ (Σ-A'-A-id c))))

  -- Moving ! between sides of an Id
  !-left : {X : Set}
        -> {M N : X}
        -> (p : Id M N)
        -> (q : Id M M)
        -> (r : Id N N)
        -> Id (p ∘ q ∘ ! p) r ≃ Id (p ∘ q) (r ∘ p)
  !-left Refl q r = Refl

{-
  Id-Σ-subst : {X : Set}
            -> (x : X)
            -> (l1 : Id x x)
            -> Id{Σ \ x -> Id x x} (x , l1) (x , l1)
            -> (Σ[ l2 ∶ Id x x ] Id (subst (λ x → Id x x) l2 l1) l1)
  Id-Σ-subst x l1 p = l1 , (snd≃ (respd snd p))

  subst-Id-Σ : {X : Set}
            -> (x : X)
            -> (l1 : Id x x)
            -> (Σ[ l2 ∶ Id x x ] Id (subst (λ x → Id x x) l2 l1) l1)
            -> Id (x , l1) (x , l1)
  subst-Id-Σ x l1 (fst , snd) = pair≃ fst snd
-}