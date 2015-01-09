
{-# OPTIONS --type-in-type --copatterns --without-K #-}

open import lib.First
open import lib.Prods
open import lib.Paths

module lib.Stream where

  Paths : Type → Type
  Paths A = Σ \ (p : A × A) → fst p == snd p

  record Stream (A : Type) : Type where
    coinductive
    field
      head : A
      tail : Stream A
  open Stream

  {-# NO_TERMINATION_CHECK #-}
  unfold : {A : Type} {X : Type} → (X → A × X) → X → Stream A 
  head (unfold f x) = fst (f x)
  tail (unfold f x) = unfold f (snd (f x))

  postulate
      unfoldη : {A : Type} {X : Type} (f : X → A × X) (s : X → Stream A)
             → ((x : X) → head (s x) == fst (f x))
             → ((x : X) → tail (s x) == s (snd (f x)))
             → (x : X) → s x == unfold f x
      -- FIXME probably should be some coherence cell, too?

  map : {A B : Type} → (A → B) → (Stream A → Stream B)
  map {A} f s = unfold {X = Stream A} (λ x → f (head x) , tail x) s

  map-id : {A : Type} → (s : Stream A) → map (\ x -> x) s == s
  map-id s = ! (unfoldη _ (\ s -> s) (λ _ → id) (λ x → id) _)

  map-o  : {A B C : Type} (g : B → C) (f : A → B) → (s : Stream A)
         → map (g o f) s == map g (map f s)
  map-o g f s = ! (unfoldη (λ x → (g o f) (head x) , tail x) (map g o map f) (λ _ → id) (λ _ → id) _)

  map-unfold  : {A B X : Type} (f : A → B) (g : X → A × X) (x : X)
                → map f (unfold g x) == unfold (\ x' → f (fst (g x')) , (snd (g x'))) x
  map-unfold f g x = unfoldη (λ x' → f (fst (g x')) , snd (g x')) (λ x₁ → map f (unfold g x₁)) (λ _ → id) (λ _ → id) _

  Bisim : {A : Type} (xs : Stream A) (ys : Stream A) → Type 
  Bisim {A} xs ys = Σ \(p : Stream (Paths A)) → (map (fst o fst) p == xs) × (map (snd o fst) p == ys)

  id-bisim-s : {A : Type} (xs : Stream A) → Stream (Paths A)
  id-bisim-s xs = map (\x -> ((x , x) , id)) xs

  id-bisim : {A : Type} (xs : Stream A) → Bisim xs xs
  id-bisim xs = id-bisim-s xs , 
                map-id _ ∘ ! (map-o (fst o fst) (λ x → (x , x) , id) _) , 
                map-id _ ∘ ! (map-o (snd o fst) (λ x → (x , x) , id) _)

  path-to-bisim : {A : Type} {xs ys : Stream A} → xs == ys → Bisim xs ys
  path-to-bisim id = id-bisim _

  bisim-to-path : {A : Type} {xs ys : Stream A} → Bisim xs ys → xs == ys
  bisim-to-path (s , (id , id)) = 
    ap {M = fst o fst} {N = snd o fst} (λ f → unfold (λ x → f (head x) , tail x) s) (λ≃ (λ x → snd x))

  comp1 : {A : Type} {xs ys : Stream A} (p : xs == ys) 
        → bisim-to-path (path-to-bisim p) == p
  comp1 id = {!!}

  comp2 : {A : Type} {xs ys : Stream A} (p : Bisim xs ys) 
        → path-to-bisim (bisim-to-path p) == p
  comp2 (s , (id , id)) = {!!}

  Bisim-heads : {A : Type} {xs ys : Stream A} → Bisim xs ys → head xs == head ys
  Bisim-heads (ps , (id , id)) = snd (head ps)

  Bisim-tails : {A : Type} {xs ys : Stream A} → Bisim xs ys → Bisim (tail xs) (tail ys)
  Bisim-tails (ps , (id , id)) = (tail ps , id , id)

  Bisim-unfold-stream : {A : Type} (X : Stream A → Stream A → Type)
               → (∀ {xs ys} → X xs ys → ((head xs) == (head ys)) × X (tail xs) (tail ys))
               → ∀ (xs ys : Stream A) → X xs ys → Stream (Paths A)
  Bisim-unfold-stream X f xs ys x = 
    unfold {X = Σ \ xsys → X (fst xsys) (snd xsys)} 
           (λ {((xs , ys) , seed) → (_ , fst (f seed)) , _ , snd (f seed)})
           ((xs , ys) , x)

  Bisim-unfold : {A : Type} (X : Stream A → Stream A → Type)
               → (∀ {xs ys} → X xs ys → ((head xs) == (head ys)) × X (tail xs) (tail ys))
               → ∀ (xs ys : Stream A) → X xs ys → Bisim xs ys
  Bisim-unfold X f xs ys x = Bisim-unfold-stream X f xs ys x , 
                               (!
                                (unfoldη {X = Σ \ xsys → X (fst xsys) (snd xsys)} 
                                 (λ x' →
                                    head (fst (fst x')) ,
                                    (tail (fst (fst x')) , tail (snd (fst x'))) , snd (f (snd x')))
                                 (fst o fst) (λ _ → id) (λ _ → id) ((xs , ys) , x))) ∘
                               map-unfold (fst o fst)
                               (λ { ((xs , ys) , seed) → (_ , fst (f seed)) , _ , snd (f seed) })
                               _ , 
                             !
                               (unfoldη {X = Σ (λ xsys → X (fst xsys) (snd xsys))} _ (snd o fst)
                                (λ _ → id) (λ _ → id) ((xs , ys) , x))
                               ∘
                               map-unfold (snd o fst)
                               (λ { ((xs , ys) , seed) → (_ , fst (f seed)) , _ , snd (f seed) })
                               _
  

  module HFinal (A : Type) where
    S-Alg = Σ \ (X : Type) → X → A × X

    S-AlgStream : S-Alg
    S-AlgStream = (Stream A , (λ s → head s , tail s))
    
    Hom : S-Alg -> S-Alg -> Type
    Hom (X , f) (Y , g) = Σ (λ (h : X → Y) → g o h == (λ p → fst p , h (snd p)) o f)

    hfinal : ∀ Y → Contractible (Hom Y S-AlgStream)
    hfinal (Y , g) = ((unfold g) , id) , 
                     (λ u → pair≃ (! (λ≃ (unfoldη g (fst u) (λ y → ap fst (ap≃ (snd u) {y}))
                                                            (λ y → snd≃ (ap≃ (snd u) {y}) ∘
                                                                     ! (ap≃ (transport-constant (fst≃ (ap≃ (snd u)))))))))
                                  {!!})

