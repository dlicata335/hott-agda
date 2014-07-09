

{-# OPTIONS --type-in-type --copatterns --without-K #-}

open import NoFunextPrelude

module Stream where

  record Stream (A : Type) : Type where
    coinductive
    field
      head : A
      tail : Stream A
  open Stream
  
  map : {A B : Type} → (A → B) → (Stream A → Stream B)
  head (map f s) = f (head s)
  tail (map f s) = map f (tail s)

  postulate 
    map-id : {A : Type} → map {A} (\ x -> x) == (\ s -> s)
    map-o  : {A B C : Type} (g : B → C) (f : A → B) → map g o map f == map (g o f)

  transport-Stream : {A B : Type} → (p : A == B) → transport Stream p == map (coe p)
  transport-Stream id = ! map-id
  
  record Bisim {A : Type} (xs : Stream A) (ys : Stream A) : Type where
    coinductive
    field 
      heads : head xs == head ys
      tails : Bisim (tail xs) (tail ys)
  open Bisim
  
  Bisim2 : Type → Type
  Bisim2 A = (Σ \ xsys -> Bisim{A} (fst xsys) (snd xsys))
  
  module LastStep (A : Type) where
  
    left : Stream (Paths A) → Stream A
    left = map (fst o fst) 
  
    right : Stream (Paths A) → Stream A
    right = map (snd o fst)
  
    middle : (s : Stream (Paths A)) → Bisim (left s) (right s)
    Bisim.heads (middle s) = (snd (head s))
    Bisim.tails (middle s) = (middle (tail s))
  
    to : Stream (Paths A) → Bisim2 A
    to s = ((left s , right s) , middle s)
  
    from : Bisim2 A → Stream (Paths A)
    head (from ((s1 , s2) , b)) = (head s1 , head s2) , Bisim.heads b
    tail (from p) = from ((tail (fst (fst p)) , tail (snd (fst p))) , Bisim.tails (snd p))
  
    from-to : (p : _) → from (to p) == p
    from-to p = {!!}
  
    to-from : (p : _) → to (from p) == p
    to-from ((xs , ys) , b) = {!!}
  
    eqv : Equiv (Stream (Paths A)) (Bisim2 A)
    eqv = improve (hequiv to from from-to to-from)
  
  extt : {A : Type} → Equiv (Paths (Stream A)) (Bisim2 A)
  extt {A} =   Paths (Stream A) ≃〈 contract-Paths≃ {Stream A} 〉
               Stream A ≃〈 coe-equiv (ap Stream (! (ua (contract-Paths≃ {A})))) 〉
               Stream (Paths A) ≃〈 LastStep.eqv A 〉
               (Bisim2 A ∎∎)
  
  extt-id : {A : Type} (s : Stream A) → fst (fst extt ((s , s) , id)) == (s , s)
  extt-id s = fst
                (LastStep.to _
                 (coe (ap Stream (! (ua contract-Paths≃)))
                  (fst contract-Paths≃ ((s , s) , id))))
                =〈 id 〉
              fst
                (LastStep.to _
                 (coe (ap Stream (! (ua contract-Paths≃))) s)) =〈 ap (λ f → fst (LastStep.to _ (f s))) (transport-Stream (! (ua contract-Paths≃)) ∘ ! (transport-ap-assoc' (λ X → X) Stream (! (ua contract-Paths≃)))) 〉
              fst
                (LastStep.to _
                 (map (coe (! (ua contract-Paths≃))) s)) =〈 ap (λ f → fst (LastStep.to _ (map f s))) (type=β! contract-Paths≃) 〉
              fst
                (LastStep.to _
                 (map (\ x -> ((x , x) , id)) s)) =〈 pair= (ap= map-id ∘ ap= (map-o (fst o fst) (λ x → (x , x) , id))) ((ap= map-id ∘ ap= (map-o (snd o fst) (λ x → (x , x) , id))) ∘ ap= (transport-constant (ap= map-id ∘ ap= (map-o (fst o fst) (λ x → (x , x) , id))))) 〉
              ((s , s) ∎)
  
  preserves-fst : ∀ {A} (α : Paths (Stream A)) → fst (fst extt α) == fst α
  preserves-fst ((s , .s) , id) = extt-id s
  
  ext : {A : Type} (s1 s2 : Stream A) → Equiv (s1 == s2) (Bisim s1 s2)
  ext s1 s2 = fiberwise-equiv-from-total≃ extt preserves-fst (s1 , s2)
