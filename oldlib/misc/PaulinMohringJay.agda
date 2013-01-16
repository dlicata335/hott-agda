
module PaulinMohringJay where

   data Id {A : Set} : A -> A -> Set where
     Refl : {a : A} -> Id a a

   -- standard J
   jay : {A : Set} (C : (x y : A) -> Id x y -> Set)
       -> {M N : A} -> (P : Id M N)
       -> ((x : A) -> C x x Refl)
       -> C M N P
   jay _ Refl b = b _

   -- Paulin-Mohring "one-sided" jay
   jay1 : {A : Set} {M : A} (C : (x : A) -> Id M x -> Set)
       -> {N : A} -> (P : Id M N)
       -> (C M Refl)
       -> C N P
   jay1 _ Refl b = b

   -- easy direction
   jayfrompm : {A : Set} (C : (x y : A) -> Id x y -> Set)
       -> {M N : A} -> (P : Id M N)
       -> ((x : A) -> C x x Refl)
       -> C M N P
   jayfrompm {A} C {M}{N} P b = jay1 (λ x (p : Id M x) → C M x p) P (b M)

   -- other direction is harder: 
   -- one way to do it is to use J into Set1 to derive Paulin-Mohring J into Set

   large-jay : {A : Set} (C : (x y : A) -> Id x y -> Set1)
       -> {M N : A} -> (P : Id M N)
       -> ((x : A) -> C x x Refl)
       -> C M N P
   large-jay _ Refl b = b _

   pmfromjay : {A : Set} {M : A} (C : (N' : A) -> Id M N' -> Set)
       -> {N : A} -> (P : Id M N)
       -> (C M Refl)
       -> C N P
   pmfromjay {A}{M} C {N} P b = 
       (large-jay (λ M' N' (P' : Id M' N') → (C' : (N'' : A) → Id M' N'' → Set) → C' M' Refl → C' N' P') 
            P 
            (λ M' C' b' → b'))
       C b

   -- or not
   subst : {A : Set} (p : A -> Set) {x y : A} -> Id x y -> p x -> p y
   subst C p = jay (λ x y _ → C x → C y) p (λ _ x' → x')

   _∘_ : {A : Set} {M N P : A} -> Id N P -> Id M N -> Id M P
   _∘_ {A}{M}{N}{P} b a = subst (\ x -> Id M x) b a

   ∘unitr : {A : Set} {M N : A} -> (α : Id M N) -> Id (α ∘ Refl) α
   ∘unitr α = jay (λ x y p → Id (p ∘ Refl) p) α (λ _ → Refl)

   subst' : {A : Set} {M : A} (P : (x : A) -> Id M x -> Set) 
            {y z : A} -> (α : Id M y) (β : Id y z) -> P y α  -> P z (β ∘ α)
   subst' {A}{M} P α β b = jay (λ y z β' → (α' : Id M y) → P y α' → P z (β' ∘ α')) β (λ _ _ b' → b') α b

   pmfromjay' : {A : Set} {M : A} (C : (x : A) -> Id M x -> Set)
           -> {N : A} -> (P : Id M N)
           -> (C M Refl)
           -> C N P
   pmfromjay' {A}{M}C {N} α b = subst (C N) (∘unitr α) (subst' C Refl α b) 

   
