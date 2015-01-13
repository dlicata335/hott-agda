
{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude

module misc.TransportEta where
   postulate 
     eta : {B : Type} (E : B → Type) 
           {b1 : B} 
           → (f : {b2 : B} → Path b1 b2 → E b1 → E b2)
           → (f id == (\ x -> x))
           → {b2 : B} (p : b1 == b2) (e : E b1) → f p e == transport E p e

     eta' : {B : Type} {b1 : B} (E : (b2 : B) → b1 == b2 → Type) 
           → (f : {b2 : B} (p : Path b1 b2) → E b1 id → E b2 p)
           → (f id == (\ x -> x))
           → {b2 : B} (p : b1 == b2) (e : E b1 id) → f p e == path-induction E e p

   scontr : {B : Type} {b1 b2 : B} → (p : b1 == b2) 
          → Path {Σ \ b2 → b1 == b2} (b1 , id) (b2 , p)
   scontr {B} {b1}{b2} p = coe {!!} (eta (λ b → Σ (λ b3 → b == b3)) {b1} (λ q x → fst x , snd x ∘ ! q) id p (b1 , id)) 
