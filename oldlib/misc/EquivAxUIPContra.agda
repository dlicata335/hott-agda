{- A proof that the equivalence axiom plus uip is inconsistent
   Dan Licata, June 2010 

   (1) The equivalence axiom states that weak equivalence is weakly
       equivalent to identity.  As a corollary weak equiv. and identity
       are interprovable.  Therefore we can substitute (WEq x y) for (Id
       x y) in any context.
   (2) Identity has UIP. By substituting weak equivalence for identity
       in this theorem, all proofs of weak equivalence are identical.  
   (3) There are two computationally different proofs of weak equivalence 
       between bool and itself, the identity and negation
   (4) But by (2) these two proofs are identical. 
       Therefore \x.x = not, from which we get a contradiction

   This file uses type-in-type just to state the equivalence axiom,
   though you could sort out the universe levels like
   in Voevodsky's Coq code instead.  
-}

{-# OPTIONS --type-in-type #-}

open import lib.Prelude hiding (WEq ; HFiber ; WEqBy ; Iso)
open Paths

module misc.EquivAxUIPContra where

  {- Weak equivalence -}
  module WEq where
    Contr : Set -> Set
    Contr A = Σ \ (t : A) -> (x : A) -> Id x t
  
    HFiber : {A B : Set} -> (A -> B) -> B -> Set
    HFiber f y = Σ \x -> Id (f x) y
  
    WEqBy : (A B : Set) -> (f : A -> B) -> Set
    WEqBy A B f = (y : _) -> Contr (HFiber f y)
  
    WEq : (A B : Set) -> Set
    WEq A B = Σ \f -> WEqBy A B f
  open WEq

  {- identity implies weak equivalence
     note: you can do this part using only J, but I use pattern-matching here for convenience
  -}
  module IdToWEq where
    idweq : ∀ {A} -> WEqBy A A (\ x -> x)
    idweq y = (y , Refl) , pf where
      pf : (x : Σ (λ x' → Id x' y)) → Id x (y , Refl)
      pf (.y , Refl) = Refl
  
    idToWEq : ∀ {A B : Set} -> Id A B -> WEq A B
    idToWEq Refl = (\ x -> x) , idweq
  open IdToWEq

  {- weakly equivalent sets are isomoprhic, even without the equivalence axiom -}
  module Iso where
    record Iso (A B : Set) : Set where
     field
      l : A -> B
      r : B -> A
      lr : (x : _) -> Id (l (r x)) x
      rl : (x : _) -> Id (r (l x)) x
    
    back : ∀ {A B : Set} -> WEq A B -> (B -> A)
    back (f , by) b = fst (fst (by b))
    
    iso : ∀ {A B : Set} -> WEq A B -> Iso A B
    iso {A} {B} w = record {l = fst w; r = back w; lr = lr w; rl = rl w}
      where lr : (w : WEq A B) (x : B) -> Id (fst w (back w x)) x
            lr (f , by) x with  (by x)
            ... | ((a , b) , c) = b

            rl : (w : WEq A B) (x : A) -> Id (back w (fst w x)) x
            rl (f , by) x with by (f x)
            ... | ((a , b) , c) = ! (resp fst (c (x , Refl)))
      
  {- equivalence axiom
     and 
     weak equivalence implies identity -}
  module WEqToId where
    postulate
      equivaxiom : ∀ {A B : Set} -> WEqBy (Id A B) (WEq A B) idToWEq 
  
    eaΣ : ∀ {A B : Set} -> WEq (Id A B) (WEq A B) 
    eaΣ = idToWEq , equivaxiom
  
    back : ∀ {A B : Set} -> WEq A B -> (B -> A)
    back (f , by) b = fst (fst (by b))
  
    wEqToId : ∀ {A B : Set} -> WEq A B -> Id A B 
    wEqToId w = back eaΣ w
  open WEqToId 

  {- all proofs of weak equivalence are identical -}
  module UniqueWEq where
   Connected : Set -> Set
   Connected A = ( x y : A) -> Id x y 

   uip : {A : Set} {m n : A} {p q : Id m n} -> Id p q
   uip {p = Refl} {q = Refl} = Refl

   idIsCon : {A : Set} {x y : A} -> Connected (Id x y)
   idIsCon p =  \ _ -> uip  

   wEqIsCon : {x y : Set} -> Connected (WEq x y)
   wEqIsCon = subst Connected (wEqToId eaΣ)  idIsCon 
  open UniqueWEq 

  module Iso1 where
   -- bool is isomorphic to bool by the identity
   weq : WEq Bool Bool
   weq = idToWEq Refl

  module Iso2 where
   -- bool is isomorphic to bool by negation

   not : Bool -> Bool
   not True = False
   not False = True

   notnot : (b : Bool) -> Id (not (not b)) b
   notnot True = Refl
   notnot False = Refl

   weq : WEq Bool Bool
   weq = not , 
         \ image -> (not image , notnot image ) , pf image where
    pf : (image : _) -> ((x : Σ (λ x' → Id (not x') image)) → Id x (not image , notnot image))
    pf ._ (True , Refl) = Refl
    pf ._ (False , Refl) = Refl
 
  module XXX where
    identify : Id Iso1.weq Iso2.weq
    identify = wEqIsCon Iso1.weq Iso2.weq

    wrong : Id (\ x -> x) Iso2.not
    wrong = resp fst identify 
  
    apply : ∀ {A B} {f g : A -> B} -> Id f g -> (x : A) -> Id (f x) (g x)
    apply Refl _ = Refl

    data Void : Set where 

    Check : Bool -> Set
    Check True = Unit
    Check False = Void

    contra : Void
    contra = subst Check (apply wrong True) _
