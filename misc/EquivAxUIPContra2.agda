{- A proof that the equivalence axiom plus uip is inconsistent
   Dan Licata, June 2010 

   FIXME CODE ROT: update to new universe poly
-}

open import lib.Prelude hiding (WEq ; HFiber ; WEqBy ; Iso)
open Paths

module misc.EquivAxUIPContra2 where

  {- Weak equivalence -}
  module WEq where
    -- contractible
    Contr : ∀ {l} -> Set l -> Set l
    Contr A = Σ \ (t : A) -> (x : A) -> Id x t
  
    HFiber : ∀ {l} {A B : Set l} -> (A -> B) -> B -> Set l
    HFiber f y = Σ \x -> Id (f x) y
  
    WEqBy : ∀ {l} (A B : Set l) -> (f : A -> B) -> Set l
    WEqBy A B f = (y : _) -> Contr (HFiber f y)
  
    WEq : ∀ {l} (A B : Set l) -> Set l
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
  
    idToWEq : ∀ {l} {A B : Set l} -> Id A B -> (WEq A B)
    idToWEq Refl = (\ x -> x) , idweq
  open IdToWEq

  {- equivalence axiom
     and 
     weak equivalence implies identity -}
  module WEqToId where
    postulate
      equivaxiom : ∀ {l} {A B : Set l} -> WEqBy (Id A B) (WEq A B) idToWEq 
  
    eaΣ : ∀ {A B : Set} -> WEq (Id A B) (WEq A B) 
    eaΣ = idToWEq , equivaxiom
  
    back : ∀ {A B : Set} -> WEq A B -> (B -> A)
    back (f , by) b = fst (fst (by b))
  
    wEqToId : ∀ {A B : Set} -> WEq A B -> Id A B 
    wEqToId w = back eaΣ w
  open WEqToId 

  module Contradiction where

   Connected : Set -> Set
   Connected A = ( x y : A) -> Id x y 

   uip : {A : Set} {m n : A} {p q : Id m n} -> Id p q
   uip {p = Refl} {q = Refl} = Refl

   pathIsCon : {A : Set} {x y : A} -> Connected (Id x y)
   pathIsCon p =  \ _ -> uip  

   wEqIsCon : {x y : Set} -> Connected (WEq x y)
   wEqIsCon = subst Connected (wEqToId eaΣ)  pathIsCon 

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

     wrong : Id True False
     wrong = resp (\ x -> back x True) identify

     data Void : Set where 

     Check : Bool -> Set
     Check True = Unit
     Check False = Void

     contra : Void
     contra = subst Check wrong _
