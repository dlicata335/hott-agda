{-# OPTIONS --type-in-type --without-K #-}

open import lib.BasicTypes 

module lib.spaces.Interval where

  open Paths

  private 
    -- thing you would try first
    module NoDefinitionalBehavior where
      postulate {- HoTT Axiom -} 
        I : Set
        Zero : I
        One  : I
        seg : Zero ≃ One
        I-rec : {C : Set} 
               -> (a b : C)
               -> (p : a ≃ b)
               -> I -> C
        compβ0 : {C : Set} 
               -> (a b : C)
               -> (p : a ≃ b)
               -> I-rec a b p Zero ≃ a
        compβ1 : {C : Set} 
               -> (a b : C)
               -> (p : a ≃ b)
               -> I-rec a b p One ≃ b
        compβseg : {C : Set} 
               -> (a b : C)
               -> (p : a ≃ b)
               -> ap (I-rec a b p) seg ≃ (! (compβ1 _ _ _)) ∘  p ∘ (compβ0 _ _ _)
                  -- wouldn't need the trans if comp0 and comp1 were definitional


  {- Nisse found a bug:
     https://lists.chalmers.se/pipermail/agda/2012/004052.html -}
  module Interval where
    private
      data I' : Set where
        Zero : I'
        One  : I'

    I : Set
    I = I'

    zero : I
    zero = Zero

    one : I
    one = One

    postulate {- HoTT Axiom -}
      seg : zero ≃ one

    I-rec : {C : Set} 
           -> (a b : C)
           -> (p : a ≃ b)
           -> I -> C
    I-rec a b _ Zero = a
    I-rec a b _ One = b

    I-elim : {C : I -> Set} 
           -> (a : C zero) (b : C one) (p : transport C seg a ≃ b)
           -> (x : I) -> C x
    I-elim a b _ Zero = a
    I-elim a b _ One = b

    postulate {- HoTT Axiom -} 
      compβseg/rec : {C : Set} 
           -> (a b : C)
           -> (p : a ≃ b)
           -> ap (I-rec a b p) seg ≃ p
      -- compβseg/elim : {C : I -> Set} 
      --      -> (a : C zero) (b : C one) (p : subst C seg a ≃ b)
      --      -> ap (I-elim a b p) seg ≃ p
    -- FIXME : η?

  {- conjectured fix: 
     https://lists.chalmers.se/pipermail/agda/2012/004061.html -}
  module IntervalFn where
    private
      data I' : Set where
        Zero : I'
        One  : I'

      data I'' : Set where
        mkI'' : (I' × (Unit -> Unit)) -> I''

    I : Set
    I = I''

    zero : I
    zero = mkI'' (Zero , _)
    
    one : I
    one = mkI'' (One , _)

    postulate {- HoTT Axiom -}
      seg : zero ≃ one

    I-rec : {C : Set} 
           -> (a b : C)
           -> (p : a ≃ b)
           -> I -> C
    I-rec a b _ (mkI'' (Zero , _)) = a
    I-rec a b _ (mkI'' (One , _)) = b

    I-elim : {C : I -> Set} 
           -> (a : C zero) (b : C one) (p : transport C seg a ≃ b)
           -> (x : I) -> C x
    I-elim a b _ (mkI'' (Zero , _)) = a
    I-elim a b _ (mkI'' (One , _)) = b

  open IntervalFn public
  {-
    Interval provides:
    I : Set
    zero : I
    one : I
    seg : zero ≃ one
    I-rec : {C : Set} 
           -> (a b : C)
           -> (p : a ≃ b)
           -> I -> C
    I-rec a b _ Zero = a
    I-rec a b _ One = b
    βseg : {C : Set} 
           -> (a b : C)
           -> (p : a ≃ b)
           -> ap (I-rec a b p) seg ≃ p
  -}

  ext-from-I : (A B : Set) (f g : A -> B) (α : (x : A) -> f x ≃ g x) -> f ≃ g
  ext-from-I A B f g α = ap h seg where
    h : (I -> A -> B)
    h = (λ i x → I-rec (f x) (g x) (α x) i)

    -- can you prove the computation rule?
    -- compute : (x : A) -> ap (\ f -> f x) ext ≃ (α x)
    -- compute x = {!Stuck.ap' (\ f -> f x) ext ≃⟨ ? ⟩ !}

{-

  seg-unique : (p : Id zero one) -> Id p seg
  seg-unique p = jay1 (λ y → I-elim{C = \ y -> Id zero y -> Set} (\ p' -> Id Refl p') (\ p' -> Id p' seg) {!!} y) p Refl

  module CharacterizeIdI {x y : I} where
    left : Id x y
    left = I-elim{(\ x -> Id x y)} 
                  (I-elim{\ y -> Id zero y} Refl seg {!!} y) 
                  (I-elim{\ y -> Id one y} (sym seg) Refl {!!} y) 
                  {!!} x 
    thm : {p : Id x y} -> Id p left
    thm = {!!}
-}
 
  module Pushout where
    private
      data Pushout : Set where
        Left  : I -> Pushout
        Right : I -> Pushout

    I+I/1=0 : Set
    I+I/1=0 = Pushout

    left : I -> I+I/1=0
    left = Left 

    right : I -> I+I/1=0
    right = Right

    postulate {- HoTT Axiom -}
      1=0 : left one ≃ right zero

    I+I/1=0-rec : {C : Set} 
                -> (left right : I -> C)
                -> (pres : left one ≃ right zero)
                -> I+I/1=0 -> C
    I+I/1=0-rec l r _ (Left x)  = l x
    I+I/1=0-rec l r _ (Right y) = r y

    postulate {- HoTT Axiom -} 
      compβ1=0 : {C : Set} 
           -> (l r : I -> C)
           -> (pres : _)
           -> ap (I+I/1=0-rec l r pres) 1=0 ≃ pres
  open Pushout
  {-
    I+I/1=0 : Set
    left : I -> I+I/1=0
    right : I -> I+I/1=0
    1=0 : left one ≃ right zero

    I+I/1=0-rec : {C : Set} 
                -> (left right : I -> C)
                -> (pres : left one ≃ right zero)
                -> I+I/1=0 -> C
    I+I/1=0-rec l r _ (Left x)  = l x
    I+I/1=0-rec l r _ (Right y) = r y
    compβ1=0 : {C : Set} 
           -> (l r : I -> C)
           -> (pres : _)
           -> ap (I+I/1=0-rec l r pres) 1=0 ≃ pres
  -}

  module CoGroupoid where
    corefl : I -> Unit
    corefl = \ _ -> <>

    cosym : I -> I
    cosym = I-rec one zero (! seg) 

    cotrans : I -> I+I/1=0 
    cotrans p = I-rec (left zero) (right one) ((ap right seg) ∘ 1=0 ∘ (ap left seg)) p

    {-
      meet : I x I -> I
      acts like algebraic meet operation
    -}
  
{-
  -- holds without functional extensionality 
  flipflip : {A B C : Set} -> (\ (x : A -> B -> C) -> flip (flip x)) ≃ (\ x -> x)
  flipflip = Refl
-}


{- other stuff related to the computation rule 
  nat : {A B : Set} {f g : A -> B} 
      -> (funpath : (x : A) -> Id (f x) (g x))
      -> {x y : A} (argpath : Id x y)
      -> Id (trans (funpath x) (ap g argpath)) (trans (ap f argpath) (funpath y))
  nat funpath Refl = sym (trans-unit-l (funpath _))  

  -- should be a consequence of above and nat
  compute : {A B : Set} {f g : A -> B} 
            -> (funpath : (x : A) -> Id (f x) (g x))
            -> {x y : A} (argpath : Id x y)
            -> Id (ap2 (\ x y -> x y) (ext funpath) argpath) (trans (funpath x) (ap g argpath))
  compute = {!!}
-}