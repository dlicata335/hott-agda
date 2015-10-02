
{-# OPTIONS --type-in-type #-}

open import lib.Prelude

module misc.Typecase where

  mutual
    data Code : Set where
      Unitc : Code
      Voidc : Code
      Boolc : Code
      Σc : (C : Code) → ([ C ] → Code) → Code
    
    [_] : Code → Set 
    [ Unitc ] = Unit
    [ Voidc ] = Void
    [ Boolc ] = Bool
    [ Σc A B ] = Σ (\ (x : [ A ]) → [ B x ])

    IsTrue : Bool → Code
    IsTrue True = Unitc
    IsTrue False = Voidc

    IsFalse : Bool → Code
    IsFalse True = Voidc
    IsFalse False = Unitc

    TrueBool : Code
    TrueBool = Σc Boolc IsTrue

    FalseBool : Code
    FalseBool = Σc Boolc IsFalse

    inspect : Code → Code
    inspect (Σc Boolc f) = f True
    inspect _ = Unitc

    contra : (p : TrueBool == FalseBool) → Void
    contra p = coe (ap ([_] o inspect) p) <>
