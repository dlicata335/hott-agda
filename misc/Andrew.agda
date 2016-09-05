{-# OPTIONS --type-in-type #-}

open import lib.Prelude

module misc.Andrew where

open BoolM

f : Bool -> Bool -> Bool
f x y = if _ / x then y else False

g : Bool -> Bool -> Bool
g x y = if _ / y then x else False

e1 : (x : Bool) → Path (f True x) (g True x)
e1 True = id
e1 False = id

eh : (x : _) → f x == g x
eh True = λ≃ e1
eh False = λ≃ (λ { True → id ; False → id })

e : f == g
e = λ≃ eh

Phi : Bool -> Type
Phi True = Bool
Phi False = Unit

Psi : (Bool -> Bool -> Bool) -> Type
Psi u = Phi (u True True) × Phi (u True False) × Phi (u False True) × Phi (u False False)

X : Psi f
X = (True , <> , <> , <>)

Y : Psi g
Y = transport Psi e X

goal : fst Y == True
goal = fst Y                                                               ≃〈 ap fst (ap≃ (transport-× e (λ u → Phi (u True True)) (λ u → Phi (u True False) × Phi (u False True) × Phi (u False False)))) 〉 
       transport (λ u → Phi (u True True)) e (fst X)                       ≃〈 ap≃ (transport-ap-assoc' Phi (λ u → u True True) e) 〉 
       transport Phi (ap (λ u → u True True) e) (fst X)                    ≃〈 ap (λ x → transport Phi x True) (ap-o (λ f₁ → f₁ True) (λ f₁ → f₁ True) e) 〉 
       transport Phi (ap (λ f₁ → f₁ True) (ap (λ f₁ → f₁ True) e)) (fst X) ≃〈 ap (λ x → transport Phi x True) (ap (ap (λ f₁ → f₁ True)) (Π≃β eh)) 〉 
       transport Phi (ap (λ f₁ → f₁ True) (λ≃ e1)) (fst X)                 ≃〈 ap (λ x → transport Phi x True) (Π≃β e1) 〉 
       True ∎
