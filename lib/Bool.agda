
open import lib.Paths
open Paths

module lib.Bool where

      data Bool : Set where
        True : Bool
        False : Bool
      {-# COMPILED_DATA Bool Bool True False #-}
  
      if_/_then_else : (p : Bool -> Set) -> (b : Bool) -> p True -> p False -> p b
      if _ / True then b1 else b2 = b1
      if _ / False then b1 else b2 = b2

{-
  respif : {Γ : Set} {θ1 θ2 : Γ} {P : Id θ1 θ2} {C : Γ -> Bool -> Set} {M : Γ -> Bool} {M1 : (x : Γ) -> C x True} {M2 : (x : Γ) -> C x False} 
         -> Id (respd (\ x -> if C x / (M x) then (M1 x) else (M2 x)) P) 
               {!!} -- (if {!\ y -> Id (subst (\ x -> C x True)!} / M N' then respd M1 P else (respd M2 P))
  respif = {!!}

-- true  branch: Id (subst (λ x → C x True) P (M1 N)) (M1 N')
-- false branch: Id (subst (λ x → C x False) P (M2 N)) (M2 N')
-}