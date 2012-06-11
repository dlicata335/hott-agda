{-# OPTIONS --type-in-type #-}

open import lib.Paths
open import lib.Prods
open import lib.Functions
open import lib.Sums
open Paths

module lib.Bool where

  data Bool : Set where
    True : Bool
    False : Bool
  {-# COMPILED_DATA Bool Bool True False #-}

  module BoolM where
      if_/_then_else : (p : Bool -> Set) -> (b : Bool) -> p True -> p False -> p b
      if _ / True then b1 else b2 = b1
      if _ / False then b1 else b2 = b2

      aborttf : ∀ {A : Set} 
              -> True ≃ False -> A
      aborttf{A} α = subst
                      (λ x →
                         if (λ _ → Set) / x then Unit else A)
                      α <>

      subst-if : {A B : Set} {M N : Bool} ->
               subst (\ x -> if (\ _ -> Set) / x then A else B) 
             ≃ (if
                 (λ M' →
                    M' ≃ N ->
                    if (λ _ → Set) / M' then A else B →
                    if (λ _ → Set) / N then A else B)
                 / M 
                 then if (λ N' → Id True N' → A → if (λ _ → Set) / N' then A else B) / N
                        then (λ _ x → x) 
                        else (λ α _ → aborttf α) 
                 else (if (λ N' → Id False N' → B → if (λ _ → Set) / N' then A else B) / N 
                       then (λ α _ → aborttf (! α)) 
                       else (λ _ x → x)))
      subst-if {A}{B}{M}{N}= λ≃ pf where
        pf : ∀ {M N} -> (α : Id M N) 
          -> Id (subst (λ x → if (λ _ → Set) / x then A else B) α) 
                ((if
                 (λ M' →
                    M' ≃ N ->
                    if (λ _ → Set) / M' then A else B →
                    if (λ _ → Set) / N then A else B)
                 / M 
                 then if (λ N' → Id True N' → A → if (λ _ → Set) / N' then A else B) / N
                        then (λ _ x → x) 
                        else (λ α _ → aborttf α) 
                 else (if (λ N' → Id False N' → B → if (λ _ → Set) / N' then A else B) / N 
                       then (λ α _ → aborttf (! α)) 
                       else (λ _ x → x))) α)
        pf {M} {.M} Refl with M 
        ... | True  = Refl
        ... | False = Refl

      Check : Bool -> Set 
      Check True  = Unit
      Check False = Void

      check : (b : Bool) -> Either (Check b) (Id b False)
      check False = Inr Refl
      check True = Inl <>
      
      _andalso_ : Bool -> Bool -> Bool 
      b1 andalso b2 = if (\_ -> Bool) / b1 then b2 else False
      
      _orelse_ : Bool -> Bool -> Bool 
      b1 orelse b2 = if (\_ -> Bool) / b1 then True else b2
      
      check-andI : {b1 b2 : Bool} -> Check b1 -> Check b2 -> Check (b1 andalso b2)
      check-andI {True} {True} _ _ = <>
      check-andI {False} () _ 
      check-andI {_} {False} _ () 

      check-andE : {b1 b2 : Bool} -> Check (b1 andalso b2) -> Check b1 × Check b2 
      check-andE {True} {True} _ = (_ , _)
      check-andE {False} ()  
      check-andE {True} {False} () 

      check-id-not : {b1 : Bool} -> Id b1 False -> Check (if (\ _ -> Bool) / b1 then False else True)
      check-id-not Refl = _

      check-noncontra : (b : Bool) -> Check b -> Check (if (\ _ -> Bool) / b then False else True) -> Void
      check-noncontra True _ v = v
      check-noncontra False v _ = v

      {-# BUILTIN BOOL  Bool  #-}
      {-# BUILTIN TRUE  True  #-}
      {-# BUILTIN FALSE False #-}


      
{-
  respif : {Γ : Set} {θ1 θ2 : Γ} {P : Id θ1 θ2} {C : Γ -> Bool -> Set} {M : Γ -> Bool} {M1 : (x : Γ) -> C x True} {M2 : (x : Γ) -> C x False} 
         -> Id (respd (\ x -> if C x / (M x) then (M1 x) else (M2 x)) P) 
               {!!} -- (if {!\ y -> Id (subst (\ x -> C x True)!} / M N' then respd M1 P else (respd M2 P))
  respif = {!!}

-- true  branch: Id (subst (λ x → C x True) P (M1 N)) (M1 N')
-- false branch: Id (subst (λ x → C x False) P (M2 N)) (M2 N')
-}