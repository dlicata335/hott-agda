{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open import lib.Prods
open import lib.Functions
open import lib.Sums

module lib.Bool where

  data Bool : Type where
    True : Bool
    False : Bool
  {-# COMPILED_DATA Bool Bool True False #-}

  module BoolM where
      if_/_then_else : (p : Bool -> Type) -> (b : Bool) -> p True -> p False -> p b
      if _ / True then b1 else b2 = b1
      if _ / False then b1 else b2 = b2

      aborttf : ∀ {A : Type} 
              -> True ≃ False -> A
      aborttf{A} α = transport
                      (λ x →
                         if (λ _ → Type) / x then Unit else A)
                      α <>

      transport-if : {A B : Type} {M N : Bool} ->
               transport (\ x -> if (\ _ -> Type) / x then A else B) 
             ≃ (if
                 (λ M' →
                    M' ≃ N ->
                    if (λ _ → Type) / M' then A else B →
                    if (λ _ → Type) / N then A else B)
                 / M 
                 then if (λ N' → Path True N' → A → if (λ _ → Type) / N' then A else B) / N
                        then (λ _ x → x) 
                        else (λ α _ → aborttf α) 
                 else (if (λ N' → Path False N' → B → if (λ _ → Type) / N' then A else B) / N 
                       then (λ α _ → aborttf (! α)) 
                       else (λ _ x → x)))
      transport-if {A}{B}{M}{N}= λ≃ pf where
        pf : ∀ {M N} -> (α : Path M N) 
          -> Path (transport (λ x → if (λ _ → Type) / x then A else B) α) 
                ((if
                 (λ M' →
                    M' ≃ N ->
                    if (λ _ → Type) / M' then A else B →
                    if (λ _ → Type) / N then A else B)
                 / M 
                 then if (λ N' → Path True N' → A → if (λ _ → Type) / N' then A else B) / N
                        then (λ _ x → x) 
                        else (λ α _ → aborttf α) 
                 else (if (λ N' → Path False N' → B → if (λ _ → Type) / N' then A else B) / N 
                       then (λ α _ → aborttf (! α)) 
                       else (λ _ x → x))) α)
        pf {M} {.M} id with M 
        ... | True  = id
        ... | False = id

      Check : Bool -> Type 
      Check True  = Unit
      Check False = Void

      check : (b : Bool) -> Either (Check b) (Path b False)
      check False = Inr id
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

      check-id-not : {b1 : Bool} -> Path b1 False -> Check (if (\ _ -> Bool) / b1 then False else True)
      check-id-not id = _

      check-noncontra : (b : Bool) -> Check b -> Check (if (\ _ -> Bool) / b then False else True) -> Void
      check-noncontra True _ v = v
      check-noncontra False v _ = v

      {-# BUILTIN BOOL  Bool  #-}
      {-# BUILTIN TRUE  True  #-}
      {-# BUILTIN FALSE False #-}

      forget : ∀ {A B} → Either A B -> Bool
      forget (Inl _) = True
      forget (Inr _) = False

{-
  respif : {Γ : Type} {θ1 θ2 : Γ} {P : Path θ1 θ2} {C : Γ -> Bool -> Type} {M : Γ -> Bool} {M1 : (x : Γ) -> C x True} {M2 : (x : Γ) -> C x False} 
         -> Path (respd (\ x -> if C x / (M x) then (M1 x) else (M2 x)) P) 
               {!!} -- (if {!\ y -> Path (transport (\ x -> C x True)!} / M N' then respd M1 P else (respd M2 P))
  respif = {!!}
-}

-- true  branch: Path (transport (λ x → C x True) P (M1 N)) (M1 N')
-- false branch: Path (transport (λ x → C x False) P (M2 N)) (M2 N')
