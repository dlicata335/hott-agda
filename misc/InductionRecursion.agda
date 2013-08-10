{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude

module misc.InductionRecursion where

 -- dybjer and setzer codes
 module Dybjer where
  data IR (D : Type) : Type where
    ι : D -> IR D
    σ : (A : Type) -> (A → IR D) → IR D
    δ : (A : Type) → ((A → D) -> IR D) → IR D

  Fam : Type -> Type
  Fam D = Σ \ (U : Type) → (U -> D)

  interp : ∀ {D} → IR D → (Fam D → Fam D)
  interp (ι d)   (U , T) = Unit , (λ _ → d)
  interp (σ A f) (U , T) = Σ (λ (a : A) → fst (interp (f a) (U , T))) , λ {(a , b) → snd (interp (f a) (U , T)) b}
  interp (δ A F) (U , T) = Σ (λ (g : A → U) → fst (interp (F (T o g)) (U , T))) , 
                             λ {(g , b) → snd (interp (F (T o g)) (U , T)) b}

  postulate
    μ : ∀ {D : _} → IR D → Fam D
    roll : ∀ {D}{c : IR D} → μ c ≃ interp c (μ c)

  -- universe with nat and Σ
  U : IR Type
  U = σ Bool λ {True → ι Nat ; False → δ Unit (λ A → δ (A <>) (λ B → ι (Σ B)))}

  nat : fst (μ U)
  nat = coe (! (ap fst roll)) (True , <>)

  zer : snd (μ U) nat
  zer = coe (ap≃ (snd≃ (! roll))) (coe
                                     (!
                                      (ap≃ (transport-→-pre (ap fst (! roll)) (snd (interp U (μ U))))
                                       {nat}))
                                     {!!})

  nat×nat : fst (μ U)
  nat×nat = coe (! (ap fst roll)) (False , (λ _ → nat) , ((λ _ → nat) , <>))

  -- Σ n:nat. case n of 0 -> n | S _ -> N × N
  example : fst (μ U)
  example = coe (! (ap fst roll)) (False , (λ _ → nat) , {!!} , <>)


 -- ghani et al. codes
 module FiberedIR {B : Type} (K : B → Type)
                  (ΣE : (A : Type) → (B : A → Σ K) → Σ K) where
   E = Σ K
 
   data IR : Type where
      ι : E → IR
      σ : (A : Type) → (A → IR) → IR
      δ : (b : B) → (K b -> IR) → IR

   interp : IR -> (E → E)
   interp (ι P) _ = P
   interp (σ A f) Q = ΣE A (λ a → interp (f a) Q)
   interp (δ b F) Q = ΣE (fst Q ≃ b) (λ α → interp (F (transport K α (snd Q))) Q)
   
   postulate 
     μ    : IR → E
     roll : (c : IR) → interp c (μ c) ≃ μ c