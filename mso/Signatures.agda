{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude

module mso.Signatures where

  data Tp : Type where
    node : Tp
    edge : Tp

  Individ : Tp → Type
  Individ node = String
  Individ edge = String

  Args : Type
  Args = List Tp

  Individs : Args → Type
  Individs [] = Unit
  Individs (τ :: τs) = Individs τs × Individ τ

  data SigThing : Type where
    i : Tp → SigThing
    r : List Tp → SigThing

  Signature = List SigThing

  _,i_ : Signature → Tp → Signature
  Σ ,i τ = i τ :: Σ

  _,r_ : Signature → Args → Signature
  Σ ,r τs = r τs :: Σ

  infixl 10 _,i_ 
  infixl 10 _,r_ 

  Graph : Signature
  Graph = [] ,r (node :: node :: []) 

  Subset = (τ : Tp) → Individ τ → Type -- FIXME: decidable/finite?

  example1 : Subset
  example1 node x = x == "a"
  example1 edge x = x == "7"

  IndividS : Subset → Tp → Type
  IndividS A τ = Σ \ (x : Individ τ) → A τ x

  IndividsS : Subset → Args → Type
  IndividsS A [] = Unit
  IndividsS A (τ :: τs) = IndividsS A τs × IndividS A τ

  data OC : Type where
    Open : OC
    Closed : OC

  data StructureS : OC → Subset → Signature → Type where
     []      : ∀ {oc A} → StructureS oc A []
     _,is_   : ∀ {oc A Σ τ} → StructureS oc A Σ → IndividS A τ → StructureS oc A (Σ ,i τ)
     _,none  : ∀ {oc A Σ τ} → StructureS oc A Σ → StructureS Open A (Σ ,i τ)              -- s,_/x 
     _,rs_   : ∀ {oc A Σ τs} → StructureS oc A Σ → (IndividsS A τs → Type) → StructureS oc A (Σ ,r τs) 

  postulate
    openify : ∀ {oc A Σ} → StructureS oc A Σ → StructureS Open A Σ

  Structure : OC → Signature → Type
  Structure oc Sig = Σ \ (A : Subset) → StructureS oc A Sig

{-
  example : Structure (· ,i node ,i edge)
  example = example1 , (<> , ("a" , id)) , {!!}

  particulargraph : Structure Graph
  particulargraph = {!!}
-}
