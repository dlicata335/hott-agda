-- a bad stab at globular sets; do coinduction instead

open import lib.Prelude using (Nat ; Z ; S)

open import homotopy.Paths
open PM

open import homotopy.Prods

module homotopy.Simplicial where

  module NPath (A : Set) where
    mutual 
      NPath : Nat -> Set
      NPath Z = A
      NPath (S n) = Σ[ x ∶ NPath n × NPath n ] SameEndpoints n x × Id (fst x) (snd x) -- too many point 2 levels down

      endpoints : ∀ {n} -> NPath (S n) -> NPath n × NPath n
      endpoints p = (fst (fst p) , snd (fst p) )
  
      SameEndpoints : (n : _) -> NPath n × NPath n -> Set
      SameEndpoints 0 _ = Unit
      SameEndpoints (S n) es = Id (endpoints{n} (fst es)) (endpoints{n} (snd es))

    test : NPath 1
    test = {!!}

  module NGraph (A : Set) where
    EdgesOn : Set -> Set1
    EdgesOn A = A -> A -> Set
  
    mutual
      NGraph : Nat -> Set1
      NGraph 0 = EdgesOn A 
      NGraph (S n) = Σ \ (g : NGraph n) -> (c : NGraphCtx n g) -> EdgesOn (Ty n g c)
      
      NGraphCtx : (n : Nat) -> NGraph n -> Set
      NGraphCtx 0     E = Σ[ x ∶ A ] Σ[ y ∶ A ] E x y × E x y
      NGraphCtx (S n) (g , p) = {!!}

      Ty : (n : Nat) -> (g : NGraph n) -> NGraphCtx n g -> Set
      Ty n g c = {!!}