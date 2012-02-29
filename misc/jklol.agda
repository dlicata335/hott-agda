{-# OPTIONS --type-in-type #-}

open import lib.Prelude

module misc.jklol where

  module Parameterized where
    module Identity {A : Set} (M : A) where
  
      data Path : A -> Set where
        Refl : Path M
  
      PathFrom : Set
      PathFrom = Σ[ y ∶ A ] Path y
        
      J : (C : (y : A) -> Path y -> Set)
          -> C M Refl
          -> (N : A) (P : Path N) -> C N P
      J C b .M Refl = b

    test : Identity.Path 0 1
    test = {!!}
  
    test' : Identity.PathFrom 0 
    test' = {!!}

    standardJ : (A : Set) (C : (x y : A) -> Identity.Path x y -> Set)
              -> ((x : A) -> C x x Identity.Refl)
              -> (M N : A) (P : Identity.Path M N) -> C M N P
    standardJ A C b M N P = Identity.J {A} M (C M) (b M) N P

  module Take0 where
    J : (A : Set) (C : (x y : A) -> Id x y -> Set)
        -> ((x : A) -> C x x Refl)
        -> (M N : A) (P : Id M N) -> C M N P
    J A C b M .M Refl = b M

  module Take1 where
    J : (A : Set) (M : A) (C : (y : A) -> Id M y -> Set)
        -> C M Refl
        -> (N : A) (P : Id M N) -> C N P
    J A M C b .M Refl = b
  
  PathFrom : {A : Set} -> A -> Set
  PathFrom {A} M = Σ[ y ∶ A ] Id M y

  J : (A : Set) (M : A) (C : PathFrom M -> Set)
      -> C (M , Refl) 
      -> (P : PathFrom M) -> C P
  J A M C b (.M , Refl) = b

  K : (A : Set) (M : A) (C : Id M M -> Set)
      -> C Refl
      -> (loop : Id M M) -> C loop
  K A M C b loop = {!!}

  pathsFrom-unique : {A : Set} (M : A) (p : PathFrom M) 
                   -> Id p (M , Refl)
  pathsFrom-unique {A} M = J A M (λ p → Id p (M , Refl)) Refl 

  data Fin : Nat -> Set where
    fz : ∀ {n} -> Fin (S n)
    fs : ∀ {n} -> Fin n -> Fin (S n)

  fin-elim : (C : (n : Nat) -> Fin n -> Set)
           -> (∀ n -> C (S n) fz)
           -> (∀ n (f : Fin n) -> C n f -> C (S n) (fs f))
           -> (n : Nat) (f : Fin n) -> C n f
  fin-elim C b1 b2 .(S n) (fz {n}) = b1 n
  fin-elim C b1 b2 .(S n) (fs {n} f) = b2 n f (fin-elim C b1 b2 n f)

  data Void : Set where

  no-fin-z : Fin 0 -> Void
  no-fin-z f = fin-elim Pred (\ _ -> <>) (\ _ _ _ -> <>) Z f where
    Pred : (n : Nat) -> Fin n -> Set
    Pred 0 f = Void
    Pred (S _) _ = Unit

  no-fin-z/pm : Fin Z -> Void
  no-fin-z/pm ()

