
module lib.Sums where

  data Void : Set where

  data Either (a : Set) (b : Set) : Set where
    Inl : a -> Either a b
    Inr : b -> Either a b
