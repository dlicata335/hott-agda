
module HEqUniv where

data Path {A : Set1} (a : A) : A → Set where

data HEq-elim (A : Set) : (B : Set) (α : Path{Set} A B) (a : A) (b : B) → Set where
