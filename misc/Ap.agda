
{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open import homotopy.Pi1S1

module misc.Ap where

  open S¹

  test : ap Cover (coe (ap (λ x → base == x) loop) loop)
      == coe (ap (\ x -> Cover base == x) (ap Cover loop)) (ap Cover loop)
  test = ?

  

