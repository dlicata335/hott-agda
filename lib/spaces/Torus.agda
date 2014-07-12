{-# OPTIONS --type-in-type --without-K #-}

open import lib.BasicTypes 
open import lib.cubical.Cubical

module lib.spaces.Torus where

module Torus where
  private
    module T where
     private
       data T' : Set where
         a' : T'
     
     T : Set
     T = T'
  
     a : T
     a = a'
  
     postulate {- HoTT Axiom -}
       p : a ≃ a
       q : a ≃ a
       f : Square p q q p
  
     T-rec :  {C : Set}
           -> (a : C)
           -> (p q : a ≃ a)
           -> (f' : Square p q q p)
           -> T -> C
     T-rec a'' _ _ _ a' = a''
  
     T-elim : (C : T -> Set)
              (a' : C a) 
              (p' : PathOver C p a' a') 
              (q' : PathOver C q a' a')
              (f' : SquareOver C f p' q' q' p') 
           -> (x : T) -> C x
     T-elim _ a'' _ _ _ a' = a''
  
     postulate {- HoTT Axiom -}
       βp/rec : {C : Set}
         -> (a' : C)
         -> (p' q' : a' ≃ a')
         -> (f' : Square p' q' q' p')
         -> ap (T-rec a' p' q' f') p ≃ p'
       
       βq/rec : {C : Set}
         -> (a' : C)
         -> (p' q' : a' ≃ a')
         -> (f' : Square p' q' q' p')
         -> ap (T-rec a' p' q' f') q ≃ q'
  
     postulate {- HoTT Axiom -}
       βf/rec : {C : Set}
         -> (a' : C)
         -> (p' q' : a' ≃ a')
         -> (f' : Square p' q' q' p')
         -> Cube (ap-square (T-rec a' p' q' f') f) f' (horiz-degen-square (βp/rec a' p' q' f')) (horiz-degen-square (βq/rec a' p' q' f')) (horiz-degen-square (βq/rec a' p' q' f')) (horiz-degen-square (βp/rec a' p' q' f'))
  
  open T public

