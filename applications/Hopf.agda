{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open Paths

module applications.Hopf where

  module Twist2 where
    open S²2

    id : S² -> S²
    id x = x

    -- 180 degree rotations about the designated axis
    rotx : S² -> S²
    rotx = S²-rec a b s n (! ba) (! fr) 

    roty : S² -> S²
    roty = S²-rec b a (! s) (! n) (! (resp ! ba)) (! (resp ! fr))

    rotz : S² -> S²
    rotz = S²-rec b a (! s) (! n) (! (resp ! fr)) (! (resp ! ba)) 

  module Twist1 where
    open S¹2
  
    id : S¹ -> S¹ 
    id x = x
  
    twist : S¹ -> S¹ 
    twist = S¹-rec b a (! s) (! n)
  
    twist-! : (x : S¹) -> twist (twist x) ≃ x
    twist-! = S¹-elim Refl Refl {!!} {!!}
  
    untwist1 : (x : S¹) -> twist x ≃ x
    untwist1 = S¹-elim (! s) 
                       n
                       (subst (λ z → twist z ≃ z) n (! s) ≃〈 subst-Id twist (λ z → z) n (! s) 〉 
                        resp (\ z -> z) n ∘ (! s) ∘ ! (resp twist n) ≃〈 {!!} 〉 
                        n ∎)
                       (subst (λ z → twist z ≃ z) s (! s) ≃〈 subst-Id twist (λ z → z) s (! s) 〉 
                        resp (\ z -> z) s ∘ (! s) ∘ ! (resp twist s) ≃〈 {!!} 〉 
                        n ∎)
  
    untwist2 : (x : S¹) -> twist x ≃ x
    untwist2 = S¹-elim (! n) 
                       s
                       (subst (λ z → twist z ≃ z) n (! n) ≃〈 subst-Id twist (λ z → z) n (! n) 〉
                        resp (λ z → z) n ∘ ! n ∘ ! (resp twist n) ≃〈 {!!} 〉 
                        (s ∎))
                       (subst (λ z → twist z ≃ z) s (! n) ≃〈 subst-Id twist (λ z → z) s (! n) 〉
                        resp (λ z → z) s ∘ ! n ∘ ! (resp twist s) ≃〈 {!!} 〉 
                        (s ∎))
                       
    test = ! (untwist2 a) ∘ (untwist1 a)