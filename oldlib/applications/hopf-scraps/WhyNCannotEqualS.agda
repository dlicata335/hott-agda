{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open Paths

module applications.hopf-scraps.WhyNCannotEqualS where

  module Loops where
    open S²2

    collapse-counterclockwise-b-fr : (s ∘ ! n) ≃ Refl
    collapse-counterclockwise-b-fr = !-inv-r s ∘ resp (λ x → s ∘ ! x) fr

    collapse-counterclockwise-b-ba : (s ∘ ! n) ≃ Refl
    collapse-counterclockwise-b-ba = !-inv-r s ∘ resp (λ x → s ∘ ! x) ba

    collapse-counterclockwise-a-fr : (n ∘ ! s) ≃ Refl
    collapse-counterclockwise-a-fr = !-inv-r n ∘ resp (λ x → n ∘ ! x) (! fr)

    collapse-counterclockwise-a-ba : (n ∘ ! s) ≃ Refl
    collapse-counterclockwise-a-ba = !-inv-r n ∘ resp (λ x → n ∘ ! x) (! ba)

    collapse-clockwise-a-fr : (! s ∘ n) ≃ Refl
    collapse-clockwise-a-fr = !-inv-l s ∘ resp (λ x → ! s ∘ x) fr

    collapse-clockwise-a-ba : (! s ∘ n) ≃ Refl
    collapse-clockwise-a-ba = !-inv-l s ∘ resp (λ x → ! s ∘ x) ba

  module Twist2 where
    open S²2

    id : S² -> S²
    id x = x

    -- 180 degree rotations about the designated axis
    rotx : S² -> S²
    rotx = S²-rec a b s n (! ba) (! fr) 

    module Unused where
      roty : S² -> S²
      roty = S²-rec b a (! s) (! n) (! (resp ! ba)) (! (resp ! fr))
  
      rotz : S² -> S²
      rotz = S²-rec b a (! s) (! n) (! (resp ! fr)) (! (resp ! ba)) 

    a' = id
    b' = rotx 

{-  have some choices about p1 and p2

    n' : a' ≃ b' 
    n' = λ≃ (S²-elim (\p -> p ≃ rotx p) 
                     p1
                     p2 
                     (subst (λ p → p ≃ rotx p) n p1 ≃〈 subst-Id (λ p → p) rotx n p1 〉 
                      resp rotx n ∘ p1 ∘ ! (resp (λ p → p) n) ≃〈 {!!} 〉 
                      s ∘ p1 ∘ ! (resp (λ p → p) n) ≃〈 {!!} 〉 
                      s ∘ p1 ∘ ! n ≃〈 {!!} 〉 
                      p2 ∎)
                     (subst (λ p → p ≃ rotx p) s p1 ≃〈 subst-Id (λ p → p) rotx s p1 〉
                      resp rotx s ∘ p1 ∘ ! (resp (λ p → p) s) ≃〈 {!!} 〉 
                      n ∘ p1 ∘ ! (resp (λ p → p) s) ≃〈 {!!} 〉 
                      n ∘ p1 ∘ ! s ≃〈 {!!} 〉 
                      p2 ∎)
                     {!!}
                     {!!})
       where p1 = {!!}
             p2 = {!!}
-}
    open Loops

    n'body : (x : _) -> a' x ≃ b' x
    n'body = (S²-elim (\p -> p ≃ rotx p) 
                     Refl
                     Refl
                     (subst (λ p → p ≃ rotx p) n Refl ≃〈 subst-Id (λ p → p) rotx n Refl 〉 
                      resp rotx n ∘ Refl ∘ ! (resp (λ p → p) n) ≃〈 resp (λ x → x ∘ ( Refl ∘ ! (resp (λ p → p) n))) (Rec.βn _ _ _ _ _ _) 〉 
                      s ∘ Refl ∘ ! (resp (λ p → p) n) ≃〈 resp (λ x → s ∘ Refl ∘ ! x) (resp-id n) 〉 
                      s ∘ Refl ∘ ! n ≃〈 resp (λ x → s ∘ x) (∘-unit-l (! n)) 〉 
                      s ∘ ! n ≃〈 collapse-counterclockwise-b-fr 〉 
                      Refl ∎)
                     (subst (λ p → p ≃ rotx p) s Refl ≃〈 subst-Id (λ p → p) rotx s Refl 〉
                      resp rotx s ∘ Refl ∘ ! (resp (λ p → p) s) ≃〈 resp (λ x → x ∘ Refl ∘ ! (resp (λ p → p) s)) (Rec.βs _ _ _ _ _ _) 〉 
                      n ∘ Refl ∘ ! (resp (λ p → p) s) ≃〈 resp (λ x → n ∘ Refl ∘ ! x) (resp-id s) 〉 
                      n ∘ Refl ∘ ! s ≃〈 resp (λ x → n ∘ x) (∘-unit-l (! s)) 〉 
                      n ∘ ! s ≃〈 collapse-counterclockwise-a-fr 〉 
                      Refl ∎)
                     {!!}
                     {!!})

    n' : a' ≃ b' 
    n' = λ≃ n'body

    -- if you take n' = s' and do Refl's all the way up, the image of loop3 is Refl; see below
    s' : a' ≃ b'
    s' = n'
           
    fr' : n' ≃ s'
    fr' = Refl 
    
    ba' : n' ≃ s'
    ba' = Refl
    
    hfr' : fr' ≃ ba'
    hfr' = Refl

    hba' : fr' ≃ ba' 
    hba' = Refl

    module Loop3Image where
      -- if it's homomorphic, S³-rec will send loop3 to this
      -- FIXME: check that this actually works

      loop3-1' : Id a' b' -> Id a' a'
      loop3-1' = \ p -> ! n' ∘ p
    
      loop3-1-n' : Id (loop3-1' n') Refl
      loop3-1-n' = !-inv-l n'
    
      loop3-2' : Id{Id a' b'} n' s' -> Id{Id a' a'} Refl Refl 
      loop3-2' = \ p' -> loop3-1-n' ∘ resp loop3-1' (! p' ∘ p')  ∘ ! loop3-1-n'
    
      loop3-2-fr' : Id (loop3-2' fr') Refl
      loop3-2-fr' = !-inv-l n' ∘ resp (_∘_ (! n')) (! fr' ∘ fr') ∘ ! (!-inv-l n') ≃〈 resp (λ x → !-inv-l n' ∘ resp (_∘_ (! n')) x ∘ ! (!-inv-l n')) (!-inv-l fr') 〉
                    !-inv-l n' ∘ Refl ∘ ! (!-inv-l n') ≃〈 resp (λ x → !-inv-l n' ∘ x) (∘-unit-l (!(!-inv-l n'))) 〉 
                    !-inv-l n' ∘ ! (!-inv-l n') ≃〈 !-inv-r (!-inv-l n') 〉 
                    Refl ∎
    
      loop3' : Id {Id{Id a' a'} Refl Refl} Refl Refl
      loop3' = loop3-2-fr' ∘ resp loop3-2' (! hba' ∘ hfr') ∘ ! loop3-2-fr'

      test : loop3' ≃ Refl
      test = loop3-2-fr' ∘ resp loop3-2' (! hba' ∘ hfr') ∘ ! loop3-2-fr' ≃〈 Refl   〉 -- because hba' = hfr' = Refl
             loop3-2-fr' ∘ Refl ∘ ! loop3-2-fr' ≃〈 resp (λ x → loop3-2-fr' ∘ x) (∘-unit-l (! loop3-2-fr')) 〉
             loop3-2-fr' ∘ ! loop3-2-fr' ≃〈 !-inv-r loop3-2-fr' 〉 
             Refl ∎
      -- therefore (! hba' ∘ hfr') must be non-trivial to get a non-trivial image of loop3

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