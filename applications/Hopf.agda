{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open Paths

module applications.Hopf where

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

    roty : S² -> S²
    roty = S²-rec b a (! s) (! n) (! (resp ! ba)) (! (resp ! fr))
  
    rotz : S² -> S²
    rotz = S²-rec b a (! s) (! n) (! (resp ! fr)) (! (resp ! ba)) 

    a' = id
    b' = rotz

    open Loops

    n'body : (x : _) -> a' x ≃ b' x
    n'body = 
           (S²-elim (λ x → Id x (rotz x)) 
                     n 
                     (! s) 
                     (subst (λ p → p ≃ rotz p) n n ≃〈 subst-Id (λ p → p) rotz n n 〉
                      resp rotz n ∘ n ∘ ! (resp (λ p → p) n) ≃〈 resp (λ x → x ∘ n ∘ ! (resp (λ p → p) n)) (Rec.βn _ _ _ _ _ _) 〉
                      ! s ∘ n ∘ ! (resp (λ p → p) n) ≃〈 resp (λ x → ! s ∘ n ∘ ! x) (resp-id n) 〉 
                      ! s ∘ n ∘ ! n ≃〈 resp (λ x → ! s ∘ x) (!-inv-r n) 〉 
                      ! s ∎)
                     (subst (λ p → p ≃ rotz p) s n ≃〈 subst-Id (λ p → p) rotz s n 〉
                        resp rotz s ∘ n ∘ ! (resp (λ p → p) s) ≃〈 resp (λ x → x ∘ n ∘ ! (resp (λ p → p) s)) (Rec.βs _ _ _ _ _ _) 〉
                        ! n ∘ n ∘ ! (resp (λ p → p) s) ≃〈 ∘-assoc (! n) n (! (resp (λ x → x) s)) 〉
                        (! n ∘ n) ∘ ! (resp (λ p → p) s) ≃〈 resp (λ x → x ∘ ! (resp (λ p → p) s)) (!-inv-l n) 〉 
                        Refl ∘ ! (resp (λ p → p) s) ≃〈 resp (λ x → Refl ∘ ! x) (resp-id s) 〉 
                        Refl ∘ ! s ≃〈 ∘-unit-l (! s) 〉 
                        (! s ∎)) 
                     {!!} 
                     {!!})

    n' : a' ≃ b' -- clockwise
    n' = λ≃ n'body

    s'body : (x : _) -> a' x ≃ b' x
    s'body = 
            (S²-elim (λ x → Id x (rotz x)) 
                     s 
                     (! n) 
                     (subst (λ p → p ≃ rotz p) n s ≃〈 subst-Id (λ p → p) rotz n s 〉
                        resp rotz n ∘ s ∘ ! (resp (λ p → p) n) ≃〈 resp (λ x → x ∘ s ∘ ! (resp (λ p → p) n)) (Rec.βn _ _ _ _ _ _) 〉
                        ! s ∘ s ∘ ! (resp (λ p → p) n) ≃〈 resp (λ x → ! s ∘ s ∘ ! x) (resp-id n) 〉
                        ! s ∘ s ∘ ! n ≃〈 ∘-assoc (! s) s (! n) 〉 
                        (! s ∘ s) ∘ ! n ≃〈 resp (λ x → x ∘ ! n) (!-inv-l s) 〉 
                        Refl ∘ ! n ≃〈 ∘-unit-l (! n) 〉 
                        ! n ∎)
                     (subst (λ p → p ≃ rotz p) s s ≃〈 subst-Id (λ p → p) rotz s s 〉
                        resp rotz s ∘ s ∘ ! (resp (λ p → p) s) ≃〈 resp (λ x → x ∘ s ∘ ! (resp (λ p → p) s)) (Rec.βs _ _ _ _ _ _) 〉
                        ! n ∘ s ∘ ! (resp (λ p → p) s) ≃〈 resp (λ x → ! n ∘ s ∘ ! x) (resp-id s) 〉
                        ! n ∘ s ∘ ! s ≃〈 resp (λ x → ! n ∘ x) (!-inv-r s) 〉 
                        ! n ∎)
                     {!!} 
                     {!!})

    s' : a' ≃ b' -- counterclockwise
    s' = λ≃ s'body

    fr'body : (x : _) -> n'body x ≃ s'body x 
    fr'body = (S²-elim (λ x → n'body x ≃ s'body x) 
                               fr 
                               {! resp (\ x -> ! s ∘ x ∘ ! n) fr !}
                               ((subst (λ x → n'body x ≃ s'body x) n fr) ≃〈 {!!} 〉 
                                respd s'body n ∘ resp (subst (λ x → a' x ≃ b' x) n) fr ∘ ! (respd n'body n) ≃〈 {!!} 〉 -- outsides are β-subst β-hit and groupoid so they should in some sense go away 
--                                resp (subst (λ x → a' x ≃ b' x) n) fr ≃〈 def subst ≃ 〉 
--                                (resp (\ x -> resp b' n ∘ x ∘ resp a' n) fr) ≃〈 β + unit 〉 
--                                (resp (\ x -> ! s ∘ x) fr) ≃〈 {!!} 〉 
                                (! (resp ! ba)) ∎)
                               {!resp (subst (λ x → a' x ≃ b' x) n) fr!}
                               {!!} {!!})

    fr' : n' ≃ s' 
    fr' = resp λ≃ (λ≃ fr'body)
    
    ba'body : (x : _) -> n'body x ≃ s'body x 
    ba'body = (S²-elim (λ x → n'body x ≃ s'body x) 
                              fr                   -- has to be homotopic to fr for the next level
                              (! (resp ! ba)) 
                              {!!} {!!} {!!} {!!})

    ba' : n' ≃ s' 
    ba' = resp λ≃ (λ≃ ba'body)
    
    hfr' : fr' ≃ ba'
    hfr' = resp (resp λ≃ o λ≃) (λ≃ (S²-elim (λ x → fr'body x ≃ ba'body x) 
                                   Refl 
                                   Refl 
                                   {!!} {!!} {!!} {!!}))

    hba' : fr' ≃ ba' 
    hba' = {!!}

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