{-# OPTIONS --type-in-type --new-without-K #-}

open import lib.BasicTypes 

module lib.spaces.3Sphere2 where

  

  module S³2 where
   module S where
    private
      data S3 : Set where
        A : S3
        B : S3

    S³ : Set
    S³ = S3

    a : S³
    a = A

    b : S³
    b = B

    postulate {- HoTT Axiom -}
      n : a ≃ b
      s : a ≃ b
      fr : n ≃ s
      ba : n ≃ s
      hfr : fr ≃ ba
      hba : fr ≃ ba

    S³-rec : {C : Set} 
           -> (a' : C)(b' : C)
           -> (n' : a' ≃ b') (s' : a' ≃ b')
           -> (fr' : n' ≃ s') (ba' : n' ≃ s')
           -> (hfr' : fr' ≃ ba') (hba' : fr' ≃ ba')
           -> S³ -> C
    S³-rec a' _ _ _ _ _ _ _ A = a'
    S³-rec _ b' _ _ _ _ _ _ B = b'

    -- FIXME
{-
    S²-elim : (C : S² -> Set)
            -> (a' : C a)(b' : C b)
            -> (n' : transport C n a' ≃ b') (s' : transport C s a' ≃ b')
            -> (fr' : transport (\ y -> Path (transport C y a') b') fr n' ≃ s') 
            -> (ba' : transport (\ y -> Path (transport C y a') b') ba n' ≃ s') 
            -> (x : S²) -> C x
    S²-elim C a' _ _ _ _ _ A = a'
    S²-elim C _ b' _ _ _ _ B = b'

    module Rec where 
     postulate {- HoTT Axiom -}
      βn :  {C : Set} 
             -> (a' : C)(b' : C)
             -> (n' : a' ≃ b') (s' : a' ≃ b')
             -> (fr' : n' ≃ s') (ba' : n' ≃ s')
             -> ap (S²-rec a' b' n' s' fr' ba') n ≃ n' 
      βs :  {C : Set} 
             -> (a' : C)(b' : C)
             -> (n' : a' ≃ b') (s' : a' ≃ b')
             -> (fr' : n' ≃ s') (ba' : n' ≃ s')
             -> ap (S²-rec a' b' n' s' fr' ba') s ≃ s' 
      βfr :  {C : Set} 
             -> (a' : C)(b' : C)
             -> (n' : a' ≃ b') (s' : a' ≃ b')
             -> (fr' : n' ≃ s') (ba' : n' ≃ s')
             -> ap (ap (S²-rec a' b' n' s' fr' ba')) fr ≃ (! (βs _ _ _ _ _ _) ∘ fr' ∘ βn _ _ _ _ _ _)
      βba :  {C : Set} 
             -> (a' : C)(b' : C)
             -> (n' : a' ≃ b') (s' : a' ≃ b')
             -> (fr' : n' ≃ s') (ba' : n' ≃ s')
             -> ap (ap (S²-rec a' b' n' s' fr' ba')) ba ≃ (! (βs _ _ _ _ _ _) ∘ ba' ∘ βn _ _ _ _ _ _)
-}
   open S public
 
   -- FIXME prove equivalence with the 1-point formulation
 
   loop3-1 : Path a b -> Path a a
   loop3-1 = \ p -> ! n ∘ p
 
   loop3-1-n : Path (loop3-1 n) id
   loop3-1-n = !-inv-l n
 
   loop3-2 : Path{Path a b} n s -> Path{Path a a} id id 
   loop3-2 = \ p -> loop3-1-n ∘ ap loop3-1 (! p ∘ p)  ∘ ! loop3-1-n
 
   loop3-2-fr : Path (loop3-2 fr) id
   loop3-2-fr = !-inv-l n ∘ ap (_∘_ (! n)) (! fr ∘ fr) ∘ ! (!-inv-l n) ≃〈 ap (λ x → !-inv-l n ∘ ap (_∘_ (! n)) x ∘ ! (!-inv-l n)) (!-inv-l fr) 〉
                !-inv-l n ∘ id ∘ ! (!-inv-l n) ≃〈 ap (λ x → !-inv-l n ∘ x) (∘-unit-l (!(!-inv-l n))) 〉 
                !-inv-l n ∘ ! (!-inv-l n) ≃〈 !-inv-r (!-inv-l n) 〉 
                id ∎
 
   loop3 : Path {Path{Path {S³} a a} id id} id id
   loop3 = loop3-2-fr ∘ ap loop3-2 (! hba ∘ hfr) ∘ ! loop3-2-fr 
