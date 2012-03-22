{-# OPTIONS --type-in-type --without-K #-}

open import lib.BasicTypes 

module lib.spaces.3Sphere2 where

  open Paths

  module S³2 where
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

    postulate
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
            -> (n' : subst C n a' ≃ b') (s' : subst C s a' ≃ b')
            -> (fr' : subst (\ y -> Id (subst C y a') b') fr n' ≃ s') 
            -> (ba' : subst (\ y -> Id (subst C y a') b') ba n' ≃ s') 
            -> (x : S²) -> C x
    S²-elim C a' _ _ _ _ _ A = a'
    S²-elim C _ b' _ _ _ _ B = b'

    module Rec where 
     postulate
      βn :  {C : Set} 
             -> (a' : C)(b' : C)
             -> (n' : a' ≃ b') (s' : a' ≃ b')
             -> (fr' : n' ≃ s') (ba' : n' ≃ s')
             -> resp (S²-rec a' b' n' s' fr' ba') n ≃ n' 
      βs :  {C : Set} 
             -> (a' : C)(b' : C)
             -> (n' : a' ≃ b') (s' : a' ≃ b')
             -> (fr' : n' ≃ s') (ba' : n' ≃ s')
             -> resp (S²-rec a' b' n' s' fr' ba') s ≃ s' 
      βfr :  {C : Set} 
             -> (a' : C)(b' : C)
             -> (n' : a' ≃ b') (s' : a' ≃ b')
             -> (fr' : n' ≃ s') (ba' : n' ≃ s')
             -> resp (resp (S²-rec a' b' n' s' fr' ba')) fr ≃ (! (βs _ _ _ _ _ _) ∘ fr' ∘ βn _ _ _ _ _ _)
      βba :  {C : Set} 
             -> (a' : C)(b' : C)
             -> (n' : a' ≃ b') (s' : a' ≃ b')
             -> (fr' : n' ≃ s') (ba' : n' ≃ s')
             -> resp (resp (S²-rec a' b' n' s' fr' ba')) ba ≃ (! (βs _ _ _ _ _ _) ∘ ba' ∘ βn _ _ _ _ _ _)
-}

  open S³2

  -- FIXME prove equivalence with the 1-point formulation

  loop3-1 : Id a b -> Id a a
  loop3-1 = \ p -> ! n ∘ p

  loop3-1-n : Id (loop3-1 n) Refl
  loop3-1-n = !-inv-l n

  loop3-2 : Id{Id a b} n s -> Id{Id a a} Refl Refl 
  loop3-2 = \ p -> loop3-1-n ∘ resp loop3-1 (! p ∘ p)  ∘ ! loop3-1-n

  loop3-2-fr : Id (loop3-2 fr) Refl
  loop3-2-fr = !-inv-l n ∘ resp (_∘_ (! n)) (! fr ∘ fr) ∘ ! (!-inv-l n) ≃〈 resp (λ x → !-inv-l n ∘ resp (_∘_ (! n)) x ∘ ! (!-inv-l n)) (!-inv-l fr) 〉
               !-inv-l n ∘ Refl ∘ ! (!-inv-l n) ≃〈 resp (λ x → !-inv-l n ∘ x) (∘-unit-l (!(!-inv-l n))) 〉 
               !-inv-l n ∘ ! (!-inv-l n) ≃〈 !-inv-r (!-inv-l n) 〉 
               Refl ∎

  loop3 : Id {Id{Id {S³} a a} Refl Refl} Refl Refl
  loop3 = loop3-2-fr ∘ resp loop3-2 (! hba ∘ hfr) ∘ ! loop3-2-fr 
