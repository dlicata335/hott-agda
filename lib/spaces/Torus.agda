{-# OPTIONS --type-in-type --without-K #-}

open import lib.BasicTypes 
open import lib.cubical.Cubical
import lib.PrimTrustMe

module lib.spaces.Torus where

module Torus where
  private
    module T where
     private
        data ##T : Type where
          #a : ##T

        data #T : Type where
          #in : (Unit -> ##T) → #T

        #out : #T -> ##T
        #out (#in f) = f <>

        ext : (x : #T) (y : ##T) → #out x == y → #in (\ _ -> y) == x
        ext (#in f) y p = lib.PrimTrustMe.transport/PId (λ x → #in (λ _ → y) == x) (lib.PrimTrustMe.ap/PId #in (lib.PrimTrustMe.funext/primtrustme {f = λ _ → y} {g = f} (λ _ → transport (λ z → lib.PrimTrustMe.PId y z) (! p) lib.PrimTrustMe.Refl))) id 
     
     T : Set
     T = #T
  
     a : T
     a = #in (\ _ -> #a)
  
     postulate {- HoTT Axiom -}
       p : a ≃ a
       q : a ≃ a
       f : Square p q q p
  
     T-rec :  {C : Set}
           -> (a' : C)
           -> (p' q' : a' ≃ a')
           -> (f' : Square p' q' q' p')
           -> T -> C
     T-rec {C} a' p' q' f' x = T-rec' phantom phantom phantom (#out x) id where
        T-rec' : (_ : Phantom p') (_ : Phantom q') (_ : Phantom f') -> (x' : ##T) -> x' == #out x -> C
        T-rec' phantom phantom phantom #a p = a'
  
     T-elim : (C : T -> Set)
              (a' : C a) 
              (p' : PathOver C p a' a') 
              (q' : PathOver C q a' a')
              (f' : SquareOver C f p' q' q' p') 
           -> (x : T) -> C x
     T-elim C a' p' q' f' x = T-elim' phantom phantom phantom (#out x) id where
        T-elim' : (_ : Phantom p') (_ : Phantom q') (_ : Phantom f') -> (x' : ##T) -> #out x == x' -> C x
        T-elim' phantom phantom phantom #a p = transport C (ext _ _ p) a'

  
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


  module UMP where

     -- this is a special case of in-PathOver-Square with some reduction.  
     -- but it was too annoying to do the reduction, and too easy to just do by path induction
     in-PathOver-Square' : {A : Type} {a0 : A} {p p' : a0 == a0} {q q' : a0 == a0} {ps : p == p'} {qs : q == q'}
                        {f : Square p q q p} {f' : Square p' q' q' p'}
                      → Cube f f' (horiz-degen-square ps) (horiz-degen-square qs) (horiz-degen-square qs) (horiz-degen-square ps)  
                      → PathOver (λ pq → Square (fst pq) (snd pq) (snd pq) (fst pq))
                                  (pair×≃ ps qs) f f' 
     in-PathOver-Square' {ps = id} {qs = id} c = hom-to-over/left _ (CubePath.cube-to-path/degen-tube c)

     T-rec-prem : Type → Type
     T-rec-prem X = 
              Σ \ (a : X) → 
              Σ \ (pq : Path a a × Path a a) → 
              Square (fst pq) (snd pq) (snd pq) (fst pq)
   
     apply-to-constructors : ∀ {X} → (T → X) → (T-rec-prem X)
     apply-to-constructors g = g a , (ap g p , ap g q) , ap-square g f

     T-recΣ : ∀ {X} → (T-rec-prem X) → (T → X) 
     T-recΣ = (λ z → T-rec (fst z) (fst (fst (snd z))) (snd (fst (snd z))) (snd (snd z)))
   
     η : {X : Type} (g : T → X) → T-recΣ (apply-to-constructors g) == g
     η g = λ≃ (T-elim _ id (PathOver=.in-PathOver-= (vertical-degen-square (βp/rec _ _ _ _))) 
                            (PathOver=.in-PathOver-= (vertical-degen-square (βq/rec _ _ _ _))) 
                            (SquareOver=ND.in-SquareOver-= 
                              (whisker-cube (! (IsEquiv.β (snd PathOver=.out-PathOver-=-eqv) _))
                                            (! (IsEquiv.β (snd PathOver=.out-PathOver-=-eqv) _))
                                            (! (IsEquiv.β (snd PathOver=.out-PathOver-=-eqv) _)) 
                                            id id (! (IsEquiv.β (snd PathOver=.out-PathOver-=-eqv) _)) 
                                            (whisker-cube (horiz-degen-square-symmetry _) 
                                                          (horiz-degen-square-symmetry _)
                                                          (horiz-degen-square-symmetry _)
                                                          id id 
                                                          (horiz-degen-square-symmetry _)
                                               (cube-symmetry-left-to-top (βf/rec _ _ _ _))))))

     β : {X : Type} (a'p'q'f' : T-rec-prem X) → apply-to-constructors (T-recΣ a'p'q'f') == a'p'q'f'
     β (a' , (p' , q') , f') = 
         ap (λ x → a' , x) 
            (pair= (pair×≃ (βp/rec a' p' q' f') (βq/rec a' p' q' f'))
                   (in-PathOver-Square' (βf/rec _ _ _ _))) 

     ump : ∀ {X} → Equiv (T → X) (T-rec-prem X)
     ump = improve (hequiv apply-to-constructors T-recΣ η β)

     T→ext : ∀ {X} (f g : T → X) → apply-to-constructors f == apply-to-constructors g → f == g
     T→ext f g p = ! (η f) · ap T-recΣ p · η g
