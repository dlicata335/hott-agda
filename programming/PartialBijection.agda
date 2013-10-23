{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open Truncation

module programming.PartialBijection where

  _<->_ : Type → Type → Type
  A <-> B = (A → B) × (B → A)

  -- FIXME: need truncation?
  InDom : {A B : Type} (f : A → Maybe B) → A → Type
  InDom f x = Trunc -1 (Σ \ y → f x == Some y)

  InIm : {A B : Type} (f : A → Maybe B) → B → Type
  InIm f y = Trunc -1 (Σ \ x → f x == Some y)
  
  HSet-Maybe : {A : Type} → HSet A → HSet (Maybe A)
  HSet-Maybe = {!!}

  module B (A B : Type)
           (HSetA : HSet A) (HSetB : HSet B) -- FIXME: implied by below
           (decA : DecPath A)
           (decB : DecPath B) where

     record IsPartialBijection (f : A → Maybe B) : Type where
       constructor partialbij
       field
         g       : B → Maybe A
         adjoint : (x : A) (y : B) → (f x == Some y) <-> (Some x == g y)

{-
     record IsPartialBijection2 (f : A → Maybe B) : Type where
       constructor partialbij2
       field
         g : Σ (InIm f) → A
         adjoint : (x : A) (y : Σ (InIm f)) → (f x == Some (fst y)) <-> (x == g y)


     tob : (f : A → Maybe B) → (pb : IsPartialBijection2 f) → Equiv (Σ (InDom f)) (Σ (InIm f))
     tob f (partialbij2 g adj) = {!!} where
       total-on-dom1 : Σ (InDom f) → Σ (InIm f)
       total-on-dom1 (x , indom) with f x 
       ...                          | Some y = y , [ x , {!need inspect!} ]
       ...                          | None = {!!} , Trunc-func (\ p → Sums.abort {!snd p!}) indom

       on-im1 : (p : Σ (InIm f)) → (InDom f (g p))
       on-im1 (y , p') = [ y , snd (adj (g (y , p')) (y , p')) id ]
-}

{-
     works without truncations

     toequiv : (f : A → Maybe B) → IsPartialBijection f → Equiv (Σ (InDom f)) (Σ (InIm f))
     toequiv f (partialbij g adj) = improve (hequiv total-on-dom1 total-on-dom2 (λ _ → id) (λ _ → id)) where
       total-on-dom1 : Σ (InDom f) → Σ (InIm f)
       total-on-dom1 (x , y , eq) = y , x , eq

       total-on-dom2 : Σ (InIm f) → Σ (InDom f)
       total-on-dom2 (y , x , eq) = x , y , eq
-}

     fromequiv : (f : A → Maybe B) → (e : Equiv (Σ (InDom f)) (Σ (InIm f))) → IsPartialBijection f 
     fromequiv f (f' , isequiv g' α β _) = partialbij {!!} {!!} where
       g : B → Maybe A
       g b = Some (fst (g' (b , {!!})))

{-
     tob : (pb : PartialBijection) → Equiv (Σ (Dom (PartialBijection.f pb))) (Σ (Dom (PartialBijection.g pb)))
     tob (partialbij f g adj) = improve (hequiv total-on-dom1 total-on-dom2 (λ x → pair≃ id (pair≃ id (HSet-UIP (HSet-Maybe HSetB) _ _ _ _))) (λ y → pair≃ id (pair≃ id (HSet-UIP (HSet-Maybe HSetA) _ _ _ _))))  where 
       total-on-dom1 : Σ (Dom f) → Σ (Dom g)
       total-on-dom1 (x , y , eq) = y , x , ! (fst (adj x y) eq)

       total-on-dom2 : Σ (Dom g) → Σ (Dom f)
       total-on-dom2 (y , x , eq) = x , y , (snd (adj x y) (! eq))

     fromb : (f : A → Maybe B) (g : B → Maybe A) 
           → Equiv (Σ (Dom f)) (Σ (Dom g)) 
           → PartialBijection
     fromb f g (f' , isequiv g' α β _) = partialbij f g (λ x y → (λ p → {!  (α (x , y , p)) !}) , (λ q → {!!}))
-}
