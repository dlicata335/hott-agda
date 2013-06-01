{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open FatPushout
open ConnectedMap
open Truncation

module homotopy.BlakersMasseyInfTopos (Z X Y : Type) 
                                      (i' j' : _)
                                      (f : Z → X) (g : Z → Y)
                                      (cf : ConnectedMap (S i') f) (cg : ConnectedMap (S j') g) where

  i : TLevel
  i = S i'

  j : TLevel
  j = S j'

  i+j = plus2 i' j'

  W = Pushout f g

  Pullback : ∀ {Z X Y : Type} → (f : X → Z) (g : Y → Z) → Type
  Pullback {_}{X}{Y} f g = Σ \ x -> Σ \ y -> f x ≃ g y

  Path-Pullback : ∀ {Z X Y : Type} → (f : X → Z) (g : Y → Z) → 
                  ∀ {x x' y y' p p'} 
                  → Path{Pullback f g} (x , y , p) (x' , y' , p')
                  ≃ Σ \(px : Path x x') -> Σ \(py : Path y y') → ap g py ∘ p ≃ p' ∘ ap f px
  Path-Pullback f g = {!!}
                                       
  X×WY = Pullback{W} inl inr 

  gluelr : (z : Z) → Path{W} (inl (f z)) (inr (g z))
  gluelr z = gluer z ∘ gluel z

  glue : Z → X×WY 
  glue z = (f z , g z , gluer z ∘ gluel z)

  Z×WY = Pullback{W} inm inr
  X×WZ = Pullback{W} inl inm
  Z×WZ = Pullback{W} inm inm

  module CodesTT where
    Codes : (z : Z) (w : W) → Path (inm z) w → Type
    Codes z = Pushout-elim _ 
                           (λ x p → Trunc i+j (HFiber glue (x , g z , (gluer z ∘ ! p))))
                           (λ z' p → Trunc i+j (HFiber glue (f z , g z' , gluer z' ∘ p ∘ gluel z))) -- FIXME choice of which side z/z' go on
                           (λ y p → Trunc i+j (HFiber glue (f z , y , p ∘ gluel z)))
                           {!!}
                           {!!}

  postulate
      Codes-contr : (z : Z) (w : W) (p : Path (inm z) w) → Contractible (CodesTT.Codes z w p)

  module Step1Symmetric where
    step2 : (z1 z2 : Z) (p : inl (f z1) ≃ inr (g z2))
          -> Contractible (Trunc i+j (HFiber glue (f z1 , g z2 , p)))
    step2 z1 z2 p = transport (\ x -> Contractible (Trunc i+j (HFiber glue (f z1 , g z2 , x))))
                              {!!}
                              (Codes-contr z1 (inm z2) (! (gluer z2) ∘ p ∘ ! (gluel z1)))
  
    step1 : (x : X) (y : Y) (p : Path{W} (inl x) (inr y)) 
          → Contractible (Trunc i+j (HFiber glue (x , y , p)))
    step1 = extend i f cf
              (λ x' →
                 ((y' : _) (p' : _) → Contractible (Trunc i+j (HFiber glue (x' , y' , p')))) ,
                  raise-HProp (Πlevel (λ _ → Πlevel (λ _ → Contractible-is-HProp _))))
              (λ z1 →
                   extend j g cg
                   (λ y' → ((p' : _) → Contractible (Trunc i+j (HFiber glue (f z1 , y' , p')))) ,
                           raise-HProp (Πlevel (λ _ → Contractible-is-HProp _)))
                   (λ z2 p → step2 z1 z2 p)) 

  module Step1Left where
    step2 : (z1 : Z) (y : Y) (p : inl (f z1) ≃ inr y)
          -> Contractible (Trunc i+j (HFiber glue (f z1 , y , p)))
    step2 = {!!}
  
    step1 : (x : X) (y : Y) (p : Path{W} (inl x) (inr y)) 
          → Contractible (Trunc i+j (HFiber glue (x , y , p)))
    step1 = extend i f cf
              (λ x' →
                 ((y' : _) (p' : _) → Contractible (Trunc i+j (HFiber glue (x' , y' , p')))) ,
                  raise-HProp (Πlevel (λ _ → Πlevel (λ _ → Contractible-is-HProp _))))
              step2

  module ∞ToposStep1Left where
    Z×XZ = Pullback{X} f f 

    1×g : Z×XZ → Z×WY
    1×g (z1 , z2 , p) = z1 , g z2 , (gluelr z2 ∘ ap inl p) ∘ ! (gluel z1)

    -- gap between type theoretic proof and ∞topos proof
    -- in the infinity topos proof, you next show 
    Step2-∞Topos = (z1 : Z) (y : Y) (p : inm z1 ≃ inr y) → Contractible (Trunc i+j (HFiber 1×g (z1 , y , p)))
    -- in the type-theoretic proof, you next show 
    Step2-TT = (z1 : Z) (y : Y) (p : inl (f z1) ≃ inr y) -> Contractible (Trunc i+j (HFiber glue (f z1 , y , p)))

    -- didn't fill in the proof terms, but this works
    eq : Step2-∞Topos ≃ Step2-TT 
    eq = ap {M = \ z y → (p : inm z ≃ inr y) → Contractible (Trunc i+j (HFiber 1×g (z , y , p)))} 
            (λ B → (z : Z) (y : Y) → B z y)
            (λ≃ (λ z → λ≃ (λ y → apΠ' (pre∘-equiv (gluel z))
                                       (λ p → ap (λ A → Contractible (Trunc i+j A)) (STS z y p))))) where
       STS : ∀ z y p → (HFiber 1×g (z , y , p ∘ ! (gluel z)))
                      ≃ (HFiber glue (f z , y , p)) 
       STS z y p = 
           HFiber 1×g (z , y , p ∘ ! (gluel z)) ≃〈 {!!} 〉 
           (Σ \ z1 → Σ \ z2 -> Σ \ (p12 : f z1 ≃ f z2) → 1×g (z1 , z2 , p12) ≃ (z , y , p ∘ ! (gluel z))) ≃〈 {!!} 〉 
           (Σ \ z1 → Σ \ z2 -> Σ \ (p12 : f z1 ≃ f z2) → Path{Z×WY} (z1 , g z2 , (gluelr z2 ∘ ap inl p12 ∘ ! (gluel z1))) (z , y , p ∘ ! (gluel z))) ≃〈 {!!} 〉 

           (Σ \ z2 ->
            Σ \ (p12 : f z ≃ f z2) →
            Σ \ (py : Path (g z2) y) → 
                ap inr py ∘ (gluelr z2 ∘ ap inl p12 ∘ ! (gluel z))
                ≃ p ∘ ! (gluel z)) ≃〈 {!!} 〉 -- rearrange; the ! comes from p12 and p12' being flipped

            (Σ \ z2 ->
             Σ \ (p12' : f z2 ≃ f z) ->
             Σ \ (py : g z2 ≃ y) → 
               ap inr py ∘ gluelr z2 ≃ p ∘ ap inl p12') ≃〈 {!!} 〉

            (Σ \ z2 -> Path{X×WY} (f z2 , g z2 , gluelr z2) (f z , y , p)) ≃〈 id 〉
            (_ ∎)

    step1 : Step2-∞Topos 
          → ((x : X) (y : Y) (p : Path{W} (inl x) (inr y)) 
              → Contractible (Trunc i+j (HFiber glue (x , y , p))))
    step1 step2 = extend i f cf  -- ENH: copied from above
              (λ x' →
                 ((y' : _) (p' : _) → Contractible (Trunc i+j (HFiber glue (x' , y' , p')))) ,
                  raise-HProp (Πlevel (λ _ → Πlevel (λ _ → Contractible-is-HProp _))))
              (coe eq step2)
          
  theorem : ConnectedMap i+j glue
  theorem (x , y , p) = ntype (∞ToposStep1Left.step1 {!!} x y p)
