{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude hiding (Z)
open PushoutFib
open ConnectedMap
open Truncation
open import lib.cubical.Cubical

module homotopy.blakersmassey.ThinFibered (X Y : Type) (P : X → Y → Type)
                                          (i' j' : TLevel)
                                          (cf : (x : X) → Connected (S i') (Σ \ y → P x y))
                                          (cg : (y : Y) → Connected (S j') (Σ \ x → P x y)) 
                                          where 

  i : TLevel
  i = S i'

  j : TLevel
  j = S j'

  i+j = plus2 i' j'

  W = PushoutFib.Pushout _ _ P

  wedge-zig : ∀ {x y'} (pxy' : P x y') 
             → ∀ (C : ∀ { x' y } → (pxy : P x y) (px'y' : P x' y') → Type)
                (nC : ∀ {x' y} → (pxy : P x y) (px'y' : P x' y') → NType i+j (C pxy px'y'))
            → (l : ∀ {x'} → (px'y' : P x' y') → C pxy' px'y')
            → (r : ∀ {y} → (pxy : P x y) → C pxy pxy')
            → (e : l pxy' == r pxy' )
            → ∀ {x' y} → (pxy : P x y) (px'y' : P x' y') → C pxy px'y'
  wedge-zig {x}{y'} pxy' C nC l r e {x'}{y} pxy  px'y' = ConnectedProduct.wedge-elim (cf x) (cg y')
                                                           (λ ppxy ppx'y' →
                                                              C (snd ppxy) (snd ppx'y') , nC (snd ppxy) (snd ppx'y'))
                                                           (Inr id) (λ z → l (snd z)) (λ z → r (snd z)) e (_ , pxy) (_ , px'y')

  abstract
    composeP : ∀ {x x' y y'} → (pxy : P x y) (pxy' : P x y') (px'y' : P x' y') 
               → Trunc (i+j) (Σ \ (px'y : P x' y) → Square {W} (glue pxy') (glue pxy) (! (glue px'y')) (! (glue px'y))) 
    composeP {x}{y'} pxy pxy' px'y' = 
        wedge-zig pxy' 
                  (\ {x'}{y} pxy px'y' → Trunc (i+j) (Σ \ (px'y : P x' y) → Square {W} (glue pxy') (glue pxy) (! (glue px'y')) (! (glue px'y))))
                  (\ _ _ -> Trunc-level) 
                  (λ pxy → [ pxy , connection2 ])
                  (λ px'y' → [ px'y' , inverses-square (glue pxy') (glue px'y') ]) 
                  (ap (λ z → [ pxy' , z ]) (! (inverses-connection-coh (glue pxy'))))
                  pxy px'y' 

    composePβ1 : ∀ {x x' y' } → (pxy' : P x y') (px'y' : P x' y') → composeP pxy' pxy' px'y' == [ px'y' , connection2 ]
    composePβ1 pxy' px'y' = ap≃ (ConnectedProduct.wedge-elim-βa _ _ _ _ _ _ _)
  
    composePβ2 : ∀ {x y y' } → (pxy : P x y) (pxy' : P x y') → composeP pxy pxy' pxy' == [ pxy , (inverses-square _ _) ]
    composePβ2 pxy' px'y' = ap≃ (ConnectedProduct.wedge-elim-βb _ _ _ _ _ _ _)
  
    composePcoh : ∀ {x y' } → (pxy' : P x y') → 
      Square (composePβ1 pxy' pxy') id (ap (λ z → [ pxy' , z ]) (! (inverses-connection-coh (glue pxy')))) (composePβ2 pxy' pxy')
    composePcoh pxy' = disc-to-square (! (ConnectedProduct.wedge-elim-coh _ _ _ _ _ _ _))

  
  composePtwice-body-2 : ∀ {x x' y y'} (pxy : P x y) (pxy' : P x y') (px'y' : P x' y') 
                        (px'y : P x' y) (s : Square {W} (glue pxy') (glue pxy) (! (glue px'y')) (! (glue px'y)))
                     → (Σ \ (pxy'2 : P x y') → Square (glue px'y) (glue px'y') (! (glue pxy)) (! (glue pxy'2)))
                     → Trunc i+j (Σ \ (pxy'2 : P x y') → Path {Path{W} (inl x) (inr y')} (glue pxy'2) (glue pxy'))
  composePtwice-body-2 pxy pxy' px'y' px'y s (pxy'2 , s2) = 
      -- combine the two squares into a path from the new copy to the original
      [ pxy'2 , ! (horiz-degen-square-to-path (whisker-square id (!-inv-l (glue pxy)) (!-inv-r (glue px'y')) (!-invol (glue pxy'2)) (s ·-square-h !-square-v s2))) ]

  composePtwice-body-1 : ∀ {x x' y y'} (pxy : P x y) (pxy' : P x y') (px'y' : P x' y') → 
                        (Σ \ (px'y : P x' y) → Square {W} (glue pxy') (glue pxy) (! (glue px'y')) (! (glue px'y))) 
                     → Trunc i+j (Σ \ (pxy'2 : P x y') → Path {Path{W} (inl x) (inr y')} (glue pxy'2) (glue pxy'))
  composePtwice-body-1 pxy pxy' px'y' (px'y , s) = Trunc-rec Trunc-level (composePtwice-body-2 pxy pxy' px'y' px'y s) (composeP px'y' px'y pxy)

  composePtwice : ∀ {x x' y y'} (pxy : P x y) (pxy' : P x y') (px'y' : P x' y') → 
                   Path {Trunc i+j (Σ \ (pxy'2 : P x y') → Path {Path{W} (inl x) (inr y')} (glue pxy'2) (glue pxy'))}
                        (Trunc-rec Trunc-level (composePtwice-body-1 pxy pxy' px'y') (composeP pxy pxy' px'y'))
                        [ pxy' , id ]
  composePtwice {x}{_}{_}{y'} pxy pxy' px'y' = 
      wedge-zig pxy' (\ {x'}{y} (pxy : P x y) (px'y' : P x' y') → Path (Trunc-rec Trunc-level (composePtwice-body-1 pxy pxy' px'y') (composeP pxy pxy' px'y')) [ pxy' , id ])
        (λ _ _ → path-preserves-level Trunc-level)
        (λ {x'} px'y' → (coh1 px'y' ∘
                          ap (Trunc-rec Trunc-level (composePtwice-body-2 pxy' pxy' px'y' px'y' connection2)) (composePβ1 px'y' pxy')) ∘
                          ap (Trunc-rec Trunc-level (composePtwice-body-1 pxy' pxy' px'y')) (composePβ1 pxy' px'y'))
        (λ {y} pxy → (coh2 pxy ∘ 
                       ap (Trunc-rec Trunc-level (composePtwice-body-2 pxy pxy' pxy' pxy (inverses-square (glue pxy') (glue pxy)))) (composePβ2 pxy' pxy)) ∘
                       ap (Trunc-rec Trunc-level (composePtwice-body-1 pxy pxy' pxy')) (composePβ2 pxy pxy'))
        (horiz-degen-square-to-path (ap-square (Trunc-rec Trunc-level (composePtwice-body-1 pxy' pxy' pxy')) (composePcoh pxy') ·-square-v
                                     sq2 ·-square-v
                                     coh12))
        pxy px'y' 
      where 
            -- second uses of composePβ are equal; need to turn connection2 into inverses-square in the function being app'ed as well
            sq2 : Square (ap (Trunc-rec Trunc-level (composePtwice-body-2 pxy' pxy' pxy' pxy' connection2)) (composePβ1 pxy' pxy'))
                         (ap (Trunc-rec Trunc-level (composePtwice-body-1 pxy' pxy' pxy')) (ap (λ z → [ pxy' , z ]) (! (inverses-connection-coh (glue pxy')))))
                         (ap (λ s → composePtwice-body-2 pxy' pxy' pxy' pxy' s (pxy' , s))
                             (! (inverses-connection-coh (glue pxy'))))
                         (ap (Trunc-rec Trunc-level (composePtwice-body-2 pxy' pxy' pxy' pxy' (inverses-square (glue pxy') (glue pxy'))))
                             (composePβ2 pxy' pxy'))
            sq2 = whisker-square id ((ap-o (Trunc-rec Trunc-level (composePtwice-body-1 pxy' pxy' pxy')) (λ z → [ pxy' , z ]) (! (inverses-connection-coh (glue pxy'))) ∘ 
                                      ! (ap-o (λ x₁ → x₁ (composeP pxy' pxy' pxy')) (λ s → Trunc-rec Trunc-level (composePtwice-body-2 pxy' pxy' pxy' pxy' s)) (! (inverses-connection-coh (glue pxy')))) ∘
                                      ! (ap-o (λ fx → fst fx (snd fx)) (λ x₁ → x₁ , composeP pxy' pxy' pxy') (ap (λ s → Trunc-rec Trunc-level (composePtwice-body-2 pxy' pxy' pxy' pxy' s)) (! (inverses-connection-coh (glue pxy')))))) ∘
                                         ap (ap (λ fx → fst fx (snd fx))) (pair×≃-id2 (ap (λ s → Trunc-rec Trunc-level (composePtwice-body-2 pxy' pxy' pxy' pxy' s)) (! (inverses-connection-coh (glue pxy'))))))
                                    ((ap-pair×≃-diag (λ a'b → composePtwice-body-2 pxy' pxy' pxy' pxy' (fst a'b) (pxy' , snd a'b)) (! (inverses-connection-coh (glue pxy'))) ∘
                                     ap-pair×≃-ap-2 (λ a'b → Trunc-rec Trunc-level (composePtwice-body-2 pxy' pxy' pxy' pxy' (fst a'b)) (snd a'b)) (λ z → [ pxy' , z ]) (! (inverses-connection-coh (glue pxy'))) (! (inverses-connection-coh (glue pxy')))) ∘
                                     ap-pair×≃-ap-1 (λ fx → fst fx (snd fx)) (λ s → Trunc-rec Trunc-level (composePtwice-body-2 pxy' pxy' pxy' pxy' s)) (! (inverses-connection-coh (glue pxy'))) (ap (λ z → [ pxy' , z ]) (! (inverses-connection-coh (glue pxy'))))) 
                                    id
                    (apply-line-to-square/tb
                     (ap (λ s → Trunc-rec Trunc-level (composePtwice-body-2 pxy' pxy' pxy' pxy' s)) (! (inverses-connection-coh (glue pxy'))))
                     (composePcoh pxy'))

            -- final coherence step for left
            coh1' : {A : Type} {x x' y' : A} (pxy' : x == y') (px'y' : x' == y')
                  → (! (horiz-degen-square-to-path (whisker-square id (!-inv-l pxy') (!-inv-r px'y') (!-invol pxy') (connection2 {p = pxy'}{q = ! px'y'} ·-square-h !-square-v connection2)))) == id
            coh1' id id = id
  
            coh1 : ∀ {x'} (px'y' : P x' y') -> (composePtwice-body-2 pxy' pxy' px'y' px'y' connection2 (pxy' , connection2)) == [ pxy' , id ]
            coh1 px'y' = ap (λ h → [ pxy' , h ]) (coh1' (glue pxy') (glue px'y'))

            -- final coherence step for right
            coh2' : {A : Type} {x y y' : A} (pxy : x == y) (pxy' : x == y')
                  → (! (horiz-degen-square-to-path (whisker-square id (!-inv-l pxy) (!-inv-r pxy') (!-invol pxy') (inverses-square pxy' pxy ·-square-h !-square-v (inverses-square pxy pxy'))))) == id
            coh2' id id = id

            coh2 : ∀ {y} (pxy : P x y) -> (composePtwice-body-2 pxy pxy' pxy' pxy (inverses-square (glue pxy') (glue pxy)) (pxy' , inverses-square (glue pxy) (glue pxy'))) == [ pxy' , id ]
            coh2 pxy = ap (λ h → [ pxy' , h ]) (coh2' (glue pxy) (glue pxy'))
            
            -- above two are equal
            coh12' : {A : Type} {x y : A} (pxy' : x == y) 
                   → Square (coh1' pxy' pxy') (ap (λ Z → ! (horiz-degen-square-to-path (whisker-square id (!-inv-l pxy') (!-inv-r pxy') (!-invol pxy') (Z ·-square-h !-square-v Z)))) (! (inverses-connection-coh pxy'))) id (coh2' pxy' pxy')
            coh12' id = id

            coh12 : Square (coh1 pxy') (ap (λ Z → composePtwice-body-2 pxy' pxy' pxy' pxy' Z (pxy' , Z)) (! (inverses-connection-coh (glue pxy')))) id (coh2 pxy')
            coh12 = whisker-square id (! (ap-o (λ h → [ pxy' , h ]) (λ Z → ! (horiz-degen-square-to-path (whisker-square id (!-inv-l (glue pxy')) (!-inv-r (glue pxy')) (!-invol (glue pxy')) (Z ·-square-h !-square-v Z)))) (! (inverses-connection-coh (glue pxy')))))
                                   id id
                                   (ap-square (λ h → [ pxy' , h ]) (coh12' (glue pxy')))

  gluel' : {x0 : X} {y0 : Y} (p0 : P x0 y0) {x : X} → P x y0 → Path {W} (inl x0) (inl x)
  gluel' p0 pxy0 = ! (glue pxy0) ∘ glue p0

  module Codes-glue where

    map' : {x0 : X} {y0 : Y} (p0 : P x0 y0) {x : X} {y   : Y} (pxy : P x y)
           {αx  : Path (inl x0) (inl x)} {αy  : Path (inl x0) (inr y)} (s : Square αx id (glue pxy) αy)
        → (HFiber (gluel' p0) αx) → Trunc i+j (HFiber (glue) αy)
    map' p0 pxy s (pxy0 , q) = 
      Trunc-rec Trunc-level 
        (λ c → [ fst c , 
                 -- massage the composite square into the required form, composing with s and q
                 square-to-disc s ∘ ap (λ z → glue pxy ∘ z) q ∘ square-to-disc-rearrange (square-symmetry (snd c)) ]) 
        (composeP pxy pxy0 p0)

    map : {x0 : X} {y0 : Y} (p0 : P x0 y0) {x   : X} {y   : Y} (pxy : P x y)
              {αx  : Path (inl x0) (inl x)} {αy  : Path (inl x0) (inr y)} (s : Square αx id (glue pxy) αy)
            → Trunc i+j (HFiber (gluel' p0 {x}) αx) → Trunc i+j (HFiber glue αy) 
    map p0 pxy s = Trunc-rec Trunc-level (map' p0 pxy s)


    backmap' : {x0 : X} {y0 : Y} (p0 : P x0 y0) {x   : X} {y   : Y} (pxy : P x y)
               {αx  : Path (inl x0) (inl x)} {αy  : Path (inl x0) (inr y)} (s : Square αx id (glue pxy) αy)
             → (HFiber glue αy) → Trunc i+j (HFiber (gluel' p0 {x}) αx) 
    backmap' p0 pxy s (px0y , q) = 
      Trunc-rec Trunc-level 
                (λ c → [ fst c , 
                         square-to-disc (!-square-h s) ∘ ap (λ Z → ! (glue pxy) ∘ Z) q ∘ square-to-disc (square-symmetry (snd c)) ]) 
                (composeP p0 px0y pxy)

    backmap : {x0 : X} {y0 : Y} (p0 : P x0 y0) {x   : X} {y   : Y} (pxy : P x y)
              {αx  : Path (inl x0) (inl x)} {αy  : Path (inl x0) (inr y)} (s : Square αx id (glue pxy) αy)
            → Trunc i+j (HFiber glue αy) → Trunc i+j (HFiber (gluel' p0 {x}) αx) 
    backmap p0 pxy s = Trunc-rec Trunc-level (backmap' p0 pxy s)


    composite1' : {x0 : X} {y0 : Y} (p0 : P x0 y0) {x   : X} {y   : Y} (pxy : P x y)
                  {αx  : Path (inl x0) (inl x)} {αy  : Path (inl x0) (inr y)} (s : Square αx id (glue pxy) αy)
                  (hf : HFiber glue αy)
               → map p0 pxy s (backmap' p0 pxy s hf) == [ hf ]
    composite1' p0 pxy s (px0y , id) = 
      map p0 pxy s (Trunc-rec Trunc-level (λ c → [ fst c , _ ]) (composeP p0 px0y pxy)) ≃〈 Trunc-rec-cconv i+j Trunc-level (λ c → [ fst c , _ ]) (map' p0 pxy s) (composeP p0 px0y pxy) 〉
      -- commuting convert
      Trunc-rec Trunc-level (\ c → Trunc-rec Trunc-level (\ c' → [ fst c' , _ ]) (composeP pxy (fst c) p0)) (composeP p0 px0y pxy) ≃〈 ap (λ F → Trunc-rec Trunc-level F (composeP p0 px0y pxy)) (λ≃ (λ c → ap (λ G → Trunc-rec Trunc-level G (composeP pxy (fst c) p0)) (λ≃ (λ c' → ap (λ Z → [ fst c' , Z ]) (coh s (snd c) (snd c')))))) 〉 
      -- use a coherence on the big path term elided with the _ 
      Trunc-rec Trunc-level (\ c → Trunc-rec Trunc-level (\ c' → [ fst c' , _ ]) (composeP pxy (fst c) p0)) (composeP p0 px0y pxy) ≃〈 composePtwice p0 px0y pxy 〉 
      -- use composePtwice
      [ px0y , id ] ∎ where
           coh1 : ∀ {A} {x0 : A} {p0 : x0 == x0} {αx : Path x0 x0} (x₁ : p0 == id) (x : αx == p0) → Id _ _ 
           coh1 id id = id

           coh : ∀ {A} {x0 y0 x y : A} {p0 : x0 == y0} {pxy : x == y} {fstc : x == y0} {fstc' : x0 == y} {αx : Path x0 x} {px0y : x0 == y} (s : Square αx id pxy px0y) (w : Square px0y p0 (! pxy) (! fstc)) (w₁ : Square fstc pxy (! p0) (! fstc')) →
               Id (square-to-disc s ∘ ap (_∘_ pxy) (square-to-disc (!-square-h s) ∘ id ∘ square-to-disc (square-symmetry w)) ∘ square-to-disc-rearrange (square-symmetry w₁))
                  (! (square-to-disc (whisker-square id (!-inv-l p0) (!-inv-r pxy) (!-invol fstc') (·-square-horiz w (!-square-v w₁))) ∘ ! (∘-unit-l px0y)))
           coh {p0 = p0} {pxy = id} {fstc = id} {fstc' = id} {αx} {px0y} = 
             horiz-degen-square-induction1 (λ {px0y₁} (s₁ : Square αx id id px0y₁) → (w : Square px0y₁ p0 id id) (w₁ : Square id id (! p0) id) → Id (square-to-disc s₁ ∘ ap (_∘_ id) (square-to-disc (!-square-h s₁) ∘ id ∘ square-to-disc (square-symmetry w)) ∘ square-to-disc-rearrange (square-symmetry w₁)) (! (square-to-disc (whisker-square id (!-inv-l p0) id id (·-square-horiz w (!-square-v w₁))) ∘ ! (∘-unit-l px0y₁))))
                                           (elim-along-equiv _ (!equiv square-disc-eqv) 
                                            (elim-along-equiv _ (!equiv (∘-unit-l-eqv-2 {p = αx} {q = p0})) 
                                              (λ x → elim-along-equiv _ (!equiv square-disc-eqv) (elim-along-equiv _ (!equiv move-!-right-eqv) (λ x₁ → coh1 {_} {_} {p0} {αx} x₁ x)))))

    
    composite2' : {x0 : X} {y0 : Y} (p0 : P x0 y0) {x   : X} {y   : Y} (pxy : P x y)
                  {αx  : Path (inl x0) (inl x)} {αy  : Path (inl x0) (inr y)} (s : Square αx id (glue pxy) αy)
                  → (hf : HFiber (gluel' p0 {x}) αx)
                  → backmap p0 pxy s (map' p0 pxy s hf) == [ hf ]
    composite2' p0 pxy {αy = αy} s (pxy0 , id) = 
      -- 4. commuting-convert like above
      backmap p0 pxy s (map' p0 pxy s (pxy0 , id)) ≃〈 Trunc-rec-cconv i+j Trunc-level (λ c → [ fst c , _ ]) (backmap' p0 pxy s) (composeP pxy pxy0 p0)  〉
      -- 3. coherence
      Trunc-rec Trunc-level (\ c → Trunc-rec Trunc-level (λ c' → [ fst c' , _ ]) (composeP p0 (fst c) pxy)) (composeP pxy pxy0 p0) ≃〈 ap (λ Z → Trunc-rec Trunc-level Z (composeP pxy pxy0 p0)) (λ≃ (λ c → ap (λ Z' → Trunc-rec Trunc-level Z' (composeP p0 (fst c) pxy)) (λ≃ (λ c' → ap (λ Z'' → [ fst c' , Z'' ]) (coh (glue p0) (glue pxy) (glue pxy0) s (glue (fst c)) (snd c) (glue (fst c')) (snd c')))))) 〉 
      -- 2. do some commuting conversions to walk the ! - ∘ glue p0 inside
      Trunc-rec Trunc-level (\ c → Trunc-rec Trunc-level (λ c' → [ fst c' , _ ]) (composeP p0 (fst c) pxy)) (composeP pxy pxy0 p0) ≃〈 !(ap (\ Z → Trunc-rec Trunc-level Z (composeP pxy pxy0 p0)) (λ≃ \ c → Trunc-rec-cconv i+j Trunc-level (composePtwice-body-2 pxy pxy0 p0 (fst c) (snd c)) (λ z → [ fst z , ap (λ x₁ → ! x₁ ∘ glue p0) (snd z) ]) (composeP p0 (fst c) pxy))) 〉 
      Trunc-rec Trunc-level (\ c → Trunc-rec Trunc-level (λ z → [ fst z , ap (λ x₁ → ! x₁ ∘ glue p0) (snd z) ]) (Trunc-rec Trunc-level (composePtwice-body-2 pxy pxy0 p0 (fst c) (snd c)) (composeP p0 (fst c) pxy))) (composeP pxy pxy0 p0) ≃〈 ! (Trunc-rec-cconv i+j Trunc-level (composePtwice-body-1 pxy pxy0 p0) (λ z → [ fst z , ap (λ x₁ → ! x₁ ∘ glue p0) (snd z) ]) (composeP pxy pxy0 p0)) 〉 
      -- 1. need to tack on the ! - ∘ glue p0 to be in the hfiber of gluel instead of glue [ not necessary above because of how composePtwice is phrased ]
      Trunc-func (λ z → fst z , ap (λ x₁ → ! x₁ ∘ glue p0) (snd z)) (Trunc-rec Trunc-level (composePtwice-body-1 pxy pxy0 p0) (composeP pxy pxy0 p0)) ≃〈 ap (Trunc-func (λ z → fst z , ap (λ x₁ → ! x₁ ∘ glue p0) (snd z))) (composePtwice pxy pxy0 p0) 〉 
      [ pxy0 , id ] ∎ where
        coh' : ∀ {A} {x0 : A} (fstc  : x0 == x0) (sndc  : id == fstc) (fstc' : x0 == x0) (sndc' : ! (id ∘ fstc) == fstc') → Path _ _
        coh' .id id ._ id = id

        coh : ∀ {A} {x0 y0 x y : A} (p0 : x0 == y0) (pxy : x == y) (pxy0 : x == y0) {αy  : Path x0 y}
                (s    : Square (! pxy0 ∘ p0) id pxy αy)
                (fstc    : x0 == y) (sndc : Square pxy0 pxy (! p0) (! fstc))
                (fstc'   : x == y0) (sndc' : Square (fstc) p0 (! pxy) (! fstc')) →
              Path (square-to-disc (!-square-h s) ∘ ap (_∘_ (! pxy))
                    (square-to-disc s ∘ id ∘ square-to-disc-rearrange (square-symmetry (sndc))) ∘ square-to-disc (square-symmetry (sndc')))
                   (ap (λ x₁ → ! x₁ ∘ p0) (! (horiz-degen-square-to-path (whisker-square id (!-inv-l pxy) (!-inv-r p0) (!-invol (fstc')) (sndc ·-square-h !-square-v (sndc'))))))
        coh {_}{x0} id id id = horiz-degen-square-induction1 (λ {αy₁} s₁ → (fstc : x0 == x0) (sndc : Square id id id (! fstc)) (fstc' : x0 == x0) (sndc' : Square fstc id id (! fstc')) → Path (square-to-disc (!-square-h s₁) ∘ ap (_∘_ id) (square-to-disc s₁ ∘ id ∘ square-to-disc-rearrange (square-symmetry sndc)) ∘ square-to-disc (square-symmetry sndc')) (ap (λ x₁ → ! x₁) (! (horiz-degen-square-to-path (whisker-square id id id (!-invol fstc') (sndc ·-square-h !-square-v sndc'))))))
                                 (λ fstc → elim-along-equiv _ (!equiv square-disc-eqv) (elim-along-equiv _ (move-!-right-eqv) (λ sndc → λ fstc' → elim-along-equiv _ (!equiv square-disc-eqv) (elim-along-equiv _ move-!-right-eqv (λ sndc' → coh' fstc sndc fstc' sndc')))))

    eqv : {x0 : X} {y0 : Y} (p0 : P x0 y0) {x : X} {y   : Y} (pxy : P x y)
          {αx  : Path (inl x0) (inl x)} {αy  : Path (inl x0) (inr y)} (s : Square αx id (glue pxy) αy)
        → Equiv (Trunc i+j (HFiber (gluel' p0 {x}) αx)) (Trunc i+j (HFiber glue αy))
    eqv p0 pxy s = improve (hequiv (map p0 pxy s)
                                   (backmap p0 pxy s)
                                   (Trunc-elim _ (λ _ → path-preserves-level Trunc-level) (composite2' p0 pxy s)) 
                                   (Trunc-elim _ (λ _ → path-preserves-level Trunc-level) (composite1' p0 pxy s)))

  module Codes (x0 : X) (y0 : Y) (p0 : P x0 y0) where

    gluel : {x : X} → P x y0 → inl x0 == inl x
    gluel = gluel' p0

    CodesFor : (w : W) (p : Path{W} (inl x0) w) → Type 
    CodesFor = Pushout-elim _ (λ x p → Trunc i+j (HFiber gluel p)) 
                              (λ y p → Trunc i+j (HFiber glue p))
                              (λ x y pxy → coe (! PathOverΠ-NDrange)
                              (λ αx αy s → ua (Codes-glue.eqv p0 pxy (PathOverPathFrom.out-PathOver-= s))))

    CodesFor' : (Σ \ (w : W) → Path{W} (inl x0) w) → Type 
    CodesFor' = uncurryd CodesFor

    transport-CodesFor'-glue : ∀ {x y} (pxy : P x y) {αx  : Path{W} (inl x0) (inl x)} {αy  : Path (inl x0) (inr y)} (s : PathOver (Path (inl x0)) (glue pxy) αx αy)
                               → transport CodesFor' (pair= (glue pxy) s) == Codes-glue.map p0 pxy (PathOverPathFrom.out-PathOver-= s) 
    transport-CodesFor'-glue pxy s = transport CodesFor' (pair= (glue pxy) s) ≃〈 transport-ap-assoc CodesFor' (pair= (glue pxy) s) 〉 
                                     coe (ap CodesFor' (pair= (glue pxy) s)) ≃〈 ap coe (ap-uncurryd-NDrange CodesFor _ _) 〉 
                                     coe (coe PathOverΠ-NDrange (apdo CodesFor (glue pxy)) _ _ s) ≃〈 ap (λ Z → coe (coe PathOverΠ-NDrange Z _ _ s)) (Pushout-elim/βglue _ _ _ (λ x y pxy₁ → coe (! PathOverΠ-NDrange) (λ αx αy s₁ → ua (Codes-glue.eqv p0 pxy₁ (PathOverPathFrom.out-PathOver-= s₁)))) _ _ _) 〉 
                                     coe (coe PathOverΠ-NDrange (coe (! PathOverΠ-NDrange)
                                           (λ αx αy s → ua (Codes-glue.eqv p0 pxy (PathOverPathFrom.out-PathOver-= s)))) _ _ s) ≃〈 ap (λ z → coe (z _ _ s)) (IsEquiv.β (snd (coe-equiv PathOverΠ-NDrange)) _) 〉 
                                     coe (ua (Codes-glue.eqv p0 pxy (PathOverPathFrom.out-PathOver-= s))) ≃〈 type≃β (Codes-glue.eqv p0 pxy (PathOverPathFrom.out-PathOver-= s)) 〉 
                                     Codes-glue.map p0 pxy (PathOverPathFrom.out-PathOver-= s) ∎

    forid : CodesFor (inl x0) id
    forid = [ p0 , !-inv-l (glue p0) ]

    redr : {y : Y} (px0y : P x0 y) → transport CodesFor' (pair= (glue px0y) connOver) forid == [ px0y , id ]
    redr px0y = transport CodesFor' (pair= (glue px0y) connOver) forid ≃〈 ap≃ (transport-CodesFor'-glue px0y connOver) 〉 
                Codes-glue.map p0 px0y (PathOverPathFrom.out-PathOver-= connOver) [ p0 , !-inv-l (glue p0) ]  ≃〈 id 〉 
                Trunc-rec Trunc-level (λ c → [ fst c , square-to-disc (PathOverPathFrom.out-PathOver-= connOver) ∘
                                                         ap (_∘_ (glue px0y)) (!-inv-l (glue p0)) ∘
                                                         square-to-disc-rearrange (square-symmetry (snd c)) ]) (composeP px0y p0 p0 ) ≃〈 ap (Trunc-rec Trunc-level (λ c → [ fst c , _ ])) (composePβ2 _ _) 〉 
                [ px0y , square-to-disc (PathOverPathFrom.out-PathOver-= connOver) ∘ ap (_∘_ (glue px0y)) (!-inv-l (glue p0)) ∘ square-to-disc-rearrange (square-symmetry (inverses-square (glue p0) (glue px0y))) ] ≃〈 ap (λ z → [ px0y , z ]) (coh (glue p0) (glue px0y)) 〉 
                [ px0y , id ] ∎ where
         coh : ∀ {A : Type} {a0 a1 a1' : A} (α : a0 == a1) (α' : a0 == a1')
               → square-to-disc (PathOverPathFrom.out-PathOver-= connOver) ∘ 
                  ap (_∘_ α') (!-inv-l α) ∘ 
                  square-to-disc-rearrange (square-symmetry (inverses-square α α')) == id
         coh id id = id

    encode : (w : W) (p : inl x0 == w) → (CodesFor w p)
    encode x p = transport CodesFor' (pair= p connOver) forid
  
    encode-decode-inr : (y : Y) (p : inl x0 == inr y) (c : HFiber glue p) → Path (encode (inr y) p) [ c ]
    encode-decode-inr y ._ (px0y , id) = (redr px0y)

    -- Trick: only do it for inr y! 
    -- This means you don't need to do the inl case, or show the two cases are the same, which is the big savings.
    -- This is similar to how you usually only need to do encode-after-decode for the point of interest.  
    -- However, we don't got a "polymorphic" result about Paths to an arbitrary w; is that ever helpful?  
    contr-r : (y : Y) (p : Path{W} (inl x0) (inr y)) → Contractible (CodesFor (inr y) p)
    contr-r y p = encode (inr y) p , Trunc-elim _ (λ _ → path-preserves-level Trunc-level) (encode-decode-inr y p)
  
  glue-connected' : ((x : X) (y : Y) (α : Path{W} (inl x) (inr y))
              → Contractible (Trunc i+j (HFiber (glue{a = x}{y}) α)))
  glue-connected' x y α = Trunc-rec (raise-HProp (Contractible-is-HProp _))
                                    (\ yp → Codes.contr-r x (fst yp) (snd yp) y α)
                                    (fst (use-level (cf x)))
  
  glue-connected : (x : X) (y : Y) → ConnectedMap i+j (glue{X}{Y}{P}{a = x}{y})
  glue-connected x y α = ntype (glue-connected' x y α)

  
  glue-map-total : (Σ \ xy → P (fst xy) (snd xy)) → Σ \ xy → Path{W} (inl (fst xy)) (inr (snd xy))
  glue-map-total ((x , y) , p) = ((x , y) , glue p)

  theorem : ConnectedMap i+j glue-map-total
  theorem = fiberwise-to-total-connected i+j (λ _ → glue) (λ xy → glue-connected (fst xy) (snd xy))

