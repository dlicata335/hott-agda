{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude hiding (Z)
open PushoutFib
open ConnectedMap
open Truncation
open import lib.cubical.Cubical

module homotopy.blakersmassey.Experiment5 (X Y : Type) (P : X → Y → Type)
                                          (i' j' : _)
                                          (cf : (x : X) → Connected (S i') (Σ \ y → P x y))
                                          (cg : (y : Y) → Connected (S j') (Σ \ x → P x y)) 
                                          (-1<=i' : -1 <=tl i') 
                                          (-1<=j' : -1 <=tl j') where

  ∘-unit-l-eqv-2 : ∀ {A} {a a' : A} {p q : a == a'} → Equiv (id ∘ p == id ∘ q) (p == q)
  ∘-unit-l-eqv-2 {p = id} {q} = improve (hequiv (λ p → ∘-unit-l q ∘ p) (λ p → ! (∘-unit-l q) ∘ p) {!!} {!!})

  move-!-right-eqv : ∀ {A} {a a' : A} {p : a == a'} {q : a' == a} → Equiv (! p == q) (p == ! q)
  move-!-right-eqv {p = id} {q} = improve (hequiv (λ p → ap ! p) (λ p → !-invol q ∘ ap ! p) {!!} {!!})

  ap-uncurryd-NDrange : {A : Type} {B : A → Type} {C : Type}
                (f : (x : A) → B x → C) {a0 a1 : A} {b0 : B a0} {b1 : B a1} (α : a0 == a1) (β : PathOver B α b0 b1)
                → ap (uncurryd f) (pair= α β) == coe PathOverΠ-NDrange (apdo f α) _ _ β 
  ap-uncurryd-NDrange _ .id id = {!!}

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
  
    composePcoh : ∀ {x y' } → (pxy' : P x y') → Square (composePβ1 pxy' pxy') id (ap (λ z → [ pxy' , z ]) (! (inverses-connection-coh (glue pxy')))) (composePβ2 pxy' pxy')
    composePcoh pxy' = disc-to-square (! (ConnectedProduct.wedge-elim-coh _ _ _ _ _ _ _))

    composePtwice : ∀ {x x' y y'} → (pxy : P x y) (pxy' : P x y') (px'y' : P x' y') →
                  Path {Trunc i+j (Σ \ (pxy'2 : P x y') → Path {Path{W} (inl x) (inr y')} (glue pxy'2) (glue pxy'))}
                       (Trunc-rec Trunc-level (λ { (px'y , s) → Trunc-rec Trunc-level (λ { (pxy'2 , s2) → [ pxy'2 , ! (horiz-degen-square-to-path
                                                                                                                      (whisker-square id (!-inv-l (glue pxy)) (!-inv-r (glue px'y')) (!-invol (glue pxy'2))
                                                                                                                        (s ·-square-h !-square-v s2))) ] }) (composeP px'y' px'y pxy) }) (composeP pxy pxy' px'y'))
                       [ pxy' , id ]
    composePtwice{x}{_}{_}{y'} pxy pxy' px'y' = 
      wedge-zig pxy' (\ {x'}{y} (pxy : P x y) (px'y' : P x' y') → Path {Trunc i+j (Σ \ (pxy'2 : P x y') → Path {Path{W} (inl x) (inr y')} (glue pxy'2) (glue pxy'))} (Trunc-rec Trunc-level (λ { (px'y , s) → Trunc-rec Trunc-level (λ { (pxy'2 , s2) → [ pxy'2 , ! (horiz-degen-square-to-path (whisker-square id (!-inv-l (glue pxy)) (!-inv-r (glue px'y')) (!-invol (glue pxy'2)) (s ·-square-h !-square-v s2))) ] }) (composeP px'y' px'y pxy) }) (composeP pxy pxy' px'y')) [ pxy' , id ])
        (λ _ _ → path-preserves-level Trunc-level)
        (λ {x'} px'y' → {!!})
        {!!}
        {!!}
        pxy px'y'

  gluel' : {x0 : X} {y0 : Y} (p0 : P x0 y0) {x : X} → P x y0 → Path {W} (inl x0) (inl x)
  gluel' p0 pxy0 = ! (glue pxy0) ∘ glue p0

  module Codes-glue where

    map' : {x0 : X} {y0 : Y} (p0 : P x0 y0) {x : X} {y   : Y} (pxy : P x y)
           {αx  : Path (inl x0) (inl x)} {αy  : Path (inl x0) (inr y)} (s : Square αx id (glue pxy) αy)
        → (HFiber (gluel' p0) αx) → Trunc i+j (HFiber (glue) αy)
    map' p0 pxy s (pxy0 , q) = 
      Trunc-rec Trunc-level 
                (λ c → [ fst c , square-to-disc s ∘ ap (λ z → glue pxy ∘ z) q ∘ square-to-disc-rearrange (square-symmetry (snd c)) ]) 
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
                (λ c → [ fst c , square-to-disc (!-square-h s) ∘ ap (λ Z → ! (glue pxy) ∘ Z) q ∘ square-to-disc (square-symmetry (snd c)) ]) 
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
      map p0 pxy s (backmap' p0 pxy s (px0y , id)) ≃〈 id 〉
      map p0 pxy s (Trunc-rec Trunc-level (λ c → [ fst c , _ ]) (composeP p0 px0y pxy)) ≃〈 Trunc-rec-cconv i+j Trunc-level (λ c → [ fst c , _ ]) (map' p0 pxy s) (composeP p0 px0y pxy) 〉
      Trunc-rec Trunc-level (\ c → Trunc-rec Trunc-level (\ c' → [ fst c' , _ ]) (composeP pxy (fst c) p0))
                           (composeP p0 px0y pxy) ≃〈 ap (λ F → Trunc-rec Trunc-level F (composeP p0 px0y pxy)) (λ≃ (λ c → ap (λ G → Trunc-rec Trunc-level G (composeP pxy (fst c) p0)) (λ≃ (λ c' → ap (λ Z → [ fst c' , Z ]) 
                                                        (coh s (snd c) (snd c')))))) 〉 
      Trunc-rec Trunc-level (\ c → Trunc-rec Trunc-level (\ c' → [ fst c' , _ ]) (composeP pxy (fst c) p0)) (composeP p0 px0y pxy) ≃〈 composePtwice p0 px0y pxy 〉 
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

    eqv : {x0 : X} {y0 : Y} (p0 : P x0 y0) {x : X} {y   : Y} (pxy : P x y)
          {αx  : Path (inl x0) (inl x)} {αy  : Path (inl x0) (inr y)} (s : Square αx id (glue pxy) αy)
        → Equiv (Trunc i+j (HFiber (gluel' p0 {x}) αx)) (Trunc i+j (HFiber glue αy))
    eqv p0 pxy s = improve (hequiv (map p0 pxy s)
                                   (backmap p0 pxy s)
                                   {!!} 
                                   (Trunc-elim _ (λ _ → path-preserves-level Trunc-level) (composite1' p0 pxy s)))

{-
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


-}
