{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude hiding (Z)
open PushoutFib
open ConnectedMap
open Truncation
open import lib.cubical.Cubical

module homotopy.blakersmassey.Experiment2 (X Y : Type) (P : X → Y → Type)
                                          (i' j' : _)
                                          (cf : (x : X) → Connected (S i') (Σ \ y → P x y))
                                          (cg : (y : Y) → Connected (S j') (Σ \ x → P x y)) where

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

  abstract
    composeP : ∀ {x x' y y'} → (pxy : P x y) (pxy' : P x y') (px'y' : P x' y') 
               → Trunc (i+j) (Σ \ (px'y : P x' y) → Square {W} (glue pxy) (glue pxy') (! (glue px'y)) (! (glue px'y'))) 
    composeP {x}{x'}{y}{y'} pxy pxy' px'y' = 
      ConnectedProduct.wedge-elim {i'} {j'} {_} {Σ (P x)}
        {Σ (λ x₁ → P x₁ y')} (cf x) (cg y')
        (λ ppxy ppx'y' →
           Trunc i+j
           (Σ
            (λ (px'y : P (fst ppx'y') (fst ppxy)) →
               Square {W} (glue (snd ppxy)) (glue pxy') (! (glue px'y))
               (! (glue (snd ppx'y')))))
           , Trunc-level)
        (Inr id) {_ , pxy'} {_ , pxy'} 
        (λ ppx''y' → [ snd ppx''y' , connection2 ])
        (λ ppxy'' → [ snd ppxy'' , inverses-square (glue (snd ppxy'')) (glue pxy') ]) 
        (ap (λ z → [ pxy' , z ]) (! (inverses-connection-coh (glue pxy'))))
        (_ , pxy) (_ , px'y')
  
    composePβ1 : ∀ {x x' y' } → (pxy' : P x y') (px'y' : P x' y') → composeP pxy' pxy' px'y' == [ px'y' , connection2 ]
    composePβ1 pxy' px'y' = ap≃ (ConnectedProduct.wedge-elim-βa _ _ _ _ _ _ _)
  
    composePβ2 : ∀ {x y y' } → (pxy : P x y) (pxy' : P x y') → composeP pxy pxy' pxy' == [ pxy , (inverses-square _ _) ]
    composePβ2 pxy' px'y' = ap≃ (ConnectedProduct.wedge-elim-βb _ _ _ _ _ _ _)
  
    composePcoh : ∀ {x y' } → (pxy' : P x y') → Square (composePβ1 pxy' pxy') id (ap (λ z → [ pxy' , z ]) (! (inverses-connection-coh (glue pxy')))) (composePβ2 pxy' pxy')
    composePcoh pxy' = disc-to-square (! (ConnectedProduct.wedge-elim-coh _ _ _ _ _ _ _))

  {-
    -- the other diagonal
    composeP2 : ∀ {x x' y y'} → (pxy : P x y) (px'y : P x' y) (px'y' : P x' y') 
             → Trunc (i+j) (Σ \ (pxy' : P x y') → Square {W} (glue pxy) (glue pxy') (! (glue px'y)) (! (glue px'y')))
    composeP2 {x}{x'}{y}{y'} pxy px'y px'y' = 
      Trunc-func (λ ps → fst ps , whisker-square (!-invol (glue pxy)) (!-invol (glue (fst ps))) id id (!-square-h (!-square-v (snd ps)))) (composeP px'y' px'y pxy)
    ConnectedProduct.wedge-elim {i'} {j'} {_} {Σ (P x')}
                                              {Σ (λ x₁ → P x₁ y)} (cf x') (cg y)
                                              (λ ppx'y' ppxy →
                                                 Trunc i+j
                                                 (Σ (λ (pxy' : P (fst ppxy) (fst ppx'y')) → Square (glue (snd ppxy)) (glue pxy') (! (glue px'y)) (! (glue (snd ppx'y')))))
                                                 , Trunc-level)
                                              (Inr id) {_ , px'y} {_ , px'y}
                                              (λ ppx2y → [ snd ppx2y , connection2 ])
                                              (λ ppx'y2 → [ snd ppx'y2 , inverses-square _ _ ])
                                              (ap (λ z → [ px'y , z ]) (! (inverses-connection-coh (glue px'y))))
                                              (_ , px'y') (_ , pxy)
  -}

  gluel' : {x0 : X} {y0 : Y} (p0 : P x0 y0) {x : X} → P x y0 → Path {W} (inl x0) (inl x)
  gluel' p0 pxy0 = ! (glue pxy0) ∘ glue p0

  module Codes-glue where

    Codes-glue-1' : {x0 : X} {y0 : Y} (p0 : P x0 y0) {x : X} {y   : Y} (pxy : P x y)
                    {αx  : Path (inl x0) (inl x)} {αy  : Path (inl x0) (inr y)} (s : Square αx id (glue pxy) αy)
                   → (HFiber (gluel' p0) αx) → Trunc i+j (HFiber (glue) αy)
    Codes-glue-1' p0 pxy s (pxy0 , q) = Trunc-rec Trunc-level 
                                                  (λ c → [ fst c , square-to-disc s ∘ ap (λ z → glue pxy ∘ z) q ∘ square-to-disc-rearrange (snd c) ]) 
                                                  (composeP pxy pxy0 p0 )

    Codes-glue-1 :  {x0 : X} {y0 : Y} (p0 : P x0 y0) {x   : X} {y   : Y} (pxy : P x y)
                   {αx  : Path (inl x0) (inl x)} {αy  : Path (inl x0) (inr y)} (s : Square αx id (glue pxy) αy)
                   → Trunc i+j (HFiber (gluel' p0 {x}) αx) → Trunc i+j (HFiber glue αy)
    Codes-glue-1 p0 pxy s = Trunc-rec Trunc-level (Codes-glue-1' p0 pxy s)

    Codes-glue-2' :  {x0 : X} {y0 : Y} (p0 : P x0 y0) {x   : X} {y   : Y} (pxy : P x y)
                     {αx  : Path (inl x0) (inl x)} {αy  : Path (inl x0) (inr y)}
                    (s : Square αx id (glue pxy) αy)
                   → (HFiber glue αy) → Trunc i+j (HFiber (gluel' p0 {x}) αx)
    Codes-glue-2' p0 pxy s (pxy0 , q) = Trunc-rec Trunc-level 
                                        (λ c → [ fst c , square-to-disc (!-square-h s) ∘ ap (λ z → ! (glue pxy) ∘ z) q ∘ square-to-disc (snd c) ]) 
                                        (composeP p0 pxy0 pxy )

    Codes-glue-2 :  {x0 : X} {y0 : Y} (p0 : P x0 y0) {x   : X} {y   : Y} (pxy : P x y)
                    {αx  : Path (inl x0) (inl x)} {αy  : Path (inl x0) (inr y)} (s : Square αx id (glue pxy) αy)
                   → Trunc i+j (HFiber glue αy) → Trunc i+j (HFiber (gluel' p0 {x}) αx)
    Codes-glue-2 p0 pxy s = Trunc-rec Trunc-level (Codes-glue-2' p0 pxy s)

{-
    -- peel off truncation, replace square with disc
    Codes-glue-1'2 :  {x0 : X} {y0 : Y} (p0 : P x0 y0) {x   : X} {y   : Y} (pxy : P x y)
                      {αx  : Path (inl x0) (inl x)} {αy  : Path (inl x0) (inr y)} (s : (glue pxy ∘ αx) == αy)
                      (hfx : HFiber (gluel' p0 {x}) αx) → (Codes-glue-2 p0 pxy (disc-to-square s) (Codes-glue-1' p0 pxy (disc-to-square s) hfx)) == [ hfx ]
    Codes-glue-1'2 {x0}{y0} p0 {x}{y} pxy id (pxy0 , id) = ConnectedProduct.wedge-elim (cf x) (cg y0)
                                                             (λ ppxy pp0 →
                                                                Codes-glue-2 (snd pp0) (snd ppxy) (disc-to-square id)
                                                                (Codes-glue-1' (snd pp0) (snd ppxy) (disc-to-square id)
                                                                 (pxy0 , id))
                                                                == [ pxy0 , id ]
                                                                , path-preserves-level Trunc-level)
                                                             (Inr id) {_ , pxy0} {_ , pxy0} {!!} {!!} {!!} (_ , pxy) (_ , p0) where
                   case1 : (b : Σ (λ x₁ → P x₁ y0)) →
                           Codes-glue-2 (snd b) pxy0 (disc-to-square id) (Codes-glue-1' (snd b) pxy0 (disc-to-square {!!}) (pxy0 , id))
                           == [ pxy0 , id ]
                   case1 (x' , px'y0) = Codes-glue-2 px'y0 pxy0 (disc-to-square id) (Codes-glue-1' px'y0 pxy0 (disc-to-square id) (pxy0 , id))
                                          ≃〈 id 〉 
                                        Codes-glue-2 px'y0 pxy0 (disc-to-square id) (Trunc-rec Trunc-level (λ c → [ fst c , _ ])
                                                                (composeP pxy0 pxy0 px'y0 )) ≃〈 ap (Codes-glue-2 px'y0 pxy0 (disc-to-square id) o Trunc-rec Trunc-level (λ c → [ fst c , _ ])) {!!} 〉 
                                        Codes-glue-2 px'y0 pxy0 (disc-to-square id) [ px'y0 , {!!} ] ≃〈 {!!} 〉 
                                        ([ pxy0 , id ] ∎)
-}
    Codes-glue-eqv : {x0 : X} {y0 : Y} (p0 : P x0 y0) {x : X} {y   : Y} (pxy : P x y)
                     {αx  : Path (inl x0) (inl x)} {αy  : Path (inl x0) (inr y)} (s : Square αx id (glue pxy) αy)
                     → Equiv (Trunc i+j (HFiber (gluel' p0 {x}) αx)) (Trunc i+j (HFiber glue αy))
    Codes-glue-eqv p0 pxy s = improve (hequiv (Codes-glue-1 p0 pxy s) {!!} {!!} {!!})



  module Codes (x0 : X) (y0 : Y) (p0 : P x0 y0) where
    open Codes-glue 

    gluel : {x : X} → P x y0 → inl x0 == inl x
    gluel = gluel' p0

    CodesFor : (w : W) (p : Path{W} (inl x0) w) → Type 
    CodesFor = Pushout-elim _ (λ x p → Trunc i+j (HFiber gluel p)) 
                              (λ y p → Trunc i+j (HFiber glue p))
                              (λ x y pxy → coe (! PathOverΠ-NDrange)
                                (λ αx αy s → ua (Codes-glue-eqv p0 pxy (PathOverPathFrom.out-PathOver-= s))))

    CodesFor' : (Σ \ (w : W) → Path{W} (inl x0) w) → Type 
    CodesFor' = uncurryd CodesFor

    transport-CodesFor'-glue : ∀ {x y} (pxy : P x y) {αx  : Path{W} (inl x0) (inl x)} {αy  : Path (inl x0) (inr y)} (s : PathOver (Path (inl x0)) (glue pxy) αx αy)
                               → transport CodesFor' (pair= (glue pxy) s) == Codes-glue-1 p0 pxy (PathOverPathFrom.out-PathOver-= s) 
    transport-CodesFor'-glue pxy s = transport CodesFor' (pair= (glue pxy) s) ≃〈 transport-ap-assoc CodesFor' (pair= (glue pxy) s) 〉 
                                     coe (ap CodesFor' (pair= (glue pxy) s)) ≃〈 ap coe (ap-uncurryd-NDrange CodesFor _ _) 〉 
                                     coe (coe PathOverΠ-NDrange (apdo CodesFor (glue pxy)) _ _ s) ≃〈 ap (λ Z → coe (coe PathOverΠ-NDrange Z _ _ s)) (Pushout-elim/βglue _ _ _ (λ x y pxy₁ → coe (! PathOverΠ-NDrange) (λ αx αy s₁ → ua (Codes-glue-eqv p0 pxy₁ (PathOverPathFrom.out-PathOver-= s₁)))) _ _ _) 〉 
                                     coe (coe PathOverΠ-NDrange (coe (! PathOverΠ-NDrange)
                                           (λ αx αy s → ua (Codes-glue-eqv p0 pxy (PathOverPathFrom.out-PathOver-= s)))) _ _ s) ≃〈 ap (λ z → coe (z _ _ s)) (IsEquiv.β (snd (coe-equiv PathOverΠ-NDrange)) _) 〉 
                                     coe (ua (Codes-glue-eqv p0 pxy (PathOverPathFrom.out-PathOver-= s))) ≃〈 type≃β (Codes-glue-eqv p0 pxy (PathOverPathFrom.out-PathOver-= s)) 〉 
                                     Codes-glue-1 p0 pxy (PathOverPathFrom.out-PathOver-= s) ∎

    forid : CodesFor (inl x0) id
    forid = [ p0 , !-inv-l (glue p0) ]

    redr : {y : Y} (px0y : P x0 y) → transport CodesFor' (pair= (glue px0y) connOver) forid == [ px0y , id ]
    redr px0y = transport CodesFor' (pair= (glue px0y) connOver) forid ≃〈 ap≃ (transport-CodesFor'-glue px0y connOver) 〉 
                Codes-glue-1 p0 px0y (PathOverPathFrom.out-PathOver-= connOver) [ p0 , !-inv-l (glue p0) ]  ≃〈 id 〉 
                Trunc-rec Trunc-level (λ c → [ fst c , square-to-disc (PathOverPathFrom.out-PathOver-= connOver) ∘
                                                         ap (_∘_ (glue px0y)) (!-inv-l (glue p0)) ∘
                                                         square-to-disc-rearrange (snd c) ]) (composeP px0y p0 p0 ) ≃〈 ap (Trunc-rec Trunc-level (λ c → [ fst c , _ ])) (composePβ2 _ _) 〉 
                [ px0y , square-to-disc (PathOverPathFrom.out-PathOver-= connOver) ∘ ap (_∘_ (glue px0y)) (!-inv-l (glue p0)) ∘ square-to-disc-rearrange (inverses-square (glue px0y) (glue p0)) ] ≃〈 ap (λ z → [ px0y , z ]) (coh (glue p0) (glue px0y)) 〉 
                [ px0y , id ] ∎ where
         coh : ∀ {A : Type} {a0 a1 a1' : A} (α : a0 == a1) (α' : a0 == a1')
               → square-to-disc (PathOverPathFrom.out-PathOver-= connOver) ∘ 
                  ap (_∘_ α') (!-inv-l α) ∘ 
                  square-to-disc-rearrange (inverses-square α' α) == id
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

