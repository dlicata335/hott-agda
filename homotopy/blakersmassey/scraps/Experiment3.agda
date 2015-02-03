{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude hiding (Z)
open PushoutFib
open ConnectedMap
open Truncation
open import lib.cubical.Cubical

module homotopy.blakersmassey.Experiment3 (X Y : Type) (P : X → Y → Type)
                                          (i' j' : _)
                                          (cf : (x : X) → Connected (S i') (Σ \ y → P x y))
                                          (cg : (y : Y) → Connected (S j') (Σ \ x → P x y)) 
                                          (-1<=i' : -1 <=tl i') 
                                          (-1<=j' : -1 <=tl j') where

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

  contract-zig-left : ∀ {x0 y0} (p0 : P x0 y0) 
                       (C : ∀ {y} → (px0y : P x0 y) → NTypes i') 
                    →  fst (C p0) → {y : Y} (p : P x0 y) → fst (C p)
  contract-zig-left {x0}{y0} p0 C c0 p = ConnectedFib.everywhere i' {Σ (λ y → P x0 y)} {_ , p0} (cf x0) (λ ppxy0 → C (snd ppxy0)) c0 (_ , p)

  contract-zig-right : ∀ {x0 y0} (p0 : P x0 y0) 
                       (C : ∀ {x} → (pxy0 : P x y0) → NTypes j') 
                    →  fst (C p0) → {x : X} (p : P x y0) → fst (C p)
  contract-zig-right {x0}{y0} p0 C c0 p = ConnectedFib.everywhere j' {Σ (λ x → P x y0)} {_ , p0} (cg y0) (λ ppxy0 → C (snd ppxy0)) c0 (_ , p)

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
  
    composePβ12 : ∀ {x x' y' } → (pxy' : P x y') (px'y' : P x' y') → composeP pxy' pxy' px'y' == [ px'y' , connection2 ]
    composePβ12 pxy' px'y' = ap≃ (ConnectedProduct.wedge-elim-βa _ _ _ _ _ _ _)
  
    composePβ23 : ∀ {x y y' } → (pxy : P x y) (pxy' : P x y') → composeP pxy pxy' pxy' == [ pxy , (inverses-square _ _) ]
    composePβ23 pxy' px'y' = ap≃ (ConnectedProduct.wedge-elim-βb _ _ _ _ _ _ _)
  
    composePcoh : ∀ {x y' } → (pxy' : P x y') → Square (composePβ12 pxy' pxy') id (ap (λ z → [ pxy' , z ]) (! (inverses-connection-coh (glue pxy')))) (composePβ23 pxy' pxy')
    composePcoh pxy' = disc-to-square (! (ConnectedProduct.wedge-elim-coh _ _ _ _ _ _ _))
  
  gluel' : {x0 : X} {y0 : Y} (p0 : P x0 y0) {x : X} → P x y0 → Path {W} (inl x0) (inl x)
  gluel' p0 pxy0 = ! (glue pxy0) ∘ glue p0

  module Codes-glue where

    map' : {x0 : X} {y0 : Y} (p0 : P x0 y0) {x : X} {y   : Y} (pxy : P x y)
                    {αx  : Path (inl x0) (inl x)} {αy  : Path (inl x0) (inr y)} (s : Square αx id (glue pxy) αy)
                   → (HFiber (gluel' p0) αx) → Trunc i+j (HFiber (glue) αy)
    map' p0 pxy s (pxy0 , q) = 
      Trunc-rec Trunc-level 
                (λ c → [ fst c , square-to-disc s ∘ ap (λ z → glue pxy ∘ z) q ∘ square-to-disc-rearrange (snd c) ]) 
                (composeP pxy pxy0 p0)

    map : {x0 : X} {y0 : Y} (p0 : P x0 y0) {x   : X} {y   : Y} (pxy : P x y)
                   {αx  : Path (inl x0) (inl x)} {αy  : Path (inl x0) (inr y)} (s : Square αx id (glue pxy) αy)
                   → Trunc i+j (HFiber (gluel' p0 {x}) αx) → Trunc i+j (HFiber glue αy)
    map p0 pxy s = Trunc-rec Trunc-level (map' p0 pxy s)

    is-equiv-diag : ∀ {x y} (pxy : P x y) (αx : Path (inl x) (inl x))
                               → IsEquiv (map pxy pxy {αx} {glue pxy ∘ αx} (disc-to-square id))
    is-equiv-diag pxy αx = {!!} where
      map-diag : {! map pxy pxy {αx} {glue pxy ∘ αx} (disc-to-square id) !} == 
                 Trunc-rec Trunc-level {!\ {( → !}
      map-diag = {!!}



    is-equiv-zig-right : ∀ {x y} → (pxy : P x y) {x' : _} (px'y : P x' y) (αx : Path (inl x) (inl x'))
                                  → IsEquiv (map pxy px'y {αx} {glue px'y ∘ αx} (disc-to-square id))
    is-equiv-zig-right {x}{y} pxy = 
      contract-zig-right pxy (\ {x' : _} (px'y : P x' y) → 
                              ((αx : Path (inl x) (inl x')) → IsEquiv (map pxy px'y {αx} {glue px'y ∘ αx} (disc-to-square id))) , Πlevel (λ _ → raise-level -1<=j' (IsEquiv-HProp _)))
                             (is-equiv-diag pxy)

    is-equiv-zig-left : ∀ {x y} → (pxy : P x y) {y' : _} (pxy' : P x y') (αx : Path (inl x) (inl x))
                                  → IsEquiv (map pxy pxy' {αx} {glue pxy' ∘ αx} (disc-to-square id))
    is-equiv-zig-left {x}{y} pxy = 
      contract-zig-left pxy (\ {y' : _} (pxy' : P x y') → 
                              ((αx : Path (inl x) (inl x)) → IsEquiv (map pxy pxy' {αx} {glue pxy' ∘ αx} (disc-to-square id))) , Πlevel (λ _ → raise-level -1<=i' (IsEquiv-HProp _)))
                             (is-equiv-diag pxy)

    -- path induction on the disc
    -- grab a point in the range and peel the truncation off it, to link pxy to p0, 
    -- then use wedge-elim on the zig
    is-equiv' : {x0 : X} {y0 : Y} (p0 : P x0 y0) {x   : X} {y   : Y} (pxy : P x y)
                {αx  : Path (inl x0) (inl x)} {αy  : Path (inl x0) (inr y)} (d : glue pxy ∘ αx == αy)
              → IsEquiv (map p0 pxy {αx = αx}{αy = αy} (disc-to-square d))
    is-equiv' {x0}{y0} p0 {x}{y} pxy {αx} id = 
      grab-point-in-range _
           (Trunc-rec (raise-level { -1 }{i+j} (-1<=plus2{i'}{j'} (Inl -1<=i')) (IsEquiv-HProp _))
             (λ hf → ConnectedProduct.wedge-elim {i'} {j'} {_} {Σ (P x0)} {Σ (λ x₁ → P x₁ y)} (cf x0) (cg y)
                          (λ pp0 ppxy → ((αx  : Path (inl x0) (inl (fst ppxy))) → 
                                         IsEquiv (map{x0}{fst pp0} (snd pp0) {fst ppxy} {y} (snd ppxy) {αx = αx} {αy = glue (snd ppxy) ∘ αx} (disc-to-square id))) ,
                                         raise-level (-1<=plus2 (Inl -1<=i')) (Πlevel (λ _ → IsEquiv-HProp _)))
                          (Inr id) 
                          {_ , fst hf} {_ , fst hf}
                          (λ ppx'y αx → is-equiv-zig-right (fst hf) (snd ppx'y) αx)
                          (λ ppxy' αx → is-equiv-zig-left (snd ppxy') (fst hf) αx)
                          (HProp-unique (Πlevel (λ _ → IsEquiv-HProp _)) _ _) 
                          (y0 , p0) (x , pxy) αx)) 

    -- replace the square with a disc
    is-equiv : {x0 : X} {y0 : Y} (p0 : P x0 y0) {x   : X} {y   : Y} (pxy : P x y)
                            {αx  : Path (inl x0) (inl x)} {αy  : Path (inl x0) (inr y)} (s : Square αx id (glue pxy) αy)
                            → IsEquiv (map p0 pxy s)
    is-equiv p0 pxy s = transport (λ Z → IsEquiv (map p0 pxy Z)) (IsEquiv.α (snd square-disc-eqv) _)
                                  (is-equiv' p0 pxy (square-to-disc s))

    eqv : {x0 : X} {y0 : Y} (p0 : P x0 y0) {x : X} {y   : Y} (pxy : P x y)
                     {αx  : Path (inl x0) (inl x)} {αy  : Path (inl x0) (inr y)} (s : Square αx id (glue pxy) αy)
                     → Equiv (Trunc i+j (HFiber (gluel' p0 {x}) αx)) (Trunc i+j (HFiber glue αy))
    eqv p0 pxy s = (map p0 pxy s , is-equiv p0 pxy s)


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
                                                         square-to-disc-rearrange (snd c) ]) (composeP px0y p0 p0 ) ≃〈 ap (Trunc-rec Trunc-level (λ c → [ fst c , _ ])) (composePβ23 _ _) 〉 
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

