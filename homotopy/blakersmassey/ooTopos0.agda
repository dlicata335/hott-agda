-- PERF: was getting too slow to keep retypechecking this.  move back eventually

{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude hiding (Z)
open FatPushoutFib
open Truncation
open import lib.cubical.Cubical

module homotopy.blakersmassey.ooTopos0 (X Y : Type) (P : X → Y → Type)
                                       (i' j' : TLevel)
                                       (cf : (x : X) → Connected (S i') (Σ \ y → P x y))
                                       (cg : (y : Y) → Connected (S j') (Σ \ x → P x y)) where 

  i : TLevel
  i = S i'

  j : TLevel
  j = S j'

  i+j = plus2 i' j'

  W = FatPushoutFib.Pushout P
  Z = Σ \xy → P (fst xy) (snd xy)

  glue : {x : X} {y : Y} (p : P x y) → Path {W} (inl x) (inr y)
  glue p = gluer p ∘ ! (gluel p)

  Z×WZ = Σ \ (z1 : Z) → Σ \ (z2 : Z) → Path {W} (inm (snd z1)) (inm (snd z2))
  〈Z×Z〉×〈YX〉Z = Σ \ (z1 : Z) → Σ \ (z2 : Z) → P (fst (fst z2)) (snd (fst z1))
  〈Z×Z〉×〈XY〉Z = Σ \ (z1 : Z) → Σ \ (z2 : Z) → P (fst (fst z1)) (snd (fst z2))

  module Wedge = Pushout

  module _ {x0 : X} {y0 : Y} (p0 : P x0 y0) where
    gluel0 : {x : X} → P x y0 → Path {W} (inm p0) (inl x)
    gluel0 pxy0 = ! (glue pxy0) ∘ gluer p0

    gluer0 : {y : Y} → P x0 y → Path {W} (inm p0) (inr y)
    gluer0 pxy0 = glue pxy0 ∘ gluel p0

    gluemr : ∀ {x y} (pxy : P x y) → P x0 y → Path {W} (inm p0) (inm pxy)
    gluemr pxy px0y = ! (gluer pxy) ∘ glue px0y ∘ gluel p0

    glueml : ∀ {x y} (pxy : P x y) → P x y0 → Path {W} (inm p0) (inm pxy)
    glueml pxy pxy0 = ! (gluel pxy) ∘ ! (glue pxy0) ∘ gluer p0

    -×WZ = Σ \ (p : Z) → Path{W} (inm p0) (inm (snd p))
    -×XZ = (Σ \ y → P x0 y)
    -×YZ = (Σ \ x → P x y0)
    Z×X-∨-×YZ = Pushout.Wedge { -×XZ } { -×YZ } (_ , p0) (_ , p0)

    gluem : Z×X-∨-×YZ → -×WZ
    gluem = Wedge.Pushout-rec (λ ppx0y → (_ , snd ppx0y) , ! (gluel (snd ppx0y)) ∘ gluel p0)
                              (λ ppxy0 → (_ , snd ppxy0) , ! (gluer (snd ppxy0)) ∘ gluer p0)
                              (λ _ → ap (λ h → ((x0 , y0) , p0) , h) (square-to-disc (inverses-square (gluel p0) (gluer p0))))

    wtp : Z×X-∨-×YZ → -×XZ × -×YZ 
    wtp = Pushout.wedge-to-prod

  module CodesGlueMaps where

    reassoc-l : 〈Z×Z〉×〈YX〉Z → Σ \(z : Z) → (-×XZ (snd z)) × (-×YZ (snd z))
    reassoc-l (((x , y) , pxy) , ((x' , y') , px'y') , px'y) = ((x' , y) , px'y) , ((y' , px'y') , (x , pxy))

    reassoc-l' : (Σ \(z : Z) → (-×XZ (snd z)) × (-×YZ (snd z))) → 〈Z×Z〉×〈YX〉Z
    reassoc-l' (((x' , y) , px'y) , ((y' , px'y') , (x , pxy))) = (_ , pxy) , (_ , px'y') , px'y

    reassoc-l-eqv : Equiv 〈Z×Z〉×〈YX〉Z (Σ \(z : Z) → (-×XZ (snd z)) × (-×YZ (snd z)))
    reassoc-l-eqv = improve (hequiv reassoc-l reassoc-l' (λ _ → id) (λ _ → id))

    reassoc-r : 〈Z×Z〉×〈XY〉Z → Σ \(z : Z) → (-×XZ (snd z)) × (-×YZ (snd z))
    reassoc-r (((x , y) , pxy) , ((x' , y') , px'y') , pxy') = ((x , y') , pxy') , ((y , pxy) , (x' , px'y'))

    reassoc-r' : (Σ \(z : Z) → (-×XZ (snd z)) × (-×YZ (snd z))) → 〈Z×Z〉×〈XY〉Z
    reassoc-r' (((x' , y) , px'y) , ((y' , px'y') , (x , pxy))) = (_ , px'y') , (_ , pxy) , px'y

    reassoc-r-eqv : Equiv 〈Z×Z〉×〈XY〉Z (Σ \(z : Z) → (-×XZ (snd z)) × (-×YZ (snd z)))
    reassoc-r-eqv = improve (hequiv reassoc-r reassoc-r' (λ _ → id) (λ _ → id))

    -- ENH: figure out where this is hiding in the ooTopos version

    switchr : (Σ \ (z : Z) → Z×X-∨-×YZ (snd z)) → (Σ \ (z : Z) → Z×X-∨-×YZ (snd z))
    switchr (z , w) = Wedge.Pushout-rec (λ xp → z , Wedge.inl xp)
                                        (λ yp → (_ , snd yp) , Wedge.inr (_ , snd z))
                                        (λ _ → ap (λ Z₁ → z , Z₁) (Wedge.glue _)) 
                                        w

    switchr-twice : ∀ z w → switchr (switchr (z , w)) == (z , w)
    switchr-twice z = Wedge.Pushout-elim _ (λ _ → id) (λ _ → id) 
                      (λ _ → PathOver=.in-PathOver-= (vertical-degen-square 
                      (Wedge.βglue/rec _ _ _ _ ∘
                       ! (ap-o switchr (λ Z₁ → z , Z₁) (Wedge.glue <>)) ∘ 
                       ap (ap switchr) (Wedge.βglue/rec _ _ _ _) ∘ 
                       ap-o switchr (λ v → switchr (z , v)) (Wedge.glue <>))))

    switchr-equiv : Equiv (Σ \ (z : Z) → Z×X-∨-×YZ (snd z)) (Σ \ (z : Z) → Z×X-∨-×YZ (snd z))
    switchr-equiv = improve (hequiv switchr switchr (\ p → switchr-twice (fst p) (snd p)) (\ p → switchr-twice (fst p) (snd p)))

    switchl : (Σ \ (z : Z) → Z×X-∨-×YZ (snd z)) → (Σ \ (z : Z) → Z×X-∨-×YZ (snd z))
    switchl (z , w) = Wedge.Pushout-rec (λ xp → (_ , snd xp) , Wedge.inl (_ , snd z))
                                        (λ yp → z , Wedge.inr yp)
                                        (λ _ → ap (λ Z₁ → ((fst (fst z) , snd (fst z)) , snd z) , Z₁) (Wedge.glue _)) 
                                        w

    switchl-twice : ∀ z w → switchl (switchl (z , w)) == (z , w)
    switchl-twice z = Wedge.Pushout-elim _ (λ _ → id) (λ _ → id) (λ _ → PathOver=.in-PathOver-=
                                                                          (vertical-degen-square
                                                                           (Wedge.βglue/rec _ _ _ _ ∘
                                                                            ! (ap-o switchl (λ Z₁ → z , Z₁) (Wedge.glue <>)) ∘
                                                                            ap (ap switchl) (Wedge.βglue/rec _ _ _ _) ∘
                                                                            ap-o switchl (λ v → switchl (z , v)) (Wedge.glue <>))))

    switchl-equiv : Equiv (Σ \ (z : Z) → Z×X-∨-×YZ (snd z)) (Σ \ (z : Z) → Z×X-∨-×YZ (snd z))
    switchl-equiv = improve (hequiv switchl switchl (\ p → switchl-twice (fst p) (snd p)) (\ p → switchl-twice (fst p) (snd p)))

    gluem-total : Σ (λ z → Z×X-∨-×YZ (snd z)) → Z×WZ
    gluem-total = fiberwise-to-total (\ (z : Z) → gluem (snd z))

    glueml-total : 〈Z×Z〉×〈YX〉Z → Z×WZ
    glueml-total = (fiberwise-to-total (\ (ppp0 : Z) → (fiberwise-to-total (\ (ppxy : Z) → glueml (snd ppp0) (snd ppxy)))))

    m-to-ml : (Σ \ (z : Z) → Z×X-∨-×YZ (snd z)) → 〈Z×Z〉×〈YX〉Z
    m-to-ml = reassoc-l' o (fiberwise-to-total (λ z1 → wtp (snd z1)) o switchr)

        
    red-gluem-total-glue : ∀ {z} → (ap (λ z₁ → gluem-total (z , z₁)) (Wedge.glue <>)) == ap (λ h → z , z , h) (square-to-disc (inverses-square (gluel (snd z)) (gluer (snd z))))
    red-gluem-total-glue {z} = ! (ap-o (λ h → z , h) (λ h → z , h) (square-to-disc (inverses-square (gluel (snd z)) (gluer (snd z))))) ∘ 
                               ap (ap (λ h → z , h)) (Wedge.βglue/rec _ _ (λ _ → ap (λ h → z , h) (square-to-disc (inverses-square (gluel (snd z)) (gluer (snd z))))) <>) ∘ 
                               ap-o (λ h → z , h) (gluem (snd z)) (Wedge.glue <>)

    m-to-ml-triangle-coh1 : ∀ {A} {a0 a1 a2 a3 : A} (lyp : a0 == a1) (lz : a2 == a1) (rz : a2 == a3) → (! lyp ∘ ! (rz ∘ ! (lz)) ∘ rz) == (! lyp ∘ lz)
    m-to-ml-triangle-coh1 id id id = id

    m-to-ml-triangle : ∀ z (w : Z×X-∨-×YZ (snd z)) → (glueml-total o m-to-ml) (z , w) == gluem-total (z , w)
    m-to-ml-triangle z = Wedge.Pushout-elim (λ w → (glueml-total o m-to-ml) (z , w) == gluem-total (z , w))
                                            (λ yp → ap (λ Q → z , ((fst (fst z) , fst yp) , snd yp) , Q) (m-to-ml-triangle-coh1 (gluel (snd yp)) (gluel (snd z)) (gluer (snd z))))
                                            (λ xp → ap (λ Q → z , ((fst xp , snd (fst z)) , snd xp) , Q) (coh2 (gluel (snd xp)) (gluer (snd xp)) (gluer (snd z))))
                                            (λ _ → PathOver=.in-PathOver-= (whisker-square id (! red) (! red-gluem-total-glue) id (ap-square (λ h → z , z , h) (coh12 (gluel (snd z)) (gluer (snd z)))))) where

      coh2 : ∀ {A} {a0 a1 a2 a3 : A} (lxp : a0 == a1) (rxp : a0 == a2) (rz : a3 == a2) → (! lxp ∘ ! (rxp ∘ ! (lxp)) ∘ rz) == (! rxp ∘ rz)
      coh2 id id id = id

      coh12 : ∀ {A} {a0 a1 a2 : A} (lz : a0 == a1) (rz : a0 == a2) → Square (m-to-ml-triangle-coh1 lz lz rz) id (square-to-disc (inverses-square lz rz)) (coh2 lz rz rz)
      coh12 id id = id

      red : (ap (λ z₁ → (glueml-total o m-to-ml) (z , z₁)) (Wedge.glue <>)) == ap (\ h → z , z , h) id
      red = ap (ap glueml-total) red1' ∘ ap-o glueml-total (λ h → m-to-ml (z , h)) (Wedge.glue <>) where
        red1'' : ap (λ h → (fiberwise-to-total (λ z1 → wtp (snd z1)) o switchr) (z , h)) (Wedge.glue <>)  == id
        red1'' =  ap (ap (λ x → z , x)) (Wedge.βglue/rec _ _ _ _) ∘ ap-o (λ x → z , x) (wtp (snd z)) (Wedge.glue <>) ∘ 
                  ! (ap-o (fiberwise-to-total (λ z1 → wtp (snd z1))) (λ h → z , h) (Wedge.glue <>)) ∘
                  ap (ap (fiberwise-to-total (λ z1 → wtp (snd z1))))(Wedge.βglue/rec _ _ _ _) ∘ 
                  ap-o (fiberwise-to-total (λ z1 → wtp (snd z1))) (λ h → switchr (z , h)) (Wedge.glue <>)

        red1' : ap (\ h → m-to-ml (z , h)) (Wedge.glue <>) == id
        red1' = ap (ap reassoc-l') red1'' ∘ ap-o reassoc-l' (λ h → (fiberwise-to-total (λ z1 → wtp (snd z1)) o switchr) (z , h)) (Wedge.glue <>)

    gluemr-total : 〈Z×Z〉×〈XY〉Z → Z×WZ
    gluemr-total = (fiberwise-to-total (\ (ppp0 : Z) → (fiberwise-to-total (\ (ppxy : Z) → gluemr (snd ppp0) (snd ppxy)))))

    m-to-mr : (Σ \ (z : Z) → Z×X-∨-×YZ (snd z)) → 〈Z×Z〉×〈XY〉Z
    m-to-mr = reassoc-r' o fiberwise-to-total (λ z1 → wtp (snd z1)) o switchl

    m-to-mr-triangle : ∀ z (w : Z×X-∨-×YZ (snd z)) → (gluemr-total o m-to-mr) (z , w) == gluem-total (z , w)
    m-to-mr-triangle z = Wedge.Pushout-elim (λ w → (gluemr-total o m-to-mr) (z , w) == gluem-total (z , w))
                                            (λ yp → ap (λ Q → z , ((fst (fst z) , fst yp) , snd yp) , Q) (coh1 (gluer (snd yp)) (gluel (snd yp)) (gluel (snd z))))
                                            (λ xp → ap (λ Q → z , ((fst xp , snd (fst z)) , snd xp) , Q) (coh2 (gluer (snd xp)) (gluer (snd z)) (gluel (snd z))))
                                            (λ _ → PathOver=.in-PathOver-= (whisker-square id (! red)
                                                                                           (! red-gluem-total-glue) id
                                                                                           (ap-square (λ h → z , z , h) (coh12 (gluel (snd z)) (gluer (snd z)))))) where
      coh1 : ∀ {A} {a0 a1 a2 a3 : A} (ryp : a0 == a1) (lyp : a0 == a2) (lz : a3 == a2) → (! ryp ∘ (ryp ∘ ! (lyp)) ∘ lz) == (! lyp ∘ lz)
      coh1 id id id = id

      coh2 : ∀ {A} {a0 a1 a2 a3 : A} (rxp : a0 == a1) (rz : a2 == a1) (lz : a2 == a3) → (! rxp ∘ (rz ∘ ! (lz)) ∘ lz) == (! rxp ∘ rz)
      coh2 id id id = id

      coh12 : ∀ {A} {a0 a1 a2 : A} (lz : a0 == a1) (rz : a0 == a2) → Square (coh1 rz lz lz) id (square-to-disc (inverses-square lz rz)) (coh2 rz rz lz)
      coh12 id id = id

      red : (ap (λ z₁ → (gluemr-total o m-to-mr) (z , z₁)) (Wedge.glue <>)) == ap (\ h → z , z , h) id
      red = ap (ap gluemr-total) red1' ∘ ap-o gluemr-total (λ h → m-to-mr (z , h)) (Wedge.glue <>) where
        red1'' : ap (λ h → (fiberwise-to-total (λ z1 → wtp (snd z1)) o switchl) (z , h)) (Wedge.glue <>)  == id
        red1'' =  ap (ap (λ x → z , x)) (Wedge.βglue/rec _ _ _ _) ∘ ap-o (λ x → z , x) (wtp (snd z)) (Wedge.glue <>) ∘ 
                  ! (ap-o (fiberwise-to-total (λ z1 → wtp (snd z1))) (λ h → z , h) (Wedge.glue <>)) ∘
                  ap (ap (fiberwise-to-total (λ z1 → wtp (snd z1))))(Wedge.βglue/rec _ _ _ _) ∘ 
                  ap-o (fiberwise-to-total (λ z1 → wtp (snd z1))) (λ h → switchl (z , h)) (Wedge.glue <>)

        red1' : ap (\ h → m-to-mr (z , h)) (Wedge.glue <>) == id
        red1' = ap (ap reassoc-r') red1'' ∘ ap-o reassoc-r' (λ h → (fiberwise-to-total (λ z1 → wtp (snd z1)) o switchl) (z , h)) (Wedge.glue <>)

  module Codes {x0 : X} {y0 : Y} (p0 : P x0 y0) where

    open CodesGlueMaps

    glue-l-ml : ∀ {x y} (pxy : P x y) {αm : Path (inm p0) (inm pxy)} {αl : Path (inm p0) (inl x)} (s : ((gluel pxy) ∘ αm) == αl)
              → Equiv (Trunc i+j (HFiber (gluel0 p0) αl)) (Trunc i+j (HFiber (glueml p0 pxy) αm))
    glue-l-ml pxy id = apTrunc' (HFiber-at-equiv (post∘-equiv (gluel pxy)) (gluel0 p0))

    module _ {x y} (pxy : P x y) {α : Path (inm p0) (inm pxy)} where
      glue-m-m-total : Equiv (HFiber (gluem p0) ((_ , pxy) , α)) 
                             (HFiber gluem-total ((_ , p0) , (_ , pxy) , α))
      glue-m-m-total = HFiber-fiberwise-to-total-eqv _

      glue-ml-ml-total : Equiv (HFiber (glueml p0 pxy) α) 
                       (HFiber glueml-total ((_ , p0) , (_ , pxy) , α))
      glue-ml-ml-total = (HFiber-fiberwise-to-total-eqv _) ∘equiv (HFiber-fiberwise-to-total-eqv _)

      glue-ml-m-total : Equiv (Trunc i+j (HFiber gluem-total ((_ , p0) , (_ , pxy) , α)))
                              (Trunc i+j (HFiber glueml-total ((_ , p0) , (_ , pxy) , α)))
      glue-ml-m-total = ConnectedMap.fiber-top-equiv (m-to-ml) _ _ (λ≃ (\ q → m-to-ml-triangle (fst q) (snd q))) 
        (ConnectedMap.precompose-equiv-connected switchr-equiv
          (ConnectedMap.postcompose-equiv-connected (!equiv reassoc-l-eqv) 
            (ConnectedMap.fiberwise-to-total-connected i+j (λ _ → Wedge.wedge-to-prod)
              (λ z → Wedge.WedgeToProd.connected (_ , snd z) (_ , snd z) (cf _) (cg _))))) 

      glue-ml-m : Equiv (Trunc i+j (HFiber (gluem p0) ((_ , pxy) , α))) (Trunc i+j (HFiber (glueml p0 pxy) α))
      glue-ml-m = apTrunc' (!equiv glue-ml-ml-total) ∘equiv 
                  glue-ml-m-total ∘equiv
                  apTrunc' glue-m-m-total

    glue-r-mr : ∀ {x y} (pxy : P x y) {αm : Path (inm p0) (inm pxy)} {αr : Path (inm p0) (inr y)} (s : ((gluer pxy) ∘ αm) == αr)
              → Equiv (Trunc i+j (HFiber (gluer0 p0) αr)) (Trunc i+j (HFiber (gluemr p0 pxy) αm))
    glue-r-mr pxy id = apTrunc' (HFiber-at-equiv (post∘-equiv (gluer pxy)) (gluer0 p0))

    glue-mr-m : ∀ {x y} (pxy : P x y) {αm : Path (inm p0) (inm pxy)} 
              → Equiv (Trunc i+j (HFiber (gluem p0) ((_ , pxy) , αm))) (Trunc i+j (HFiber (gluemr p0 pxy) αm))
    glue-mr-m {x}{y} pxy {α} = apTrunc' (!equiv ((HFiber-fiberwise-to-total-eqv _) ∘equiv (HFiber-fiberwise-to-total-eqv _))) ∘equiv 
                               step2 ∘equiv
                               apTrunc' (HFiber-fiberwise-to-total-eqv _) where
              
      step2 : Equiv (Trunc i+j (HFiber gluem-total ((_ , p0) , (_ , pxy) , α)))
                    (Trunc i+j (HFiber gluemr-total ((_ , p0) , (_ , pxy) , α)))
      step2 = ConnectedMap.fiber-top-equiv (m-to-mr) _ _ (λ≃ (\ q → m-to-mr-triangle (fst q) (snd q))) 
        (ConnectedMap.precompose-equiv-connected switchl-equiv
          (ConnectedMap.postcompose-equiv-connected (!equiv reassoc-r-eqv) 
            (ConnectedMap.fiberwise-to-total-connected i+j (λ _ → Wedge.wedge-to-prod)
              (λ z → Wedge.WedgeToProd.connected (_ , snd z) (_ , snd z) (cf _) (cg _))))) 


    -- descent cube corresponds to defining a fibration over Z×_{W}W by Pushout-elim into the universe;
    -- the distrbuted pushout is sort of implicit in carrying along the Path{W} (inm p0) w here--- we never make it explicitly
    -- equivalences are what you need to show that the squares are pullbacks
    CodesFor : (w : W) (p : Path{W} (inm p0) w) → Type 
    CodesFor = Pushout-elim _ (λ x α → Trunc i+j (HFiber (gluel0 p0) α)) 
                              (λ x y p α → Trunc i+j (HFiber (gluem p0) ( (_ , p) , α)))
                              (λ y α → Trunc i+j (HFiber (gluer0 p0) α))
                              (λ x y pxy → coe (! PathOverΠ-NDrange) 
                                 (λ αm αl d → ua (!equiv (glue-l-ml pxy (square-to-disc (PathOverPathFrom.out-PathOver-= d))) 
                                                          ∘equiv glue-ml-m pxy)))
                              (λ x y pxy → coe (! PathOverΠ-NDrange) 
                                 (λ αm αl d → ua (!equiv (glue-r-mr pxy (square-to-disc (PathOverPathFrom.out-PathOver-= d))) 
                                                  ∘equiv glue-mr-m pxy)))

    CodesFor' : (Σ \ (w : W) → Path{W} (inm p0) w) → Type 
    CodesFor' = uncurryd CodesFor
