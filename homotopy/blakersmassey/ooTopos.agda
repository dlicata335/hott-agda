{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude hiding (Z)
open FatPushoutFib
open Truncation
open import lib.cubical.Cubical
import homotopy.blakersmassey.ooTopos0

module homotopy.blakersmassey.ooTopos (X Y : Type) (P : X → Y → Type)
                                      (i' j' : TLevel)
                                      (cf : (x : X) → Connected (S i') (Σ \ y → P x y))
                                      (cg : (y : Y) → Connected (S j') (Σ \ x → P x y)) where 
  open homotopy.blakersmassey.ooTopos0 X Y P i' j' cf cg

  open CodesGlueMaps 

  module Section where
    open CodesGlueMaps
    open Codes 

    [〈Z×Z〉×〈XY〉Z] : ∀ {x y} (pxy : P x y) {x' y'} (px'y' : P x' y') (α : Path (inm pxy) (inm px'y')) → Type
    [〈Z×Z〉×〈XY〉Z] pxy {x'}{y'} px'y' α = Trunc i+j (HFiber (gluemr pxy px'y') α)

    gluemr-uncurry : (zs : 〈Z×Z〉×〈XY〉Z) → Path {W} (inm (snd (fst zs))) (inm (snd (fst (snd zs))))
    gluemr-uncurry (z1 , z2 , p) = gluemr (snd z1) (snd z2) p

    〈Z×Z〉×〈XY〉Z→[〈Z×Z〉×〈XY〉Z] : ∀ (zs : 〈Z×Z〉×〈XY〉Z) → [〈Z×Z〉×〈XY〉Z] (snd (fst zs)) (snd (fst (snd zs))) (gluemr-uncurry zs)
    〈Z×Z〉×〈XY〉Z→[〈Z×Z〉×〈XY〉Z] (_ , _ , p) = [ p , id ] 
    
    fix-path-equiv : ∀ {x0 y0} (p0 : P x0 y0) → Equiv (CodesFor p0 (inm p0) id) (CodesFor p0 (inm p0) _)
    fix-path-equiv p0 = apTrunc' (HFiber-result-equiv (ap (λ x → (_ , p0) , x) (! (m-to-mr-triangle-coh1 (gluer p0) (gluel p0) (gluel p0)) ∘ ! (!-inv-l (gluel p0)))))

    C≃[〈Z×Z〉×〈XY〉Z] : ∀ {x0 y0} (p0 : P x0 y0) → Equiv (CodesFor p0 (inm p0) id) ([〈Z×Z〉×〈XY〉Z] p0 p0 (gluemr p0 p0 p0))
    C≃[〈Z×Z〉×〈XY〉Z] p0 = glue-mr-m p0 p0 {gluemr p0 p0 p0} ∘equiv fix-path-equiv p0

    [〈Z×Z〉×〈XY〉Z]→C : ∀ {x0 y0} (p0 : P x0 y0) → ([〈Z×Z〉×〈XY〉Z] p0 p0 (gluemr p0 p0 p0)) → (CodesFor p0 (inm p0) id) 
    [〈Z×Z〉×〈XY〉Z]→C p0 = IsEquiv.g (snd (C≃[〈Z×Z〉×〈XY〉Z] p0))

    section : ∀ {x0 y0} (p0 : P x0 y0) (w : W) (p : inm p0 == w) → (CodesFor p0 w p)
    section p0 ._ id = ([〈Z×Z〉×〈XY〉Z]→C p0) (〈Z×Z〉×〈XY〉Z→[〈Z×Z〉×〈XY〉Z] ((_ , p0) , (_ , p0) , p0))


  module Retraction where    

    open Codes
    open Section

    CodesT = Σ \ (zww : Σ \ (z : Z) → Σ \ (w : W) → inm (snd z) == w) → CodesFor (snd (fst zww)) (fst (snd zww)) (snd (snd zww))

    glueml-uncurry : (zs : 〈Z×Z〉×〈YX〉Z) → Path {W} (inm (snd (fst zs))) (inm (snd (fst (snd zs))))
    glueml-uncurry (z1 , z2 , p) = glueml (snd z1) (snd z2) p

    -- [Z×Z×YXZ] → C
    ml-to-Codes : ∀ {x y} (pxy : P x y) {x' y'} (px'y' : P x' y') (α : Path (inm pxy) (inm px'y'))
                → (Trunc i+j (HFiber (glueml pxy px'y') α)) 
                → CodesT
    ml-to-Codes {x}{y} pxy {x'} px'y' α in-ml = ((_ , pxy) , (inl x') , (gluel px'y' ∘ α)) , IsEquiv.g (snd (glue-l-ml pxy px'y' {αm = α} id)) in-ml 

    -- [Z×Z×XYZ] → C
    mr-to-Codes : ∀ {x y} (pxy : P x y) {x' y'} (px'y' : P x' y') (α : Path (inm pxy) (inm px'y'))
                → (Trunc i+j (HFiber (gluemr pxy px'y') α)) 
                → CodesT
    mr-to-Codes {x}{y} pxy {x'}{y'} px'y' α in-mr = ((_ , pxy) , (inr y') , (gluer px'y' ∘ α)) , IsEquiv.g (snd (glue-r-mr pxy px'y' {αm = α} id)) in-mr

    -- like Z×YZ×XZ → [Z×XZ×YZ] (could compose with reassoc... but glueml is naturally dependent on the pair)
    make-ml : (zs : 〈Z×Z〉×〈YX〉Z) → Trunc i+j (HFiber (\ p → glueml-uncurry (fst zs , fst (snd zs) , p)) (glueml-uncurry zs))
    make-ml (_ , _ , p) = [ p , id ]

    -- like Z×XZ×YZ → [Z×XZ×YZ] (could compose with reassoc...)
    make-mr : (zs : 〈Z×Z〉×〈XY〉Z) → Trunc i+j (HFiber (\ p → gluemr-uncurry (fst zs , fst (snd zs) , p)) (gluemr-uncurry zs))
    make-mr (_ , _ , p) = [ p , id ]

    π111 : 〈Z×Z〉×〈XY〉Z → 〈Z×Z〉×〈XY〉Z
    π111 (z , _) = (z , z , (snd z))

    π112 : 〈Z×Z〉×〈XY〉Z → 〈Z×Z〉×〈YX〉Z
    π112 (z , _ , p) = (z , (_ , p) , snd z)

    π112' : 〈Z×Z〉×〈YX〉Z → 〈Z×Z〉×〈XY〉Z
    π112' (z , _ , p) = (z , (_ , p) , snd z)

    factor : π111 == π112' o π112
    factor = id

    test : ∀ zs → snd (fst zs) == snd (fst (π111 zs))
    test zs = id

    commute112 : (zs : 〈Z×Z〉×〈XY〉Z) → (mr-to-Codes (snd (fst zs)) (snd (fst (snd zs))) (gluemr-uncurry zs) (make-mr zs)) 
                                  == ml-to-Codes _ _ _ (make-ml (π112 zs))
    commute112 zs = {!!}

    commute111 : (zs : 〈Z×Z〉×〈XY〉Z) → (mr-to-Codes (snd (fst zs)) (snd (fst (snd zs))) (gluemr-uncurry zs) (make-mr zs)) ==
                                     (mr-to-Codes (snd (fst zs)) (snd (fst zs)) (gluemr-uncurry (π111 zs)) (make-mr (π111 zs)))
    commute111 zs = {!!}

    commute111' : (zs : 〈Z×Z〉×〈XY〉Z) → 〈Z×Z〉×〈XY〉Z→[〈Z×Z〉×〈XY〉Z] (π111 zs) == {!in-[〈Z×Z〉×〈XY〉Z] zs!}
    commute111' zs = {!!}
    
    retraction' : ∀ (zs : 〈Z×Z〉×〈XY〉Z) (c : [〈Z×Z〉×〈XY〉Z] (snd (fst zs)) (snd (fst (snd zs))) (gluemr-uncurry zs))
                →  IsEquiv.g (snd (glue-mr-m (snd (fst zs)) (snd (fst (snd zs))))) (〈Z×Z〉×〈XY〉Z→[〈Z×Z〉×〈XY〉Z] zs) 
                == IsEquiv.g (snd (glue-mr-m (snd (fst zs)) (snd (fst (snd zs))))) c
    retraction' zs = {!!}

  module OverZ {x0 : X} {y0 : Y} (p0 : P x0 y0) where
    open Codes p0
    open Section 
    open Retraction

    -- "C is a retract of [〈Z×Z〉×〈XY〉Z] by the inclusion" reduces the goal to retraction'
    retraction : (w : W) (p : Path{W} (inm p0) w) (c : CodesFor w p) → Path (section p0 w p) c
    retraction ._ id = elim-along-equiv _ (!equiv (C≃[〈Z×Z〉×〈XY〉Z] p0)) (λ c → ap (IsEquiv.g (snd (fix-path-equiv p0))) (retraction' ((_ , p0) , (_ , p0) , p0) c))

    contr : (w : W) (p : Path{W} (inm p0) w) → Contractible (CodesFor w p)
    contr w p = section p0 w p , retraction w p

    -- this is the same goal as the end of Step 1.2.1.1
    gluer0-connected : (y : Y) → ConnectedMap i+j (gluer0 p0 {y})
    gluer0-connected y = λ α → ntype (contr (inr y) α)

    -- it's a slightly different way of getting here:
    -- both use cf, and showing that Z×XZ is the pullback in that diagram
    -- amounts to moving gluel(p0) to the other side of an equation, which
    -- is what we are doing directly here

    glue-as-gluer0 : (y : Y) → glue{x0}{y} == (\ z → z ∘ ! (gluel p0)) o gluer0 p0
    glue-as-gluer0 y = λ≃ (λ z → coh (glue z) (gluel p0)) where 
      coh : {A : Type} {a b c : A} (α : a == b) (β : c == a) → α == ((α ∘ β) ∘ ! β)
      coh id id = id

    glue-connected' : (y : Y) → ConnectedMap i+j (glue{x = x0} {y})
    glue-connected' y  = transport (\ Z → ConnectedMap i+j Z) (! (glue-as-gluer0 y))
                                   (ConnectedMap.postcompose-equiv-connected (pre∘-equiv (! (gluel p0))) 
                                                                             (gluer0-connected y))

  -- make y0,p0 : P x0 y0 using connectivity 
  -- Z -> X is (S _)-connected, so to make an hprop for X, we can do it for Z
  glue-connected : (x0 : X) (y : Y) → ConnectedMap i+j (glue{x = x0}{y})
  glue-connected x0 y = Trunc-rec (raise-HProp (Πlevel (\ _ → (NType-is-HProp _)))) (λ yp0 → OverZ.glue-connected' (snd yp0) y)
                                  (fst (use-level (cf x0)))

  glue-map-total : (Σ \ xy → P (fst xy) (snd xy)) → Σ \ xy → Path{W} (inl (fst xy)) (inr (snd xy))
  glue-map-total ((x , y) , p) = ((x , y) , glue p)

  theorem : ConnectedMap i+j glue-map-total
  theorem = ConnectedMap.fiberwise-to-total-connected i+j (λ _ → glue) (λ xy → glue-connected (fst xy) (snd xy))

