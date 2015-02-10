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

  module Section {x0 y0} (p0 : P x0 y0) where
    open CodesGlueMaps
    open Codes p0

    〈-×Z〉×〈XY〉Z = Σ \ (z2 : Z) → P x0 (snd (fst z2))

    [〈-×Z〉×〈XY〉Z] : ∀ {x' y'} (px'y' : P x' y') (α : Path (inm p0) (inm px'y')) → Type
    [〈-×Z〉×〈XY〉Z] {x'}{y'} px'y' α = Trunc i+j (HFiber (gluemr p0 px'y') α)

    gluemr-uncurry : (zs : 〈-×Z〉×〈XY〉Z) → Path {W} (inm p0) (inm (snd (fst zs)))
    gluemr-uncurry (z2 , p) = gluemr p0 (snd z2) p

    〈-×Z〉×〈XY〉Z→[〈-×Z〉×〈XY〉Z] : ∀ (zs : 〈-×Z〉×〈XY〉Z) → [〈-×Z〉×〈XY〉Z] (snd (fst zs)) (gluemr-uncurry zs)
    〈-×Z〉×〈XY〉Z→[〈-×Z〉×〈XY〉Z] (_ , p) = [ p , id ] 

    Codes-diag-path-equiv : Equiv (CodesFor (inm p0) (gluemr p0 p0 p0)) (CodesFor (inm p0) id) 
    Codes-diag-path-equiv = apTrunc' (HFiber-result-equiv (ap (λ x → (_ , p0) , x) ((!-inv-l (gluel p0)) ∘ (m-to-mr-triangle-coh1 (gluer p0) (gluel p0) (gluel p0)))))

    [〈-×Z〉×〈XY〉Z]≃C0 : Equiv ([〈-×Z〉×〈XY〉Z] p0 (gluemr p0 p0 p0)) (CodesFor (inm p0) id)
    [〈-×Z〉×〈XY〉Z]≃C0 = (Codes-diag-path-equiv) ∘equiv !equiv (glue-mr-m p0 {gluemr p0 p0 p0})

    section : (w : W) (p : inm p0 == w) → (CodesFor w p)
    section ._ id = (fst ([〈-×Z〉×〈XY〉Z]≃C0)) (〈-×Z〉×〈XY〉Z→[〈-×Z〉×〈XY〉Z] ((_ , p0) , p0))

{-
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
{-
    commute111' : (zs : 〈Z×Z〉×〈XY〉Z) → 〈Z×Z〉×〈XY〉Z→[〈Z×Z〉×〈XY〉Z] (π111 zs) == {!in-[〈Z×Z〉×〈XY〉Z] zs!}
    commute111' zs = {!!}
-}
    
-}
  module Retraction {x0 : X} {y0 : Y} (p0 : P x0 y0) where
    open Codes p0
    open Section p0

    CodesT : Type
    CodesT = Σ \ (ww : Σ \ (w : W) → inm p0 == w) → CodesFor (fst ww) (snd ww)

    m-to-Codes : ∀ {x' y'} (px'y' : P x' y') (α : Path (inm p0) (inm px'y'))
                → (Trunc i+j (HFiber (gluem p0) ((_ , px'y') , α)) )
                → CodesT
    m-to-Codes {x'} px'y' α in-m = (inm px'y' , α) , in-m

    
    [〈-×Z〉×〈XY〉Z]t = Σ \ (zw : -×WZ p0) → [〈-×Z〉×〈XY〉Z] (snd (fst zw)) (snd zw)

    〈-×Z〉×〈XY〉Z→[〈-×Z〉×〈XY〉Z]t : 〈-×Z〉×〈XY〉Z → [〈-×Z〉×〈XY〉Z]t
    〈-×Z〉×〈XY〉Z→[〈-×Z〉×〈XY〉Z]t (z , px0y) = (z , (gluemr p0 (snd z) px0y)) , 〈-×Z〉×〈XY〉Z→[〈-×Z〉×〈XY〉Z] (z , px0y)

    〈-×Z〉×〈XY〉Z→[〈-×Z〉×〈XY〉Z]t-connected : ConnectedMap i+j 〈-×Z〉×〈XY〉Z→[〈-×Z〉×〈XY〉Z]t
    〈-×Z〉×〈XY〉Z→[〈-×Z〉×〈XY〉Z]t-connected = {!  !}
    
    diagram-chase : ∀ (zs : 〈-×Z〉×〈XY〉Z) 
                  →  m-to-Codes _ _ (snde (glue-mr-m p0) (〈-×Z〉×〈XY〉Z→[〈-×Z〉×〈XY〉Z] ((_ , p0) , p0)))
                  == m-to-Codes _ _ (snde (glue-mr-m (snd (fst zs))) (〈-×Z〉×〈XY〉Z→[〈-×Z〉×〈XY〉Z] zs))
    diagram-chase zs = {!!}

    -- Step R.3: 
    -- first, use connectedness along 〈-×Z〉×〈XY〉Z→[〈-×Z〉×〈XY〉Z]t
    -- then do the diagram chase
    -- note that the fst component must be the identity because singleton is contractible
    abstract
    -- Σ Codes is i+j-truncated, so can extend along foo
      retraction3 : (c' :  [〈-×Z〉×〈XY〉Z] p0 (gluemr p0 p0 p0)) → 
                    Path
                      (m-to-Codes p0 (gluemr-uncurry ((_ , p0) , p0)) (snde (glue-mr-m p0) (〈-×Z〉×〈XY〉Z→[〈-×Z〉×〈XY〉Z] (((x0 , y0) , p0) , p0))))
                      (m-to-Codes p0 (gluemr-uncurry ((_ , p0) , p0)) (snde (glue-mr-m p0) c'))
      retraction3 c' = ConnectedMap.extend i+j 〈-×Z〉×〈XY〉Z→[〈-×Z〉×〈XY〉Z]t 〈-×Z〉×〈XY〉Z→[〈-×Z〉×〈XY〉Z]t-connected
                    (λ t → Path{Σe (Σ (_==_ (inm p0))) (λ ww → CodesFor (fst ww) (snd ww))}
                                (m-to-Codes _ _ (snde (glue-mr-m p0) (〈-×Z〉×〈XY〉Z→[〈-×Z〉×〈XY〉Z] ( ((x0 , y0) , p0) , p0))))
                                (m-to-Codes _ _ (snde (glue-mr-m _) (snd t)))
                       ,   path-preserves-level (Σlevel (raise-level (-2<= _) singleton-contractible) (λ p → Codes-level (fst p) (snd p))))
                    diagram-chase 
                    (_ , c')

      retraction3-fst : (c' :  [〈-×Z〉×〈XY〉Z] p0 (gluemr p0 p0 p0)) → Path (ap fst (retraction3 c')) id
      retraction3-fst c' = HSet-UIP (raise-level { -2} {tl 0} (Inl (-2< _)) (raise-level (-2<= _) singleton-contractible)) _ _ _ _

    -- Step R.2: massage R.3, extracting the path we want from the Σ type
    retraction2 : (c' : [〈-×Z〉×〈XY〉Z] p0 (gluemr-uncurry (((x0 , y0) , p0) , p0)))  
                           →    snde (glue-mr-m p0) (〈-×Z〉×〈XY〉Z→[〈-×Z〉×〈XY〉Z] (((x0 , y0) , p0) , p0))
                             == snde (glue-mr-m p0) c'
    retraction2 c' = over-to-hom (changeover CodesFor' (retraction3-fst c') (over-o-ap CodesFor' {fst} (apdo snd (retraction3 c')))) where
    
    -- Step R.1: s (p (ν c')) == (ν c')
    -- peel off an annoying thing
    retraction1 : (c' :  [〈-×Z〉×〈XY〉Z] p0 (gluemr p0 p0 p0)) →
                 (fst [〈-×Z〉×〈XY〉Z]≃C0 (〈-×Z〉×〈XY〉Z→[〈-×Z〉×〈XY〉Z] (((x0 , y0) , p0) , p0))) ==
                 (fst [〈-×Z〉×〈XY〉Z]≃C0 c')
    retraction1 = λ c' → ap (fst Codes-diag-path-equiv) (retraction2 c') where

    -- Step R: by path induction and moving equivalences around, it suffices to show retraction1
    -- (this is the "C is a retract of blah" step... rather than using a retraction,
    --  we know what fiber we're in, and the retraction is an equivalence on that fiber)
    retraction : (w : W) (p : Path{W} (inm p0) w) (c : CodesFor w p) → Path (section w p) c
    retraction ._ id = elim-along-equiv (λ c → Path (section (inm p0) id) c) [〈-×Z〉×〈XY〉Z]≃C0 retraction1

  module OverZ {x0 : X} {y0 : Y} (p0 : P x0 y0) where
    open Codes p0
    open Section p0
    open Retraction p0

    -- so we need a section and a retraction
    contr : (w : W) (p : Path{W} (inm p0) w) → Contractible (CodesFor w p)
    contr w p = section w p , retraction w p

    -- Step D: what we want is a special case of codes being contractible
    gluer0-connected : (y : Y) → ConnectedMap i+j (gluer0 p0 {y})
    gluer0-connected y = λ α → ntype (contr (inr y) α)

    -- Step C: it suffices to show that gluer0 is connected
    -- slightly different way of getting here than in the ooTopos proof:
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

  -- Step B: make y0,p0 : P x0 y0 using connectivity 
  -- Z -> X is (S _)-connected, so to make an hprop for X, we can do it for Z
  glue-connected : (x0 : X) (y : Y) → ConnectedMap i+j (glue{x = x0}{y})
  glue-connected x0 y = Trunc-rec (raise-HProp (Πlevel (\ _ → (NType-is-HProp _)))) (λ yp0 → OverZ.glue-connected' (snd yp0) y)
                                  (fst (use-level (cf x0)))

  -- Working backwards, Step A: work in the slice

  glue-map-total : (Σ \ xy → P (fst xy) (snd xy)) → Σ \ xy → Path{W} (inl (fst xy)) (inr (snd xy))
  glue-map-total ((x , y) , p) = ((x , y) , glue p)

  theorem : ConnectedMap i+j glue-map-total
  theorem = ConnectedMap.fiberwise-to-total-connected i+j (λ _ → glue) (λ xy → glue-connected (fst xy) (snd xy))

