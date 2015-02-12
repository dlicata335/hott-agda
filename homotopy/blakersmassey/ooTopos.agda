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
    open OverZMaps p0

    Codes-diag-path-equiv : Equiv (CodesFor (inm p0) (gluemr p0 p0)) (CodesFor (inm p0) id) 
    Codes-diag-path-equiv = apTrunc' (HFiber-result-equiv (ap (λ x → (_ , p0) , x) ((!-inv-l (gluel p0)) ∘ (m-to-mr-triangle-coh1 (gluer p0) (gluel p0) (gluel p0)))))

    [Z×0YZ]≃C0 : Equiv ([Z×0YZ] p0 (gluemr p0 p0)) (CodesFor (inm p0) id)
    [Z×0YZ]≃C0 = (Codes-diag-path-equiv) ∘equiv !equiv (glue-mr-m p0 {gluemr p0 p0})

    section : (w : W) (p : inm p0 == w) → (CodesFor w p)
    section ._ id = (fst ([Z×0YZ]≃C0)) (Z×0YZ→[Z×0YZ] ((_ , p0) , p0))

  module Retraction {x0 : X} {y0 : Y} (p0 : P x0 y0) where
    open Codes p0
    open Section p0
    open OverZMaps p0

    CodesT : Type
    CodesT = Σ \ (ww : Σ \ (w : W) → inm p0 == w) → CodesFor (fst ww) (snd ww)

    in-Codes-m : ∀ {x' y'} {px'y' : P x' y'} {α : Path (inm p0) (inm px'y')}
                → (Trunc i+j (HFiber gluem ((_ , px'y') , α)) )
                → CodesT
    in-Codes-m {x'} {px'y' = px'y'} {α} in-m = (inm px'y' , α) , in-m


    shift1 : Z×0YZ → Z×X0Z 
    shift1 (z , p) = (_ , p) , p0

    shift2 : Z×X0Z → Z×0YZ 
    shift2 (z , p) = (_ , p) , p0

    diagram-chase1 : ∀ (zs : Z×0YZ) 
                  → in-Codes-m (snde (glue-ml-m (snd (fst (shift1 zs)))) (Z×X0Z→[Z×X0Z] (shift1 zs)))
                  == in-Codes-m (snde (glue-mr-m (snd (fst zs))) (Z×0YZ→[Z×0YZ] zs))
    diagram-chase1 zs = ! step1 ∘ {!!} where
      step1 :  in-Codes-m (snde (glue-mr-m (snd (fst zs))) (Z×0YZ→[Z×0YZ] zs))
            == in-Codes-m (Z×X-∨-xYZ→[Z×X-∨-xYZ] (Wedge.inl (_ , snd zs)))
      step1 = in-Codes-m (snde (glue-mr-m (snd (fst zs))) (Z×0YZ→[Z×0YZ] zs)) ≃〈 id 〉 
              ((inm (snd (fst zs)) , gluemr-uncurry zs) , snde (glue-mr-m (snd (fst zs))) (Z×0YZ→[Z×0YZ] zs)) ≃〈 pair= (pair= (! (gluer (snd zs)) ∘ gluer (snd (fst zs))) (PathOverPathFrom.in-PathOver-= (disc-to-square {!OK!}))) {!!} 〉 
              (_ , [ Wedge.inl (_ , snd zs) , id ]) ≃〈 id 〉 
              in-Codes-m (Z×X-∨-xYZ→[Z×X-∨-xYZ] (Wedge.inl (_ , snd zs))) ∎

    diagram-chase2 : ∀ (zs : Z×X0Z) 
                  → in-Codes-m (snde (glue-mr-m (snd (fst (shift2 zs)))) (Z×0YZ→[Z×0YZ] (shift2 zs)))
                  == in-Codes-m (snde (glue-ml-m (snd (fst zs))) (Z×X0Z→[Z×X0Z] zs))
    diagram-chase2 zs = {!!}

    diagram-chase : ∀ (zs : Z×0YZ) 
                  → in-Codes-m (snde (glue-mr-m p0) (Z×0YZ→[Z×0YZ] (shift2 (shift1 zs))))
                  == in-Codes-m (snde (glue-mr-m (snd (fst zs))) (Z×0YZ→[Z×0YZ] zs))
    diagram-chase zs = diagram-chase1 zs ∘ diagram-chase2 (shift1 zs)

    
    [Z×0YZ]t = Σ \ (zw : -×WZ) → [Z×0YZ] (snd (fst zw)) (snd zw)

    Z×0YZ→[Z×0YZ]t : Z×0YZ → [Z×0YZ]t
    Z×0YZ→[Z×0YZ]t (z , px0y) = (z , (gluemr (snd z) px0y)) , Z×0YZ→[Z×0YZ] (z , px0y)

    -- probably some lemmas that would help here?
    -- seems like it should be an instance of something more general
    Z×0YZ→[Z×0YZ]t-connected : ConnectedMap i+j Z×0YZ→[Z×0YZ]t
    Z×0YZ→[Z×0YZ]t-connected ( (z , w) , h) = ntype (Trunc-elim
                                                       (λ h₁ → Trunc i+j (HFiber Z×0YZ→[Z×0YZ]t ((z , w) , h₁)))
                                                       (λ _ → Trunc-level) 
                                                       (λ hr → path-induction (λ w₁ sndhr → Trunc i+j (HFiber Z×0YZ→[Z×0YZ]t ((z , w₁) , [ fst hr , sndhr ])))
                                                                               [ (z , fst hr) , id ] 
                                                                               (snd hr))
                                                       h ,
                                                     Trunc-elim _ (λ _ → path-preserves-level Trunc-level) (secondcase ((z , w) , h))) where
       secondcase : ∀ zwh → (h : HFiber Z×0YZ→[Z×0YZ]t zwh) → Trunc-elim (λ h₁ → Trunc i+j (HFiber Z×0YZ→[Z×0YZ]t (fst zwh , h₁))) (λ z₁ → Trunc-level) (λ hr → path-induction (λ w₁ sndhr → Trunc i+j (HFiber Z×0YZ→[Z×0YZ]t ((_ , w₁) , [ fst hr , sndhr ]))) [ (_ , fst hr) , id ] (snd hr)) (snd zwh) == [ h ]
       secondcase ._ (h1 , id) = id
    
    -- Step R.3: 
    -- first, use connectedness along Z×0YZ→[Z×0YZ]t
    -- then do the diagram chase
    -- note that the fst component must be the identity because singleton is contractible
    abstract
    -- Σ Codes is i+j-truncated, so can extend along foo
      retraction3 : (c' :  [Z×0YZ] p0 (gluemr p0 p0)) → 
                    Path
                      (in-Codes-m (snde (glue-mr-m p0) (Z×0YZ→[Z×0YZ] (((x0 , y0) , p0) , p0))))
                      (in-Codes-m (snde (glue-mr-m p0) c'))
      retraction3 c' = ConnectedMap.extend i+j Z×0YZ→[Z×0YZ]t Z×0YZ→[Z×0YZ]t-connected
                    (λ t → Path{Σe (Σ (_==_ (inm p0))) (λ ww → CodesFor (fst ww) (snd ww))}
                                (in-Codes-m (snde (glue-mr-m p0) (Z×0YZ→[Z×0YZ] ( ((x0 , y0) , p0) , p0))))
                                (in-Codes-m (snde (glue-mr-m _) (snd t)))
                       ,   path-preserves-level (Σlevel (raise-level (-2<= _) singleton-contractible) (λ p → Codes-level (fst p) (snd p))))
                    diagram-chase 
                    (_ , c')

      retraction3-fst : (c' :  [Z×0YZ] p0 (gluemr p0 p0)) → Path (ap fst (retraction3 c')) id
      retraction3-fst c' = HSet-UIP (raise-level { -2} {tl 0} (Inl (-2< _)) (raise-level (-2<= _) singleton-contractible)) _ _ _ _

    -- Step R.2: massage R.3, extracting the path we want from the Σ type
    retraction2 : (c' : [Z×0YZ] p0 (gluemr-uncurry (((x0 , y0) , p0) , p0)))  
                           →    snde (glue-mr-m p0) (Z×0YZ→[Z×0YZ] (((x0 , y0) , p0) , p0))
                             == snde (glue-mr-m p0) c'
    retraction2 c' = over-to-hom (changeover CodesFor' (retraction3-fst c') (over-o-ap CodesFor' {fst} (apdo snd (retraction3 c')))) where
    
    -- Step R.1: s (p (ν c')) == (ν c')
    -- peel off an annoying thing
    retraction1 : (c' :  [Z×0YZ] p0 (gluemr p0 p0)) →
                 (fst [Z×0YZ]≃C0 (Z×0YZ→[Z×0YZ] (((x0 , y0) , p0) , p0))) ==
                 (fst [Z×0YZ]≃C0 c')
    retraction1 = λ c' → ap (fst Codes-diag-path-equiv) (retraction2 c') where

    -- Step R: by path induction and moving equivalences around, it suffices to show retraction1
    -- (this is the "C is a retract of blah" step... rather than using a retraction,
    --  we know what fiber we're in, and the retraction is an equivalence on that fiber)
    retraction : (w : W) (p : Path{W} (inm p0) w) (c : CodesFor w p) → Path (section w p) c
    retraction ._ id = elim-along-equiv (λ c → Path (section (inm p0) id) c) [Z×0YZ]≃C0 retraction1

  module OverZ {x0 : X} {y0 : Y} (p0 : P x0 y0) where
    open Codes p0
    open Section p0
    open Retraction p0
    open OverZMaps p0

    -- so we need a section and a retraction
    contr : (w : W) (p : Path{W} (inm p0) w) → Contractible (CodesFor w p)
    contr w p = section w p , retraction w p

    -- Step D: what we want is a special case of codes being contractible
    gluer0-connected : (y : Y) → ConnectedMap i+j (gluer0 {y})
    gluer0-connected y = λ α → ntype (contr (inr y) α)

    -- Step C: it suffices to show that gluer0 is connected
    -- slightly different way of getting here than in the ooTopos proof:
    -- both use cf, and showing that Z×XZ is the pullback in that diagram
    -- amounts to moving gluel(p0) to the other side of an equation, which
    -- is what we are doing directly here

    glue-as-gluer0 : (y : Y) → glue{x0}{y} == (\ z → z ∘ ! (gluel p0)) o gluer0
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

