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

  glue-map : Z → X×WY 
  glue-map z = (f z , g z , gluer z ∘ gluel z)

  Z×WY = Pullback{W} inm inr
  Z×WX = Pullback{W} inm inl
  Z×WZ = Pullback{W} inm inm

  ZxWZ→ZxWY : Z×WZ → Z×WY
  ZxWZ→ZxWY (z1 , z2 , p) = z1 , g z2 , gluer z2 ∘ p

  module CodesTT where
    -- difference with Codes∞Topos: keep glue-map the same; change the args

    Codes : (z : Z) (w : W) → Path (inm z) w → Type
    Codes z = Pushout-elim _ 
                           (λ x p → Trunc i+j (HFiber glue-map (x , g z , (gluer z ∘ ! p))))
                           (λ z' p → Trunc i+j (HFiber glue-map (f z , g z' , gluer z' ∘ p ∘ gluel z))) -- FIXME choice of which side z/z' go on
                           (λ y p → Trunc i+j (HFiber glue-map (f z , y , p ∘ gluel z)))
                           {!!} -- Trunc i+j (HFiber glue-map (f z' , g z , gluer z ∘ ! p ∘ ! (gluel z'))) 
                                -- = Trunc i+j (HFiber glue-map (f z , g z' , gluer z' ∘ p ∘ gluel z))
                           {!easy!}

    center : (z : Z) (w : W) (p : Path (inm z) w) → (Codes z w p)
    center z ._ id = [ z , ap (λ p → f z , g z , p) (! (∘-assoc (gluer z) id (gluel z))) ]

    postulate
      Codes-contr : (z : Z) (w : W) (p : Path (inm z) w) → Contractible (Codes z w p)

  module Step1TTSymmetric where
    open CodesTT

    step2 : (z1 z2 : Z) (p : inl (f z1) ≃ inr (g z2))
          -> Contractible (Trunc i+j (HFiber glue-map (f z1 , g z2 , p)))
    step2 z1 z2 p = transport (\ x -> Contractible (Trunc i+j (HFiber glue-map (f z1 , g z2 , x))))
                              {!OK!}
                              (Codes-contr z1 (inm z2) (! (gluer z2) ∘ p ∘ ! (gluel z1)))
  
    step1 : (x : X) (y : Y) (p : Path{W} (inl x) (inr y)) 
          → Contractible (Trunc i+j (HFiber glue-map (x , y , p)))
    step1 = extend i f cf
              (λ x' →
                 ((y' : _) (p' : _) → Contractible (Trunc i+j (HFiber glue-map (x' , y' , p')))) ,
                  raise-HProp (Πlevel (λ _ → Πlevel (λ _ → Contractible-is-HProp _))))
              (λ z1 →
                   extend j g cg
                   (λ y' → ((p' : _) → Contractible (Trunc i+j (HFiber glue-map (f z1 , y' , p')))) ,
                           raise-HProp (Πlevel (λ _ → Contractible-is-HProp _)))
                   (λ z2 p → step2 z1 z2 p)) 

  module Step1TTLeft where
    open CodesTT

    step2 : (z1 : Z) (y : Y) (p : inl (f z1) ≃ inr y)
          -> Contractible (Trunc i+j (HFiber glue-map (f z1 , y , p)))
    step2 z1 y p = transport (\ x -> Contractible (Trunc i+j (HFiber glue-map (f z1 , y , x))))
                             {!OK!}
                             (Codes-contr z1 (inr y) (p ∘ ! (gluel z1)))
  
    step1 : (x : X) (y : Y) (p : Path{W} (inl x) (inr y)) 
          → Contractible (Trunc i+j (HFiber glue-map (x , y , p)))
    step1 = extend i f cf
              (λ x' →
                 ((y' : _) (p' : _) → Contractible (Trunc i+j (HFiber glue-map (x' , y' , p')))) ,
                  raise-HProp (Πlevel (λ _ → Πlevel (λ _ → Contractible-is-HProp _))))
              step2

  Z×XZ = Pullback{X} f f 
  Z×YZ = Pullback{Y} g g 

  -- FIXME: could rewrite these as maps of fibrations, since they leave fst unchanged

  glue-map-r : Z×XZ → Z×WY
  glue-map-r (z1 , z2 , p) = z1 , g z2 , (gluelr z2 ∘ ap inl p ∘ ! (gluel z1))

  glue-map-l : Z×YZ → Z×WX
  glue-map-l (z1 , z2 , p) = z1 , f z2 , ! (gluelr z2) ∘ ap inr p ∘ gluer z1

  CM = Pushout{Z}{Z×XZ}{Z×YZ} (λ z → z , z , id) (λ z → z , z , id)

  glue-map-m : CM -> Z×WZ
  glue-map-m = Pushout-rec (λ {(z1 , z2 , p) → z1 , z2 , gluel z2 ∘ ap inl p ∘ ! (gluel z1)})
                           (λ z → z , z , id)
                           (λ {(z1 , z2 , p) → z1 , z2 , ! (gluer z2) ∘ ap inr p ∘ gluer z1})
                           (λ z → ap (λ p → z , z , p) (!-inv-r (gluel z) ∘ ∘-assoc (gluel z) id (! (gluel z))))
                           (λ z → ap (λ p → z , z , p) (! (!-inv-l (gluer z) ∘ ∘-assoc (! (gluer z)) id (gluer z))))

  module Codes∞Topos where
    -- difference with CodesTT: args are always the same; change the glue-map

    module MoveToConnectedMap where
      fiberwise-to-total : ∀ {A} {B1 B2 : A → Type} (f : ∀ a → B1 a → B2 a) → Σ B1 → Σ B2
      fiberwise-to-total f (a , b) = (a , f a b)

      fiberwise-to-total-connected : ∀ n {A} {B1 B2 : A → Type} (f : ∀ a → B1 a → B2 a)
           → (∀ a → ConnectedMap n (f a))
           → ConnectedMap n (fiberwise-to-total f)
      fiberwise-to-total-connected n f cf (a , b2) = transport (λ A → NType -2 (Trunc n A))
                                       (! (({!commute and path induction!} ∘ apΣ' id-equiv (λ a' → apΣ' id-equiv (λ b1 → ! ΣPath.path))) ∘ Σassoc.path))
                                       (cf a b2)

      module Lemma (n : _) {A B C : _} (h : C → B) 
                (f : B → A) (g : C → A) 
                (α : f o h ≃ g)
                (ch : ConnectedMap n h)
                (a : A) where

         h' : HFiber g a → HFiber f a
         h' (c , p) = h c , p ∘ ap≃ α

         h'-connected-ump : ConnectedMapUMP n h'
         h'-connected-ump P br = (λ {(b , p) → ext b p}) ,
                                 ext-β where
           ext : (b : B) → (p : Path (f b) a) → fst (P (b , p))
           ext = ConnectedMap.extend n h ch
                    (\ b -> ((p : _) → fst (P (b , p))) , Πlevel (\ p -> snd (P (b , p))))
                    (λ c (p : f (h c) ≃ a) → transport (\ p -> fst (P (h c , p)))
                                                       (!-inv-l-back p (ap≃ α) ∘ ! (∘-assoc p (! (ap≃ α)) (ap≃ α)))
                                                       (br (c , p ∘ ! (ap≃ α))))

           ext-β : (x : HFiber g a) → ext (fst (h' x)) (snd (h' x)) ≃ br x
           ext-β (c , p) =   adjustment ∘ 
                             ap≃
                             (extendβ n h ch
                              (λ b →
                                 ((p' : _) → fst (P (b , p'))) , Πlevel (λ p' → snd (P (b , p'))))
                              (λ c' (p' : f (h c') ≃ a) →
                                 transport (λ p0 → fst (P (h c' , p0)))
                                 (!-inv-l-back p' (ap≃ α) ∘ ! (∘-assoc p' (! (ap≃ α)) (ap≃ α)))
                                 (br (c' , p' ∘ ! (ap≃ α))))
                              c)
                             {p ∘ ap≃ α} where
            adjustment : (transport (λ p0 → fst (P (h c , p0)))
                               (!-inv-l-back (p ∘ ap≃ α) (ap≃ α) ∘
                                ! (∘-assoc (p ∘ ap≃ α) (! (ap≃ α)) (ap≃ α)))
                               (br (c , (p ∘ ap≃ α) ∘ ! (ap≃ α))))
                    ≃ (br (c , p))
            adjustment = apd (λ p' → br (c , p'))
                             (!-inv-r-back p (ap≃ α) ∘ !(∘-assoc p (ap≃ α) (! (ap≃ α))))
                         ∘ {!!}



           
             



    module Codes-gluel where

      CM' : Z → Type
      CM' z1 = Wedge {Σ (λ z2 → f z1 ≃ f z2)} {Σ (λ z2 → g z1 ≃ g z2)} (z1 , id) (z1 , id)

      CM-to-CM' : CM → Σ CM'
      CM-to-CM' = Pushout-rec (λ {(z1 , z2 , p) → z1 , inl (z2 , p)})
                              (λ z → z , inl (z , id))
                              (λ {(z1 , z2 , p) → z1 , inr (z2 , p)})
                              (λ _ → id)
                              (λ z → pair≃ id (gluer _ ∘ gluel _))

      CM'-to-CM : Σ CM' → CM
      CM'-to-CM (z , w) = Pushout-rec (λ {(z2 , p) → inl (z , z2 , p)})
                                      (λ _ → inm z) 
                                      (λ {(z2 , p) → inr (z , z2 , p)})
                                      (λ _ → gluel z)
                                      (λ _ → gluer z)
                                      w

      CM-eqv : Equiv CM (Σ CM')
      CM-eqv = {!!}

      cΣ1 : ∀ z → Connected i (Σ (λ z2 → f z ≃ f z2))
      cΣ1 z = transport (Connected i) (apΣ' id-equiv (λ z' → flip≃)) (cf (f z))

      cΣ2 : ∀ z → Connected j (Σ (λ z2 → g z ≃ g z2))
      cΣ2 z = transport (Connected j) (apΣ' id-equiv (λ z' → flip≃)) (cg (g z))
  
      CM'-to-prod : ∀ z -> CM' z -> (Σ (λ z2 → f z ≃ f z2)) × (Σ (λ z2 → g z ≃ g z2))
      CM'-to-prod z = wedge-to-prod

      CM'-to-prod-connected : ∀ z → ConnectedMap i+j (CM'-to-prod z)
      CM'-to-prod-connected z = WedgeToProd.ci _ _ (cΣ1 z) (cΣ2 z)


{-   
    -- trying to do Codes-glue directly gets ugly fast

    P : X → Y → Type
    P x y = Σ \ z -> (f z ≃ x) × (g z ≃ y)

    -- gluep : ∀ {x y} → P x y → Path{W}(inl x)(inr y)
    -- gluep (z , p1 , p2) = {!!}
    
    cΣ1 : (x : X) → Connected i (Σ \ y -> P x y)
    cΣ1 = ConnectedMap.extend i f cf (\ x -> Connected i (Σ (P x)) , raise-HProp (NType-is-HProp _))
                                     (λ z → ntype ([ (g z) , (z , id , id) ] , 
                                                   (Trunc-elim _ (λ _ → path-preserves-level Trunc-level)
                                                                 (λ {(y , z' , p1 , p2) → {!!}}))))

    module Codes-gluer where
      map1 : ∀ z z' p → 
             (Trunc i+j (HFiber glue-map-m (z , z' , (! (gluer z')) ∘ p)))
           → (Trunc i+j (HFiber glue-map-r (z , g z' , p)))
      map1 z z' p = Trunc-func (λ {(cm , b) → {!Pushout-rec !}})

      map2' : ∀ z z' (p : inm z ≃ inr (g z'))
                z1 z2 (p12 : f z1 ≃ f z2)
              → (q : z1 ≃ z)
              → (r : g z2 ≃ g z')
              → ap inr r ∘ gluelr z2 ∘ ap inl p12 ∘ ! (gluel z1) ≃ p ∘ ap inm q
              → (HFiber glue-map-m (z , z' , (! (gluer z')) ∘ p))
      map2' z z' p .z z2 p12 id r α = {!p!}

      map2 : ∀ z z' p → 
             (Trunc i+j (HFiber glue-map-r (z , g z' , p)))
           → (Trunc i+j (HFiber glue-map-m (z , z' , (! (gluer z')) ∘ p)))
      map2 z z' p = Trunc-func (λ {((z1 , z2 , p12) , b) → {!snd (snd (coe (Path-Pullback _ _) b))!}})

    eqv : (z z' : Z) (p : Path (inm z) (inr (g z')))
        → Equiv (Trunc i+j (HFiber glue-map-m (z , z' , (! (gluer z')) ∘ p)))
                        (Trunc i+j (HFiber glue-map-r (z , g z' , p)))
    eqv z z' p = {!!}
-}
    eqv : (z z' : Z) (p : _)
        → Equiv (Trunc i+j (HFiber glue-map-m (z , z' , p)))
                (Trunc i+j (HFiber glue-map-r (ZxWZ→ZxWY (z , z' , p))))
    eqv z z' p = {!!}

    Codes : (z : Z) (w : W) → Path (inm z) w → Type
    Codes z = Pushout-elim _ 
                           (λ x p → Trunc i+j (HFiber glue-map-l (z , x , p))) 
                           (λ z' p → Trunc i+j (HFiber glue-map-m (z , z' , p)))
                           (λ y p → Trunc i+j (HFiber glue-map-r (z , y , p)))
                           {!!}
                           {!!}
    {-
                           (λ z' → λ≃ (λ p → ua (Codes-gluer.eqv z z' p) ∘
                                             ap (λ p' → Trunc i+j (HFiber glue-map-m (z , z' , p'))) (transport-Path-right (! (gluer z')) p))
                                             ∘ transport-→-pre' (λ z0 → Path (inm z) z0) (gluer z') _)
    -}

    -- ENH probably easier to do the calculations if written out as a coe with pathsfrom contractible
    center : (z : Z) (w : W) (p : Path (inm z) w) → Codes z w p
    center z ._ id = [ inm z , id ]

    postulate
      Codes-contr : (z : Z) (w : W) (p : Path (inm z) w) → Contractible (Codes z w p)
    

  module Step1∞ToposLeft where

    step2 : ConnectedMap i+j glue-map-r
    step2 (z1 , y , p) = ntype (Codes∞Topos.Codes-contr z1 (inr y) p)

    -- FIXME: passing from step2 to step2' is a bit unmotivated from a type-theoretic perspective,
    --        unless you think Codes∞Topos.Codes is nicer than CodesTT.Codes

    -- FIXME: is there a smoother way to do this?
    -- one option is the equality in eq' below
    step2' : (z1 : Z) (y : Y) (p : inl (f z1) ≃ inr y) -> Contractible (Trunc i+j (HFiber glue-map (f z1 , y , p)))
    step2' z1 y p = {!fact1!} , {!TODO!} where
      fact1 : Trunc i+j (HFiber glue-map (f z1 , y , (p ∘ ! (gluel z1)) ∘ gluel z1))
      fact1 = extend i+j glue-map-r step2
                (λ {(z , y , p) → Trunc i+j (HFiber glue-map (f z , y , p ∘ gluel z)) , Trunc-level})
                (λ { (z1 , z2 , p) → [ z2 , (coe (! (Path-Pullback inl inr)) (! p , id , {!OK!})) ] }) 
                (z1 , y , p ∘ ! (gluel z1))

    step1 : ((x : X) (y : Y) (p : Path{W} (inl x) (inr y)) 
              → Contractible (Trunc i+j (HFiber glue-map (x , y , p))))
    step1 = extend i f cf  -- ENH: copied from above
              (λ x' →
                 ((y' : _) (p' : _) → Contractible (Trunc i+j (HFiber glue-map (x' , y' , p')))) ,
                  raise-HProp (Πlevel (λ _ → Πlevel (λ _ → Contractible-is-HProp _))))
              step2'

{-
  module Test where
  
    -- does it help more than having one less thing to contract...?

    glue-map-r' : (z : Z) → (Σ \ z' → f z ≃ f z') -> (Σ \ y -> Path{W} (inm z) (inr y))
    glue-map-r' z1 (z2 , p) = (g z2 , (gluelr z2 ∘ ap inl p ∘ ! (gluel z1)))

    eq : (z1 : Z) (z2 : Z) (p : _) → HFiber (glue-map-r' z1) (g z2 , p ∘ ! (gluel z1))
                                   ≃ HFiber glue-map (f z1 , g z2 , p)
    eq = {!HFiber glue-map (f z1!}
-}
    

  module Step1Comparison where

    -- gap between type theoretic proof and ∞topos proof
    -- in the infinity topos proof, you next show 
    Step2-∞Topos = (z1 : Z) (y : Y) (p : inm z1 ≃ inr y) → Contractible (Trunc i+j (HFiber glue-map-r (z1 , y , p)))
    -- in the type-theoretic proof, you next show 
    Step2-TT = (z1 : Z) (y : Y) (p : inl (f z1) ≃ inr y) -> Contractible (Trunc i+j (HFiber glue-map (f z1 , y , p)))

    -- didn't fill in the proof terms, but this works
    eq' : ∀ z y p → (HFiber glue-map-r (z , y , p ∘ ! (gluel z)))
                  ≃ (HFiber glue-map (f z , y , p)) 
    eq' z y p = 
           HFiber glue-map-r (z , y , p ∘ ! (gluel z)) ≃〈 {!!} 〉 
           (Σ \ z1 → Σ \ z2 -> Σ \ (p12 : f z1 ≃ f z2) → glue-map-r (z1 , z2 , p12) ≃ (z , y , p ∘ ! (gluel z))) ≃〈 {!!} 〉 
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

    eq : Step2-∞Topos ≃ Step2-TT 
    eq = ap {M = \ z y → (p : inm z ≃ inr y) → Contractible (Trunc i+j (HFiber glue-map-r (z , y , p)))} 
            (λ B → (z : Z) (y : Y) → B z y)
            (λ≃ (λ z → λ≃ (λ y → apΠ' (pre∘-equiv (gluel z))
                                       (λ p → ap (λ A → Contractible (Trunc i+j A)) (eq' z y p)))))

    -- can therefore do Step2-∞Topos from CodesTT
    step2-from-CodesTT : Step2-∞Topos
    step2-from-CodesTT z1 y p = 
      transport (\ x -> Contractible (Trunc i+j (HFiber glue-map-r (z1 , y , x)))) {!OK!}
        (transport (\ A -> Contractible (Trunc i+j A)) (! (eq' z1 y (p ∘ gluel z1)))
                   (CodesTT.Codes-contr z1 (inr y) p))

    -- can also do it directly from Codes∞Topos
    step2-from-Codes∞Topos : Step2-∞Topos
    step2-from-Codes∞Topos z1 y p = (Codes∞Topos.Codes-contr z1 (inr y) p)

    -- can use eq to get step1
    -- ENH: copied from above
    step1 : ((x : X) (y : Y) (p : Path{W} (inl x) (inr y)) 
              → Contractible (Trunc i+j (HFiber glue-map (x , y , p))))
    step1 = extend i f cf 
              (λ x' →
                 ((y' : _) (p' : _) → Contractible (Trunc i+j (HFiber glue-map (x' , y' , p')))) ,
                  raise-HProp (Πlevel (λ _ → Πlevel (λ _ → Contractible-is-HProp _))))
              (coe eq step2-from-CodesTT)
          
  theorem : ConnectedMap i+j glue-map
  theorem (x , y , p) = ntype (Step1∞ToposLeft.step1 x y p)
