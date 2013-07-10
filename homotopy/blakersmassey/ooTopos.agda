{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open FatPushout
open ConnectedMap
open Truncation

module homotopy.blakersmassey.ooTopos (Z X Y : Type) 
                                      (i' j' : _)
                                      (f : Z → X) (g : Z → Y)
                                      (cf : ConnectedMap (S i') f) (cg : ConnectedMap (S j') g) where
  -- FIXME move
  Pullback : ∀ {Z X Y : Type} → (f : X → Z) (g : Y → Z) → Type
  Pullback {_}{X}{Y} f g = Σ \ x -> Σ \ y -> f x ≃ g y

  Path-Pullback-Type : ∀ {Z X Y : Type} → (f : X → Z) (g : Y → Z) → 
                       (x x' : X) (y y' : Y) (p : f x ≃ g y) (p' : f x' ≃ g y')
                  → Type
  Path-Pullback-Type f g x x' y y' p p' = Σ \(px : Path x x') -> Σ \(py : Path y y') → ap g py ∘ p ≃ p' ∘ ap f px

  postulate
    Path-Pullback : ∀ {Z X Y : Type} → (f : X → Z) (g : Y → Z) → 
                    ∀ {x x' y y' p p'} 
                    → Path{Pullback f g} (x , y , p) (x' , y' , p')
                    ≃ Path-Pullback-Type f g x x' y y' p p'
--  Path-Pullback f g = {!!}

{-

  fiberwise-to-total : ∀ {A} {B1 B2 : A → Type} (f : ∀ a → B1 a → B2 a) → Σ B1 → Σ B2
  fiberwise-to-total f (a , b) = (a , f a b)
 
  fiberwise-to-total-connected : ∀ n {A} {B1 B2 : A → Type} (f : ∀ a → B1 a → B2 a)
       → (∀ a → ConnectedMap n (f a))
       → ConnectedMap n (fiberwise-to-total f)
  fiberwise-to-total-connected n f cf (a , b2) = transport (λ A → NType -2 (Trunc n A))
                                   (! (({!commute and path induction!} ∘ apΣ' id-equiv (λ a' → apΣ' id-equiv (λ b1 → ! ΣPath.path))) ∘ Σassoc.path))
                                   (cf a b2)

  module ConnectedMapOnFibers 
               (n : _) {A B C : _} (h : C → B) 
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
-}


  i : TLevel
  i = S i'

  j : TLevel
  j = S j'

  i+j = plus2 i' j'

  W = Pushout f g
                                       
  X×WY = Pullback{W} inl inr 

  gluelr : (z : Z) → Path{W} (inl (f z)) (inr (g z))
  gluelr z = gluer z ∘ gluel z

  glue-map : Z → X×WY 
  glue-map z = (f z , g z , gluelr z)

  Z×WY = Pullback{W} inm inr
  Z×WX = Pullback{W} inm inl
  Z×WZ = Pullback{W} inm inm

  g2 : Z×WZ → Z×WY
  g2 (z1 , z2 , p) = z1 , g z2 , gluer z2 ∘ p

  f2 : Z×WZ → Z×WX
  f2 (z1 , z2 , p) = z1 , f z2 , ! (gluel z2) ∘ p

  Z×XZ = Pullback{X} f f 
  Z×YZ = Pullback{Y} g g 


  -- note: could rewrite these as maps of fibrations, since they leave fst unchanged,
  -- but that didn't seem to help much.  

  codes-r : Z×XZ → Z×WY
  codes-r (z1 , z2 , p) = z1 , g z2 , (gluelr z2 ∘ ap inl p ∘ ! (gluel z1))

  codes-l : Z×YZ → Z×WX
  codes-l (z1 , z2 , p) = z1 , f z2 , ! (gluelr z2) ∘ ap inr p ∘ gluer z1

  -- source of Codes middle map
  CM = Pushout{Z}{Z×XZ}{Z×YZ} (λ z → z , z , id) (λ z → z , z , id)

  codes-m : CM -> Z×WZ
  codes-m = Pushout-rec (λ {(z1 , z2 , p) → z1 , z2 , gluel z2 ∘ ap inl p ∘ ! (gluel z1)})
                           (λ z → z , z , id)
                           (λ {(z1 , z2 , p) → z1 , z2 , ! (gluer z2) ∘ ap inr p ∘ gluer z1})
                           (λ z → ap (λ p → z , z , p) (!-inv-r (gluel z) ∘ ∘-assoc (gluel z) id (! (gluel z))))
                           (λ z → ap (λ p → z , z , p) (! (!-inv-l (gluer z) ∘ ∘-assoc (! (gluer z)) id (gluer z))))

  module Codes-glue where
{-
      CM' : Z → Type
      CM' z1 = Wedge {Σ (λ z2 → f z1 ≃ f z2)} {Σ (λ z2 → g z1 ≃ g z2)} (z1 , id) (z1 , id)
  
      module CM≃CM' where

        to : CM → Σ CM'
        to = Pushout-rec (λ {(z1 , z2 , p) → z1 , inl (z2 , p)})
                                (λ z → z , inl (z , id))
                                (λ {(z1 , z2 , p) → z1 , inr (z2 , p)})
                                (λ _ → id)
                                (λ z → pair≃ id (gluer _ ∘ gluel _))

        from : Σ CM' → CM
        from (z , w) = Pushout-rec (λ {(z2 , p) → inl (z , z2 , p)})
                                      (λ _ → inm z) 
                                      (λ {(z2 , p) → inr (z , z2 , p)})
                                      (λ _ → gluel z)
                                      (λ _ → gluer z)
                                      w

        abstract
          from-to : ∀ x -> from (to x) ≃ x
          from-to = Pushout-elim _ (λ _ → id) (λ z → gluel z) (λ _ → id)
                                (λ z →
                                     transport (λ z' → from (to z') ≃ z') (gluel z) id ≃〈 transport-Path (from o to) (λ x → x) (gluel z) id 〉
                                     ap (λ x → x) (gluel z) ∘ id ∘ ! (ap (from o to) (gluel z)) ≃〈 ap (λ q → q ∘ id ∘ ! (ap (from o to) (gluel z))) (ap-id (gluel z)) 〉
                                     (gluel z) ∘ id ∘ ! (ap (from o to) (gluel z)) ≃〈 ∘-assoc (gluel z) id (! (ap (from o to) (gluel z))) 〉
                                     (gluel z) ∘ ! (ap (from o to) (gluel z)) ≃〈 ap (λ q → gluel z ∘ ! q) (idl z) 〉
                                     gluel z ∎)
                                (λ z →
                                     transport (λ z' → Path (from (to z')) z') (gluer z) (gluel z) ≃〈 transport-Path (from o to) (\ x -> x) (gluer z) _ 〉 
                                     ap (λ x → x) (gluer z) ∘ gluel z ∘ ! (ap (from o to) (gluer z)) ≃〈 ap (λ q → q ∘ gluel z ∘ ! (ap (from o to) (gluer z))) (ap-id (gluer z))〉
                                     (gluer z) ∘ gluel z ∘ ! (ap (from o to) (gluer z)) ≃〈 ∘-assoc (gluer z) (gluel z) (! (ap (from o to) (gluer z)))〉  
                                     ((gluer z) ∘ gluel z) ∘ ! (ap (from o to) (gluer z)) ≃〈 ap (\ x -> ((gluer z) ∘ gluel z) ∘ ! x) (idr z) 〉  
                                     ((gluer z) ∘ gluel z) ∘ ! ((gluer z) ∘ gluel z) ≃〈 !-inv-r ((gluer z) ∘ gluel z) 〉  
                                     id ∎) where
                  idl : (z : _) → (ap (from o to) (gluel z)) ≃ id
                  idl z = (ap (from o to) (gluel z)) ≃〈 ap-o from to (gluel z)  〉
                          (ap from (ap to (gluel z))) ≃〈 {!β!}  〉
                          id ∎
  
                  idr : (z : _) → (ap (from o to) (gluer z)) ≃ gluer z ∘ gluel z
                  idr z = (ap (from o to) (gluer z)) ≃〈 ap-o from to (gluer z)  〉
                          (ap from (ap to (gluer z))) ≃〈 {!β!}  〉
                          (ap from (pair≃ id (gluer _ ∘ gluel _))) ≃〈 {!! (∘-Σ id id (gluer _) (gluel _))!}  〉
                          (ap from (pair≃ id (gluer _) ∘ (pair≃ id (gluel _)))) ≃〈 ap-∘ from (pair≃ id (gluer _)) (pair≃ id (gluel _))  〉
                          (ap from (pair≃ id (gluer _)) ∘ ap from (pair≃ id (gluel _))) ≃〈 {!β!}  〉
                          (gluer z ∘ ap from (pair≃ id (gluel _))) ≃〈 {!β!}  〉
                          gluer z ∘ gluel z ∎
  
          to-from : ∀ x -> to (from x) ≃ x
          to-from (z , w) = Pushout-elim (\ w -> to (from (z , w)) ≃ (z , w))
                                         (λ _ → id) (λ z' → pair≃ id (gluel z')) (λ _ → id)
                                         {!OK!} {!OK!} w

        eqv : Equiv CM (Σ CM')
        eqv = improve (hequiv to from from-to to-from)

        path : CM ≃ (Σ CM')
        path = ua eqv

      cΣ1 : ∀ z → Connected i (Σ (λ z2 → f z ≃ f z2))
      cΣ1 z = transport (Connected i) (apΣ' id-equiv (λ z' → flip≃)) (cf (f z))

      cΣ2 : ∀ z → Connected j (Σ (λ z2 → g z ≃ g z2))
      cΣ2 z = transport (Connected j) (apΣ' id-equiv (λ z' → flip≃)) (cg (g z))
  
      CM'-to-prod : ∀ z -> CM' z -> (Σ (λ z2 → f z ≃ f z2)) × (Σ (λ z2 → g z ≃ g z2))
      CM'-to-prod z = wedge-to-prod

      CM'-to-prod-connected : ∀ z → ConnectedMap i+j (CM'-to-prod z)
      CM'-to-prod-connected z = WedgeToProd.ci _ _ (cΣ1 z) (cΣ2 z)
-}
      Z×XZ×YZ = Σ \ z -> (Σ (λ z2 → f z ≃ f z2)) × (Σ (λ z2 → g z ≃ g z2))
{-
      ΣCM'-to-prod : Σ CM' → Z×XZ×YZ
      ΣCM'-to-prod = fiberwise-to-total CM'-to-prod

      CM-to-prod : CM → Z×XZ×YZ
      CM-to-prod = ΣCM'-to-prod o CM≃CM'.to

      CM-to-prod-connected : ConnectedMap i+j CM-to-prod
      CM-to-prod-connected = transport (\ (p : Σ \(A : Type) → A → Z×XZ×YZ) → ConnectedMap i+j (snd p))
                                       (pair≃ (! CM≃CM'.path)
                                              ((ap (λ x → fiberwise-to-total CM'-to-prod o x) (type≃β CM≃CM'.eqv ∘ ap coe (!-invol CM≃CM'.path))) ∘ transport-→-pre (! CM≃CM'.path) _)) 
                                       (fiberwise-to-total-connected i+j CM'-to-prod CM'-to-prod-connected)
-}
--        PB-r = Σ \ (p1 : Z×WZ) → Σ \ (p2 : Z×XZ) → codes-r p2 ≃ g2 p1

      module Prod≃Pullback-L where
        PB-l = Pullback codes-l f2 

        -- could do this by (1) writing maps and checking composites
        --                  (2) chain of type equivalences, but will be annoying to calculate that the map is right
        --                  (3) showing universal property of pullback

        postulate
          FIXME : ∀ {A} → A

        prod-pb : Z×XZ×YZ → PB-l
        prod-pb (z1 , (z2 , p2) , (z3 , p3)) = (z3 , z1 , !  p3) , 
                                                (z3 , z2 , gluel z2 ∘ ap inl p2 ∘ ! (gluel z1) ∘ ! (gluer z1) ∘ ! (ap inr p3) ∘ gluer z3) , 
                                                coe (! (Path-Pullback inm inl)) (id , p2 , FIXME)

        mutual
          pb-prod' : ∀ z1 z2 (p : inm z1 ≃ inm z2) z3 z4 (q : _) → 
                       (Σ \ (s : z3 ≃ z1) → Σ \ (t : (f z4) ≃ (f z2)) → 
                             (ap inl t ∘ ! (gluer z4 ∘ gluel z4) ∘ ap inr q ∘ gluer z3)
                           ≃ ((! (gluel z2) ∘ p) ∘ ap inm s))
                     → Z×XZ×YZ
          pb-prod' z1 z2 p .z1 z4 q (id , t , w) = z4 , (z2 , t) , z1 , ! q  -- doesn't use p and w 
  
          pb-prod : PB-l → Z×XZ×YZ
          pb-prod ((z3 , z4 , q) , (z1 , z2 , p) , r) = pb-prod' z1 z2 p z3 z4 q (coe (Path-Pullback _ _) r)


        comp1 : (x : _) → pb-prod (prod-pb x) ≃ x
        comp1 (z1 , (z2 , p2) , (z3 , p3)) =
          (pb-prod (prod-pb (z1 , (z2 , p2) , z3 , p3))) ≃〈 id 〉 
          pb-prod' z3 z2 (gluel z2 ∘ ap inl p2 ∘ ! (gluel z1) ∘ ! (gluer z1) ∘ ! (ap inr p3) ∘ gluer z3)
                   z3 z1 (! p3) (coe (Path-Pullback inm inl {z3}{z3}{f z1}{f z2}{ ! (gluelr z1) ∘ ap inr (! p3) ∘ gluer z3}) (coe (! (Path-Pullback inm inl)) (id , p2 , FIXME))) ≃〈 ap (pb-prod' z3 z2 (gluel z2 ∘ ap inl p2 ∘ ! (gluel z1) ∘ ! (gluer z1) ∘ ! (ap inr p3) ∘ gluer z3) z3 z1 (! p3)) (ap≃ (transport-inv-2 (λ x → x) (Path-Pullback inm inl {z3} {z3} {f z1} {f z2} { ! (gluelr z1) ∘ ap inr (! p3) ∘ gluer z3}))) 〉 
          (z1 , (z2 , p2) , z3 , ! (! p3)) ≃〈 pair≃ id (pair≃ id (pair≃ id (!-invol p3))) 〉
          (z1 , (z2 , p2) , z3 , p3) ∎

        comp2 : (x : _) → prod-pb (pb-prod x) ≃ x
        comp2 


        prod≃pb-l : PB-l ≃ Z×XZ×YZ
        prod≃pb-l = {!!}


{-      
  
      eqvmr : (z z' : Z) (p : inm z ≃ inm z')
        → Equiv (Trunc i+j (HFiber codes-m (z , z' , p)))
                (Trunc i+j (HFiber codes-r (g2 (z , z' , p))))
      eqvmr z z' p = {!!}

      eqvlm : (z z' : Z) (p : inm z ≃ inm z')
        → Equiv (Trunc i+j (HFiber codes-l (f2 (z , z' , p))))
                (Trunc i+j (HFiber codes-m (z , z' , p)))
      eqvlm z z' p = {!!}

  Codes : (z : Z) (w : W) → Path (inm z) w → Type
  Codes z = Pushout-elim _ 
                         (λ x p → Trunc i+j (HFiber codes-l (z , x , p))) 
                         (λ z' p → Trunc i+j (HFiber codes-m (z , z' , p)))
                         (λ y p → Trunc i+j (HFiber codes-r (z , y , p)))
                         {!!}
                         (λ z' →
                              λ≃
                              (λ p →
                                 ap (λ p' → Trunc i+j (HFiber codes-r p')) (pair≃ id (pair≃ id (!-inv-r-front (gluer z') p))) ∘
                                 ua (Codes-glue.eqvmr z z' (! (gluer z') ∘ p)) ∘
                                 ap (λ p' → Trunc i+j (HFiber codes-m (z , z' , p')))
                                 (transport-Path-right (! (gluer z')) p))
                              ∘ transport-→-pre' (λ z0 → Path (inm z) z0) (gluer z') _)
    {-
                           (λ z' → λ≃ (λ p → ua (Codes-gluer.eqv z z' p) ∘
                                             ap (λ p' → Trunc i+j (HFiber codes-m (z , z' , p'))) (transport-Path-right (! (gluer z')) p))
                                             ∘ transport-→-pre' (λ z0 → Path (inm z) z0) (gluer z') _)
    -}

  -- ENH might be easier to do the uniqueness if written out as a coe with pathsfrom contractible
  center : (z : Z) (w : W) (p : Path (inm z) w) → Codes z w p
  center z ._ id = [ inm z , id ]

  Codes-contr : (z : Z) (w : W) (p : Path (inm z) w) → Contractible (Codes z w p)
  Codes-contr z w p = center z w p , {!!}
    
  codes-r-connected : ConnectedMap i+j codes-r
  codes-r-connected (z1 , y , p) = ntype (Codes-contr z1 (inr y) p)

  -- could use eq instead
  glue-map-connected' : (z1 : Z) (y : Y) (p : inl (f z1) ≃ inr y) -> Contractible (Trunc i+j (HFiber glue-map (f z1 , y , p)))
  glue-map-connected' z1 y p = {!fact1!} , {!TODO!} where
    fact1 : Trunc i+j (HFiber glue-map (f z1 , y , (p ∘ ! (gluel z1)) ∘ gluel z1))
    fact1 = extend i+j codes-r codes-r-connected
              (λ {(z , y , p) → Trunc i+j (HFiber glue-map (f z , y , p ∘ gluel z)) , Trunc-level})
              (λ { (z1 , z2 , p) → [ z2 , (coe (! (Path-Pullback inl inr)) (! p , id , {!OK!})) ] }) 
              (z1 , y , p ∘ ! (gluel z1))
  {-
    -- didn't fill in the proof terms, but this works
    eq' : ∀ z y p → (HFiber codes-r (z , y , p ∘ ! (gluel z)))
                  ≃ (HFiber glue-map (f z , y , p)) 
    eq' z y p = 
           HFiber codes-r (z , y , p ∘ ! (gluel z)) ≃〈 {!!} 〉 
           (Σ \ z1 → Σ \ z2 -> Σ \ (p12 : f z1 ≃ f z2) → codes-r (z1 , z2 , p12) ≃ (z , y , p ∘ ! (gluel z))) ≃〈 {!!} 〉 
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
    eq = ap {M = \ z y → (p : inm z ≃ inr y) → Contractible (Trunc i+j (HFiber codes-r (z , y , p)))} 
            (λ B → (z : Z) (y : Y) → B z y)
            (λ≃ (λ z → λ≃ (λ y → apΠ' (pre∘-equiv (gluel z))
                                       (λ p → ap (λ A → Contractible (Trunc i+j A)) (eq' z y p)))))
  -}

  glue-map-connected : ((x : X) (y : Y) (p : Path{W} (inl x) (inr y)) 
            → Contractible (Trunc i+j (HFiber glue-map (x , y , p))))
  glue-map-connected = extend i f cf
                       (λ x' →
                         ((y' : _) (p' : _) → Contractible (Trunc i+j (HFiber glue-map (x' , y' , p')))) ,
                           raise-HProp (Πlevel (λ _ → Πlevel (λ _ → Contractible-is-HProp _))))
                       glue-map-connected'

  theorem : ConnectedMap i+j glue-map
  theorem (x , y , p) = ntype (glue-map-connected x y p)
-}