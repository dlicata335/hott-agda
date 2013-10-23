{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open FatPushoutFib
open ConnectedMap
open Truncation

{- TRANASLATION GUIDE:
 P : X → Y → Type
 Z = Σ x,y. P x y
 f : Z → X = π1 
 g : Z → Y = π1 o π2
 cf is equivalent to f (i.e. π1) being connected, and similarly for cg
-}
module homotopy.blakersmassey.TypeTheory (X Y : Type) (P : X → Y → Type)
                                         (i' j' : _)
                                         (cf : (x : X) → Connected (S i') (Σ \ y → P x y))
                                         (cg : (y : Y) → Connected (S j') (Σ \ x → P x y)) where

  i : TLevel
  i = S i'

  j : TLevel
  j = S j'

  i+j = plus2 i' j'

  W = Pushout P
                                       
  glue-map : (x : X) (y : Y) → P x y → Path{W} (inl x) (inr y)
  glue-map x y p = gluer x y p ∘ ! (gluel x y p)

{- For the translation guides:
  Z×WY = Pullback{W} inm inr
  Z×WX = Pullback{W} inm inl
  Z×WZ = Pullback{W} inm inm

  Z×XZ = Pullback{X} f f 
  Z×YZ = Pullback{Y} g g 
-}

  -- TRANSLATION GUIDE: 
  -- ZxXZ → ZxWX
  -- expands to (x1,y1,p1) (x2,y2,p2) (p3 : y1 = y2) ->
  --            (x1,y1,p1) x2 such that inm(x1,y1,p1) == inl x2
  -- the map here was (z1 , z2 , p) = z1 , f z2 , ! (gluelr z2) ∘ ap inr p ∘ gluer z1
  -- 
  -- so the hfiber of this is those 
  --    x1 y1 p1 x2 α as below
  -- such that there exist (x1',y1',p1') (x2',y2',p2') (p3' : y1' = y2')
  --    such that ((x1,y1,p1),x2,α) == ((x1',y1',p1'),x2',!(gluelr x2' y2' p2') ∘ ap inr p3' ∘ gluer x1' y1' p1')
  --
  -- breaking apart the path in the Σ
  -- the hfiber of this is those 
  --    x1 y1 p1 x2 α as below
  -- such that there exist (x1',y1',p1') (x2',y2',p2') (p3' : y1' = y2') where
  --    (x1,y1,p1) == (x1',y1',p1')
  --    x2 == x2'
  --    α = !(gluelr x2' y2' p2') ∘ ap inr p3' ∘ gluer x1' y1' p1'
  --
  -- so we can contract away x1' y1' p1' x2' y2' by path induction, unifying
  --    x1 = x1'
  --    y1 = y1' = y2'
  --    p1 = p1'
  --    x2 = x2'
  --    p3 = refl
  -- which reduces the formula to 
  -- there exist p2' such that
  --    α = !(gluelr x2 y1 p2') ∘ gluer x1 y1 p1
  --
  -- rearrange to gluelr x2 y1 p2' = gluer x1 y1 p1 ∘ ! α per Eric
  --
  -- is this where we stop, or is there more simplification to do?  
  
  codes-l : (x1 : X) (y1 : Y) (p1 : P x1 y1) (x2 : X) (α : Path{W} (inm x1 y1 p1) (inl x2)) → Type
  codes-l x1 y1 p1 x2 α = Σ (λ (p2' : P x2 y1) → (glue-map x2 y1 p2') == (gluer x1 y1 p1) ∘ ! α)

  codes-r : (x1 : X) (y1 : Y) (p1 : P x1 y1) (y2 : Y) (α : Path{W} (inm x1 y1 p1) (inr y2)) → Type
  codes-r x1 y1 p1 y2 α = Σ (λ (p2 : P x1 y2) → glue-map x1 y2 p2 == α ∘ ! (gluel x1 y1 p1))

  -- TRANSLATION:
  -- the left and right are the translation of the inl and inr cases of the old codes-m
  -- the P is part of the translation of the 
  codes-m : (x1 : X) (y1 : Y) (p1 : P x1 y1) 
            (x2 : X) (y2 : Y) (p2 : P x2 y2) → Path{W} (inm x1 y1 p1) (inm x2 y2 p2) → Type
  codes-m x1 y1 p1 x2 y2 p2 α = Pushout {Σ (λ (p : x1 == x2) → α == ! (gluel x2 y2 p2) ∘ ap inl p ∘ gluel x1 y1 p1)}
                                        {Σ (λ (q : y1 == y2) → α == ! (gluer x2 y2 p2) ∘ ap inr q ∘ gluer x1 y1 p1)}
                                        (λ pα1 qα2 → (transport (λ (pr : X × Y) → P (fst pr) (snd pr))
                                                       (pair×≃ (fst pα1) (fst qα2)) p1 == p2)
                                                     × {! some condition about snd pα1 and snd pα2 ? !} )

{-
  -- source of Codes middle map
  CM = Pushout{Z}{Z×XZ}{Z×YZ} (λ z → z , z , id) (λ z → z , z , id)

  codes-m : CM -> Z×WZ
  codes-m = Pushout-rec (λ {(z1 , z2 , p) → z1 , z2 , gluel z2 ∘ ap inl p ∘ ! (gluel z1)})
                           (λ z → z , z , id)
                           (λ {(z1 , z2 , p) → z1 , z2 , ! (gluer z2) ∘ ap inr p ∘ gluer z1})
                           (λ z → ap (λ p → z , z , p) (!-inv-r (gluel z) ∘ ∘-assoc (gluel z) id (! (gluel z))))
                           (λ z → ap (λ p → z , z , p) (! (!-inv-l (gluer z) ∘ ∘-assoc (! (gluer z)) id (gluer z))))

-}

  Codes : (x1 : X) (y1 : Y) (p1 : P x1 y1) (w : W) → Path (inm x1 y1 p1) w → Type
  Codes x1 y1 p1 = Pushout-elim _ 
                         (λ x2 α → Trunc i+j (codes-l x1 y1 p1 x2 α)) 
                         (λ x2 y2 p2 α → Trunc i+j (codes-m x1 y1 p1 x2 y2 p2 α)) 
                         (λ y2 α → Trunc i+j (codes-r x1 y1 p1 y2 α))
                         {!!}
                         {!!}
                         -- (λ z' →
                         --      λ≃
                         --      (λ p →
                         --         ap (λ p' → Trunc i+j (HFiber codes-r p')) (pair≃ id (pair≃ id (!-inv-r-front (gluer z') p))) ∘
                         --         ua (Codes-glue.eqvmr z z' (! (gluer z') ∘ p)) ∘
                         --         ap (λ p' → Trunc i+j (HFiber codes-m (z , z' , p')))
                         --         (transport-Path-right (! (gluer z')) p))
                         --      ∘ transport-→-pre' (λ z0 → Path (inm z) z0) (gluer z') _)
    {-
                           (λ z' → λ≃ (λ p → ua (Codes-gluer.eqv z z' p) ∘
                                             ap (λ p' → Trunc i+j (HFiber codes-m (z , z' , p'))) (transport-Path-right (! (gluer z')) p))
                                             ∘ transport-→-pre' (λ z0 → Path (inm z) z0) (gluer z') _)
    -}

  center :  (x1 : X) (y1 : Y) (p1 : P x1 y1) (w : W) (α : Path (inm x1 y1 p1) w) → (Codes x1 y1 p1 w α)
  center x1 y1 p1 .(inm x1 y1 p1) id = [ inm (id , ! (∘-assoc (! (gluel x1 y1 p1)) id (gluel x1 y1 p1)) ∘ ! (!-inv-l (gluel x1 y1 p1)))
                                             (id , ! (∘-assoc (! (gluer x1 y1 p1)) id (gluer x1 y1 p1)) ∘ ! (!-inv-l (gluer x1 y1 p1)))
                                             (id , {!!}) ] -- need definition of Codesm

  Codes-contr : (x1 : X) (y1 : Y) (p1 : P x1 y1) (w : W) (α : Path (inm x1 y1 p1) w) → Contractible (Codes x1 y1 p1 w α)
  Codes-contr x1 y1 p1 w α = center x1 y1 p1 w α , {!the big diagram chase goes here!}

  cπ1 : ConnectedMap i {Σ \ x -> Σ \ y → P x y}{X} fst
  cπ1 = λ x → {!cf x!} -- and contract with J

  glue-map-total : (Σ \ x → Σ \ y → P x y) → Σ \ x → Σ \ y → Path{W} (inl x) (inr y)
  glue-map-total (x , y , p) = (x , y , glue-map x y p)
  
  glue-map-connected''' : (x1 : X) (y1 : Y) (p1 : P x1 y1) 
                      → (y : Y) (α : Path {W} (inm x1 y1 p1) (inr y))
                      → Contractible (Trunc i+j (Σ \ (p2 : P x1 y) → glue-map x1 y p2 == α ∘ ! (gluel x1 y1 p1)))
  glue-map-connected''' x1 y1 p1 y = Codes-contr x1 y1 p1 (inr y)

  glue-map-connected'' : (x1 : X) (y1 : Y) (p1 : P x1 y1) 
                      → (y : Y) (α : Path {W} (inm x1 y1 p1) (inr y))
                      → Contractible (Trunc i+j (HFiber glue-map-total (x1 , y , α ∘ ! (gluel x1 y1 p1))))
  glue-map-connected'' = {!glue-map-connected''!} -- simplify HFiber of projections 

  glue-map-connected' : (x1 : X) (y1 : Y) (p1 : P x1 y1) 
                      → (y : Y) (α : Path {W} (inl x1) (inr y))
                      → Contractible (Trunc i+j (HFiber glue-map-total (x1 , y , α)))
  glue-map-connected' = {!glue-map-connected''!}   -- because composition with ! (gluel x1 y1 p1) is an equivalence

  glue-map-connected : ((x : X) (y : Y) (α : Path{W} (inl x) (inr y)) 
            → Contractible (Trunc i+j (HFiber glue-map-total (x , y , α))))
  glue-map-connected x y α = extend i fst cπ1
                               (λ x' →
                                  ((y' : _) (p' : _) →
                                   Contractible (Trunc i+j (HFiber glue-map-total (x' , y' , p'))))
                                  ,
                                  raise-HProp
                                  (Πlevel (λ _ → Πlevel (λ _ → Contractible-is-HProp _))))
                               (λ p₁ → glue-map-connected' (fst p₁) (fst (snd p₁)) (snd (snd p₁))) x y α

  theorem : ConnectedMap i+j glue-map-total
  theorem (x , y , p) = ntype (glue-map-connected x y p)
