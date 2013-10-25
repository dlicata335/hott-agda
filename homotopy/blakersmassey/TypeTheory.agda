{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude hiding (Z ; ntype)
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

  -- TRANSLATION GUIDE:
  -- Z×WY = Pullback{W} inm inr
  -- Z×WX = Pullback{W} inm inl
  -- Z×WZ = Pullback{W} inm inm
  -- Z×XZ = Pullback{X} f f 
  -- Z×YZ = Pullback{Y} g g 

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
  codes-l x1 y1 p1 x2 α = Σ (λ (p21 : P x2 y1) → (glue-map x2 y1 p21) == (gluer x1 y1 p1) ∘ ! α)

  codes-r : (x1 : X) (y1 : Y) (p1 : P x1 y1) (y2 : Y) (α : Path{W} (inm x1 y1 p1) (inr y2)) → Type
  codes-r x1 y1 p1 y2 α = Σ (λ (p12 : P x1 y2) → glue-map x1 y2 p12 == α ∘ ! (gluel x1 y1 p1))

  -- codes-l pulled back along Z×WZ → Z×WX to be over Z×WZ;
  -- pullback is just substitution!
  codes-l-Z : (x1 : X) (y1 : Y) (p1 : P x1 y1) 
              (x2 : X) (y2 : Y) (p2 : P x2 y2) → Path{W} (inm x1 y1 p1) (inm x2 y2 p2) → Type
  codes-l-Z x1 y1 p1 x2 y2 p2 α = 
       Σ (λ (p21 : P x2 y1) → glue-map _ _ p21 == (gluer _ _ p1) ∘ ! (gluel _ _ p2 ∘ α))

  -- α == ! (gluel _ _ p2) ∘ ! (glue-map x2 y1 p3) ∘ gluer _ _ p1)

  -- HFiber of the map from Z×XZ×YZ → Z×WZ, with the hfiber simplified away
  codes-m-r : (x1 : X) (y1 : Y) (p1 : P x1 y1) 
             (x2 : X) (y2 : Y) (p2 : P x2 y2) → Path{W} (inm x1 y1 p1) (inm x2 y2 p2) → Type
  codes-m-r x1 y1 p1 x2 y2 p2 α = 
       Σ (λ (p3 : P x1 y2) → α == ! (gluer x2 y2 p2) ∘ glue-map x1 y2 p3 ∘  gluel x1 y1 p1)


  Z = Σ (λ x → Σ (λ y → P x y)) 
  Z×YZ = Σ (λ (x1' : X) → Σ (λ (y' : Y) → Σ (λ (x2' : X) → P x1' y' × P x2' y')))
  Z×XZ = Σ (λ (y1' : Y) → Σ (λ (x' : X) → Σ (λ (y2' : Y) → P x' y1' × P x' y2')))
  Z×WZ = Σ \ (x1 : X) → Σ \ (y1 : Y) -> Σ \ (p1 : P x1 y1) -> 
                     Σ \ (x2 : X) → Σ \ (y2 : Y) -> Σ \ (p2 : P x2 y2) → Path{W} (inm x1 y1 p1) (inm x2 y2 p2) 

  -- this definition of 
  -- codes-m is basically the same as in ooTopos, except for
  -- a slight rearrangement, which lets you skip a few equality proofs
  module CodesMHFibPushout where
    CM : Type
    CM = Pushout.Pushout
        { Z }
        { Z×YZ }
        { Z×XZ } 
        (λ {(x , y , p) → (x , y , x , p , p)})
        (λ {(x , y , p) → (y , x , y , p , p)})
  
    codes-m-map : CM → Z×WZ
    codes-m-map = (Pushout.Pushout-rec {C = Z×WZ}
          (λ {(x1' , y1' , x2' , p11' , p21')
            → (x1' , y1' , p11' , x2' , y1' , p21' , (! (gluer _ _ p21')) ∘ (gluer x1' y1' p11')) })
          (λ {(y1' , x1' , y2' ,  p11' , p12')
            → (x1' , y1' , p11' , x1' , y2' , p12' , (! (gluel _ _ p12')) ∘ gluel _ _ p11') }) 
          (λ z → ap
                   (λ h →
                      fst z ,
                      fst (snd z) , snd (snd z) , fst z , fst (snd z) , snd (snd z) , h)
                   (! (! (!-inv-l (gluer _ _ _)) ∘ !-inv-l (gluel _ _ _)))))
  
    codes-m : (x1 : X) (y1 : Y) (p1 : P x1 y1) 
              (x2 : X) (y2 : Y) (p2 : P x2 y2) → Path{W} (inm x1 y1 p1) (inm x2 y2 p2) → Type
    codes-m x1 y1 p1 x2 y2 p2 α = HFiber codes-m-map ((x1 , y1 , p1 , x2 , y2 , p2 , α))

  {-
    codes-m->m-l : (x1 : X) (y1 : Y) (p1 : P x1 y1) 
                 (x2 : X) (y2 : Y) (p2 : P x2 y2) (α : Path{W} (inm x1 y1 p1) (inm x2 y2 p2))
               → codes-m x1 y1 p1 x2 y2 p2 α 
               → codes-l-Z x1 y1 p1 x2 y2 p2 α 
    codes-m->m-l x1 y1 p1 x2 y2 p2 α (cm1 , cm2) = Pushout.Pushout-elim
                                                   (λ x →
                                                      codes-m-map x == (x1 , y1 , p1 , x2 , y2 , p2 , α) →
                                                      codes-m-l x1 y1 p1 x2 y2 p2 α)
                                                   (λ {(x1' , y' , x2' , p1' , p2') eq → {!!}})
                                                   {!!}
                                                   {!!}
                                                   cm1 cm2
  -}

  module CodesMHFibWedge (x1 : X) (y1 : Y) (p1 : P x1 y1) where
    Z×X- = Σ \ y2 -> P x1 y2
    -×YZ = Σ \ x2 → P x2 y1

    -×WZ : Type
    -×WZ = Σ \ (x2 : X) -> Σ \ (y2 : Y) → Σ \ (p2 : P x2 y2) → Path{W} (inm x1 y1 p1) (inm x2 y2 p2)

    CM : Type
    CM = Pushout.Wedge { Z×X- } { -×YZ } (y1 , p1) (x1 , p1) 
    
    left-map : Z×X- → -×WZ
    left-map (y2 , p21) = x1 , y2 , p21 , ! (gluel _ _ p21) ∘ gluel _ _ p1

    right-map : -×YZ → -×WZ
    right-map (x2 , p21) = x2 , y1 , p21 , ! (gluer _ _ p21) ∘ gluer _ _ p1

    codes-m-map : CM → -×WZ 
    codes-m-map = Pushout.Pushout-rec left-map
                                      right-map 
                                      (λ _ → pair≃ id (pair≃ id (pair≃ id (! (!-inv-l (gluer _ _ _)) ∘ !-inv-l (gluel _ _ _)))))

    codes-m : (x2 : X) (y2 : Y) (p2 : P x2 y2) → Path{W} (inm x1 y1 p1) (inm x2 y2 p2) → Type
    codes-m x2 y2 p2 α = HFiber codes-m-map (x2 , y2 , p2 , α)

    -- intermediate definitions of codes-m-l and codes-m-r that are a little more hfibered up
    ZxX-xYZ = ((Σ \ y2 -> P x1 y2) × Σ \ x2 → P x2 y1)


    -- FIXME: note these two might be swapped

    codes-m-l-map : ZxX-xYZ -> -×WZ 
    codes-m-l-map x = left-map (fst x) -- x1 , (y2 , (p12 , ! (gluel _ _ p12) ∘ gluel _ _ p1))

    codes-m-r-map : ZxX-xYZ -> -×WZ 
    codes-m-r-map x = right-map (snd x)
    
    codes-m-l' : (x2 : X) (y2 : Y) (p2 : P x2 y2) → Path{W} (inm x1 y1 p1) (inm x2 y2 p2) → Type 
    codes-m-l' x2 y2 p2 α = HFiber codes-m-l-map (x2 , y2 , p2 , α)

    codes-m-r' : (x2 : X) (y2 : Y) (p2 : P x2 y2) → Path{W} (inm x1 y1 p1) (inm x2 y2 p2) → Type 
    codes-m-r' x2 y2 p2 α = HFiber codes-m-r-map (x2 , y2 , p2 , α)

    m-l==m-l' : (x2 : X) (y2 : Y) (p2 : P x2 y2) (α : Path{W} (inm x1 y1 p1) (inm x2 y2 p2))
               → codes-m-l' x2 y2 p2 α 
               == codes-l-Z x1 y1 p1 x2 y2 p2 α 
    m-l==m-l' x2 y2 p2 α = {!!}

    m-r==m-r' : (x2 : X) (y2 : Y) (p2 : P x2 y2) (α : Path{W} (inm x1 y1 p1) (inm x2 y2 p2))
               → codes-m-r' x2 y2 p2 α 
               == codes-m-r x1 y1 p1 x2 y2 p2 α 
    m-r==m-r' x2 y2 p2 α = {!!}

    -- so it suffices to show that these exist and are i+j connected

    codes-map=codes-m-l-map : ∀ x → codes-m-map x == codes-m-l-map (Pushout.wedge-to-prod x)
    codes-map=codes-m-l-map = Pushout.Pushout-elim _ (λ p → {!!}) {!!} {!!}
  
    m==m-l' : (x2 : X) (y2 : Y) (p2 : P x2 y2) (α : Path{W} (inm x1 y1 p1) (inm x2 y2 p2))
               → codes-m x2 y2 p2 α 
               -> codes-m-l' x2 y2 p2 α 
    m==m-l' x2 y2 p2 α (cm1 , cm2) = {!!} 

    m==m-r' : (x2 : X) (y2 : Y) (p2 : P x2 y2) (α : Path{W} (inm x1 y1 p1) (inm x2 y2 p2))
               → codes-m x2 y2 p2 α 
               -> codes-m-l' x2 y2 p2 α 
    m==m-r' x2 y2 p2 α (cm1 , cm2) = {!Pushout.wedge-to-prod cm1!} 

  module CodesMPushout where
    codes-m : (x1 : X) (y1 : Y) (p1 : P x1 y1)
              (x2 : X) (y2 : Y) (p2 : P x2 y2) → Path{W} (inm x1 y1 p1) (inm x2 y2 p2) → Type
    codes-m x1 y1 p1 x2 y2 p2 α = Pushout.Pushout {{!!}}
                                                  {Σ \ (α12 : x1 == x2) → α == ! (gluel _ _ p2) ∘ ap inl α12 ∘ gluel _ _ p1} 
                                                  {Σ \ (α12 : y1 == y2) → α == ! (gluer _ _ p2) ∘ ap inr α12 ∘ gluer _ _ p1}
                                                  {!!}
                                                  {!!}

  open CodesMHFibPushout

  codes-glue-l : ∀ x1 y1 p1 → (x : X) (y : Y) (p : P x y) →
      transport (λ w → Path (inm x1 y1 p1) w → Type) (gluel x y p)
      (λ α → Trunc i+j (codes-m x1 y1 p1 x y p α))
      ≃ (λ α → Trunc i+j (codes-l x1 y1 p1 x α))
  codes-glue-l x1 y1 p1 x y p = {!STS!} where
    step1 :  (α : _) → 
        (Trunc i+j (codes-m x1 y1 p1 x y p (! (gluel x y p) ∘ α)))
      ≃ (Trunc i+j (codes-l-Z x1 y1 p1 x y p (! (gluel x y p) ∘ α)))
    step1 = {!!}

    step2 :  (α : _) → 
        (Trunc i+j (codes-l-Z x1 y1 p1 x y p (! (gluel x y p) ∘ α)))
      ≃ (Trunc i+j (codes-l x1 y1 p1 x α))
    step2 α = ap (λ A → Trunc i+j (Σe (P x y1) A)) (λ≃ (λ p3 → {!cancel inverses!}))

    STS :  (α : _) → 
        (Trunc i+j (codes-m x1 y1 p1 x y p (! (gluel x y p) ∘ α)))
      ≃ (Trunc i+j (codes-l x1 y1 p1 x α))
    STS α = step2 α ∘ step1 α


  Codes : (x1 : X) (y1 : Y) (p1 : P x1 y1) (w : W) → Path (inm x1 y1 p1) w → Type
  Codes x1 y1 p1 = Pushout-elim (\ w -> Path (inm x1 y1 p1) w → Type)
                         (λ x2 α → Trunc i+j (codes-l x1 y1 p1 x2 α)) 
                         (λ x2 y2 p2 α → Trunc i+j (codes-m x1 y1 p1 x2 y2 p2 α)) 
                         (λ y2 α → Trunc i+j (codes-r x1 y1 p1 y2 α))
                         (codes-glue-l x1 y1 p1)
                         {!ntype x1 y1 p1!}
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
  center x1 y1 p1 .(inm x1 y1 p1) id = [ (Pushout.inl (x1 , (y1 , (x1 , (p1 , p1))))) , 
                                         (ap (λ z → x1 , y1 , p1 , x1 , y1 , p1 , z) (!-inv-l (gluer x1 y1 p1))) ] 
                                         -- [ inm (id , ! (∘-assoc (! (gluel x1 y1 p1)) id (gluel x1 y1 p1)) ∘ ! (!-inv-l (gluel x1 y1 p1)))
                                         --       (id , ! (∘-assoc (! (gluer x1 y1 p1)) id (gluer x1 y1 p1)) ∘ ! (!-inv-l (gluer x1 y1 p1)))
                                         --      (id , {!!}) ] -- need definition of Codesm

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
  theorem (x , y , p) = {!ntype (glue-map-connected x y p)!} -- 
