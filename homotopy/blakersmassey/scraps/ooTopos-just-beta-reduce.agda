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

  module OverZ {x0 : X} {y0 : Y} (p0 : P x0 y0) where
    open OverZ0 p0
    
    open CodesGlueMaps

    -- construct the section

{-
    -- first construct the section for Z 
    -- FIXME: not sure why we're going in via Z×XZ×YZ; could do the symmetric one, or just write it directly as
    sectionZ' : Trunc i+j (HFiber (gluemr p0 p0) id) 
    sectionZ' = [ p0 , coh (gluer p0) (gluel p0) ] where
      coh : ∀ {A} {a0 a1 a2 : A} (r : a0 == a1) (l : a0 == a2) → (! r ∘ (r ∘ ! l) ∘ l) == id
      coh id id = id

    sectionZ : CodesFor (inm p0) id
    sectionZ = IsEquiv.g (snd (glue-mr-m p0)) sectionZ'
-}
    sectionZcoh : Path {Σ \ (z : Z) → Path{W} (inm p0) (inm (snd z))} (((x0 , y0) , p0) , ! (gluel p0) ∘ gluel p0) (((x0 , y0) , p0) , id)
    sectionZcoh = ap (λ p → ((x0 , y0) , p0) , p) (!-inv-l (gluel p0))

    sectionZ : CodesFor (inm p0) id
    sectionZ = [ Wedge.inl (_ , p0) ,  sectionZcoh ]

    -- use of path induction is hiding in a silent use of Z = Z ×W W
    encode : (w : W) (p : inm p0 == w) → (CodesFor w p)
    encode x p = transport CodesFor' (pair= p connOver) sectionZ

{-
    transport-CodesFor'-glue : ∀ {x y} (pxy : P x y) {αx  : Path{W} (inl x0) (inl x)} {αy  : Path (inl x0) (inr y)} (s : PathOver (Path (inl x0)) (glue pxy) αx αy)
                               → transport CodesFor' (pair= (glue pxy) s) == Codes-glue.map p0 pxy (PathOverPathFrom.out-PathOver-= s) 
    transport-CodesFor'-glue pxy s = transport CodesFor' (pair= (glue pxy) s) ≃〈 transport-ap-assoc CodesFor' (pair= (glue pxy) s) 〉 
                                     coe (ap CodesFor' (pair= (glue pxy) s)) ≃〈 ap coe (ap-uncurryd-NDrange CodesFor _ _) 〉 
                                     coe (coe PathOverΠ-NDrange (apdo CodesFor (glue pxy)) _ _ s) ≃〈 ap (λ Z → coe (coe PathOverΠ-NDrange Z _ _ s)) (Pushout-elim/βglue _ _ _ (λ x y pxy₁ → coe (! PathOverΠ-NDrange) (λ αx αy s₁ → ua (Codes-glue.eqv p0 pxy₁ (PathOverPathFrom.out-PathOver-= s₁)))) _ _ _) 〉 
                                     coe (coe PathOverΠ-NDrange (coe (! PathOverΠ-NDrange)
                                           (λ αx αy s → ua (Codes-glue.eqv p0 pxy (PathOverPathFrom.out-PathOver-= s)))) _ _ s) ≃〈 ap (λ z → coe (z _ _ s)) (IsEquiv.β (snd (coe-equiv PathOverΠ-NDrange)) _) 〉 
                                     coe (ua (Codes-glue.eqv p0 pxy (PathOverPathFrom.out-PathOver-= s))) ≃〈 type≃β (Codes-glue.eqv p0 pxy (PathOverPathFrom.out-PathOver-= s)) 〉 
                                     Codes-glue.map p0 pxy (PathOverPathFrom.out-PathOver-= s) ∎
-}
{-
    redrm : {y : Y} (px0y : P x0 y) → Path{Trunc i+j (HFiber (gluemr p0 px0y) (! (gluel px0y) ∘ gluel p0) )} 
      (IsEquiv.g
       (snd
        (!equiv
         (glue-r-mr px0y
          (∘-assoc (gluer px0y) (! (gluel px0y)) (gluel p0)))))
       (encode (inr y) (glue px0y ∘ gluel p0)))
      (IsEquiv.g
       (snd
        (!equiv
         (glue-r-mr px0y
          (∘-assoc (gluer px0y) (! (gluel px0y)) (gluel p0)))))
       [ px0y , id ])
    redrm px0y = ! red1 ∘ {!!} where
      red1 : (IsEquiv.g (snd (!equiv (glue-r-mr px0y (∘-assoc (gluer px0y) (! (gluel px0y)) (gluel p0))))) [ px0y , id ]) == [ px0y , {!!} ]
      red1 = {![ ? ] ≃〈 ? 〉 _ ∎ !}
-}
    red1-coh : ∀ {A} {a0 a1 a2 : A} (rp : a0 == a1) (lp : a0 == a2) → (! (rp ∘ ! lp) ∘ rp) == lp
    red1-coh id id = id

    red1 : {y : Y} (px0y : P x0 y) → transport CodesFor' (pair= (gluel p0) connOver) sectionZ == [ p0 , red1-coh (gluer p0) (gluel p0) ]
    red1 px0y = {!!} where
      red3 : fst (apTrunc' (glue-m-m-total p0)) sectionZ == [ ((_ , p0) , (Wedge.inl (_ , p0))) , pair= id (hom-to-over sectionZcoh) ]
      red3 = id

      red4 : fst (glue-ml-m-total p0) [ ((_ , p0) , (Wedge.inl (_ , p0))) , pair= id (hom-to-over sectionZcoh) ] == [ ((_ , p0) , (_ , p0) , p0) , ap (λ Z₁ → (_ , p0) , (_ , p0) , Z₁) (!-inv-l (gluel p0) ∘ m-to-ml-triangle-coh1 (gluel p0) (gluel p0) (gluer p0)) ] -- just guessing
      red4 = {!!}

      red5 : fst (apTrunc' (!equiv (glue-ml-ml-total p0))) [ ((_ , p0) , (_ , p0) , p0) , ap (λ Z₁ → (_ , p0) , (_ , p0) , Z₁) (!-inv-l (gluel p0) ∘ m-to-ml-triangle-coh1 (gluel p0) (gluel p0) (gluer p0)) ] == [ p0 , (!-inv-l (gluel p0) ∘ m-to-ml-triangle-coh1 (gluel p0) (gluel p0) (gluer p0)) ]
      red5 = {!id!}

      red2 : fst (glue-ml-m p0) sectionZ == [ p0 , {!!} ]
      red2 = fst (glue-ml-m p0) sectionZ ≃〈 id 〉 
             fst (glue-ml-m p0) sectionZ ≃〈 {!!} 〉 
             _ ∎

      red1' : fst (!equiv (glue-l-ml p0 (square-to-disc (PathOverPathFrom.out-PathOver-= connOver))) ∘equiv glue-ml-m p0) sectionZ == [ p0 , red1-coh (gluer p0) (gluel p0) ] 
      red1' = {!!}
      

    redr : {y : Y} (px0y : P x0 y) → Path{Trunc i+j (HFiber (gluer0 p0) (glue px0y ∘ gluel p0))} (encode (inr y) (glue px0y ∘ gluel p0)) [ px0y , id ]
    redr {y} px0y = {!!}
      -- move-path-along-equiv/general-conclusion
      --             (!equiv (glue-r-mr px0y {αm = ! (gluel px0y) ∘ gluel p0} {αr = glue px0y ∘ gluel p0} (∘-assoc (gluer px0y) (! (gluel px0y)) (gluel p0)))) (redrm {y} px0y)
{-
    redr px0y = transport CodesFor' (pair= (glue px0y) connOver) forid ≃〈 ap≃ (transport-CodesFor'-glue px0y connOver) 〉 
                Codes-glue.map p0 px0y (PathOverPathFrom.out-PathOver-= connOver) [ p0 , !-inv-l (glue p0) ]  ≃〈 id 〉 
                Trunc-rec Trunc-level (λ c → [ fst c , square-to-disc (PathOverPathFrom.out-PathOver-= connOver) ∘
                                                         ap (_∘_ (glue px0y)) (!-inv-l (glue p0)) ∘
                                                         square-to-disc-rearrange (square-symmetry (snd c)) ]) (composeP px0y p0 p0 ) ≃〈 ap (Trunc-rec Trunc-level (λ c → [ fst c , _ ])) (composePβ2 _ _) 〉 
                [ px0y , square-to-disc (PathOverPathFrom.out-PathOver-= connOver) ∘ ap (_∘_ (glue px0y)) (!-inv-l (glue p0)) ∘ square-to-disc-rearrange (square-symmetry (inverses-square (glue p0) (glue px0y))) ] ≃〈 ap (λ z → [ px0y , z ]) (coh (glue p0) (glue px0y)) 〉 
                [ px0y , id ] ∎ where
         coh : ∀ {A : Type} {a0 a1 a1' : A} (α : a0 == a1) (α' : a0 == a1')
               → square-to-disc (PathOverPathFrom.out-PathOver-= connOver) ∘ 
                  ap (_∘_ α') (!-inv-l α) ∘ 
                  square-to-disc-rearrange (square-symmetry (inverses-square α α')) == id
         coh id id = id
-}

    -- really only need it for inr
    encode-decode-inr : (y : Y) (p : inm p0 == inr y) (c : HFiber (gluer0 p0) p) → Path (encode (inr y) p) [ c ]
    encode-decode-inr y ._ (px0y , id) = redr px0y

    contr-r : (y : Y) (p : Path{W} (inm p0) (inr y)) → Contractible (CodesFor (inr y) p)
    contr-r y p = encode (inr y) p , Trunc-elim _ (λ _ → path-preserves-level Trunc-level) (encode-decode-inr y p)

    -- this is the same goal as the end of Step 1.2.1.1
    gluer0-connected : (y : Y) → ConnectedMap i+j (gluer0 p0 {y})
    gluer0-connected y = λ α → ntype (contr-r y α)

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

