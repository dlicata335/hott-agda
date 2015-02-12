{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude hiding (Z)
open FatPushoutFib
open Truncation
open import lib.cubical.Cubical
import homotopy.blakersmassey.ooToposCodes

module homotopy.blakersmassey.ooTopos (X Y : Type) (P : X → Y → Type)
                                       (i' j' : TLevel)
                                       (cf : (x : X) → Connected (S i') (Σ \ y → P x y))
                                       (cg : (y : Y) → Connected (S j') (Σ \ x → P x y)) where 
  open homotopy.blakersmassey.ooToposCodes X Y P i' j' cf cg

  open CodesGlueMaps 

  module OverZ {x0 : X} {y0 : Y} (p0 : P x0 y0) where
    open Codes p0
    open OverZMaps p0

    -- make a section

    sectioncoh : Path { -×WZ}  (((x0 , y0) , p0) , ! (gluel p0) ∘ gluel p0) (((x0 , y0) , p0) , id)
    sectioncoh = (ap (\ Z → ((x0 , y0) , p0) , Z) (!-inv-l (gluel p0)))

    sectionZ : CodesFor (inm p0) id
    sectionZ = [ Wedge.inl (_ , p0) , sectioncoh ]

    section : (w : W) (p : inm p0 == w) → (CodesFor w p)
    section y p = transport CodesFor' (pair= p connOver) sectionZ


    -- show that it is also a retraction

    transport-CodesFor'-gluel : ∀ {x y} (pxy : P x y) {αl : _} {αm : _} (s : PathOver (λ v → Path (inm p0) v) (gluel pxy) αm αl) {a : _ }
                              → transport CodesFor' (pair= (gluel pxy) s) a == fst (glue-m-l pxy s) a
    transport-CodesFor'-gluel pxy s = ap≃(
                                       transport CodesFor' (pair= (gluel pxy) s) ≃〈 transport-ap-assoc CodesFor' (pair= (gluel pxy) s) 〉 
                                       coe (ap CodesFor' (pair= (gluel pxy) s)) ≃〈 ap coe (ap-uncurryd-NDrange CodesFor _ _) 〉 
                                       coe (coe PathOverΠ-NDrange (apdo CodesFor (gluel pxy)) _ _ s) ≃〈 ap (λ Z → coe (coe PathOverΠ-NDrange Z _ _ s)) (Pushout-elim/βgluel _ _ _ _ (λ x y pxy₁ → coe (! PathOverΠ-NDrange) (λ αm αl d → ua (glue-m-l pxy₁ d))) (λ x y pxy₁ → coe (! PathOverΠ-NDrange) (λ αm αl d → ua (glue-m-r pxy₁ d))) _ _ _) 〉 
                                       coe (coe PathOverΠ-NDrange (coe (! PathOverΠ-NDrange)
                                             (λ αx αy s → ua (glue-m-l pxy s))) _ _ s) ≃〈 ap (λ z → coe (z _ _ s)) (IsEquiv.β (snd (coe-equiv PathOverΠ-NDrange)) _) 〉 
                                       coe (ua (glue-m-l pxy s)) ≃〈 type≃β (glue-m-l pxy s) 〉 
                                       fst (glue-m-l pxy s) ∎)

    transport-CodesFor'-gluer : ∀ {x y} (pxy : P x y) {αr : _} {αm : _} (s : PathOver (λ v → Path (inm p0) v) (gluer pxy) αm αr) {a : _ }
                              → transport CodesFor' (pair= (gluer pxy) s) a == fst (glue-m-r pxy s) a 
    transport-CodesFor'-gluer pxy s = ap≃(   transport CodesFor' (pair= (gluer pxy) s) ≃〈 transport-ap-assoc CodesFor' (pair= (gluer pxy) s) 〉 
                                       coe (ap CodesFor' (pair= (gluer pxy) s)) ≃〈 ap coe (ap-uncurryd-NDrange CodesFor _ _) 〉 
                                       coe (coe PathOverΠ-NDrange (apdo CodesFor (gluer pxy)) _ _ s) ≃〈 ap (λ Z → coe (coe PathOverΠ-NDrange Z _ _ s)) (Pushout-elim/βgluer _ _ _ _ (λ x y pxy → coe (! PathOverΠ-NDrange) (λ αm αl d → ua (glue-m-l pxy d ))) (λ x y pxy → coe (! PathOverΠ-NDrange) (λ αm αl d → ua (glue-m-r pxy d ))) _ _ _) 〉 
                                       coe (coe PathOverΠ-NDrange (coe (! PathOverΠ-NDrange)
                                             (λ αx αy s → ua (glue-m-r pxy s))) _ _ s) ≃〈 ap (λ z → coe (z _ _ s)) (IsEquiv.β (snd (coe-equiv PathOverΠ-NDrange)) _) 〉 
                                       coe (ua (glue-m-r pxy s)) ≃〈 type≃β (glue-m-r pxy s) 〉 
                                       fst (glue-m-r pxy s) ∎)

    -- follows from the above if we move the transport to the other side
    transport-CodesFor'-!gluel : ∀ {x y} (pxy : P x y) {αl : _} {αm : _} (s : PathOver (λ v → Path (inm p0) v) (! (gluel pxy)) αl αm) {a : _ }
                              → transport CodesFor' (pair= (! (gluel pxy)) s) a == snde (glue-m-l pxy (changeover _ (!-invol (gluel pxy)) (!o s))) a
    transport-CodesFor'-!gluel pxy s {a} = transport CodesFor' (pair= (! (gluel pxy)) s) a ≃〈 ap (\ s → transport CodesFor' (pair= (! (gluel pxy)) s) a) (!o-invol/start-over-! s) 〉 
                                           transport CodesFor' (pair= (! (gluel pxy)) (!o (changeover _ (!-invol (gluel pxy)) (!o s)))) a ≃〈 ap (λ p → transport CodesFor' p a) (! (!Σ (gluel pxy) (changeover _ (!-invol (gluel pxy)) (!o s)))) 〉 
                                           transport CodesFor' (! (pair= (gluel pxy) (changeover _ (!-invol (gluel pxy)) (!o s)))) a 
                                           ≃〈 coe (! (move-transport-right-!≃ CodesFor' (pair= (gluel pxy) (changeover _ (!-invol (gluel pxy)) (!o s))))) 
                                                  (! (IsEquiv.β (snd (glue-m-l pxy (changeover (Path (inm p0)) (!-invol (gluel pxy)) (!o s)))) _ ∘
                                                    transport-CodesFor'-gluel pxy (changeover (Path (inm p0)) (!-invol (gluel pxy)) (!o s)) {snde (glue-m-l pxy (changeover (Path (inm p0)) (!-invol (gluel pxy)) (!o s))) a})) 〉 
                                           _ ∎

    retraction-r : (y : Y) (p : Path{W} (inm p0) (inr y)) (c : CodesFor (inr y) p) → Path (section (inr y) p) c
    retraction-r y p = Trunc-elim _ (λ _ → path-preserves-level Trunc-level) 
                                    (λ hf → path-induction (λ p₁ sndhf → Path (section (inr y) p₁) [ fst hf , sndhf ])
                                                            ((chase4 {i = transport CodesFor' (ap (λ x → inr y , x) (∘-assoc (gluer (fst hf)) (! (gluel (fst hf))) (gluel p0)))}
                                                                     {transport CodesFor' (pair= (gluer (fst hf)) (PathOverPathFrom.in-PathOver-= ∘-square))}
                                                                     {transport CodesFor' (pair= (! (gluel (fst hf))) (PathOverPathFrom.in-PathOver-= ∘-square))}
                                                                     {transport CodesFor' (pair= (gluel p0) (PathOverPathFrom.in-PathOver-= connection))} 
                                                                (step4 (fst hf)) (step3 (fst hf)) (step2 (fst hf)) step1 ∘
                                                              ap≃ (transport-∘4 CodesFor' (ap (λ x → inr y , x) (∘-assoc (gluer (fst hf)) (! (gluel (fst hf))) (gluel p0))) (pair= (gluer (fst hf)) (PathOverPathFrom.in-PathOver-= ∘-square)) (pair= (! (gluel (fst hf))) (PathOverPathFrom.in-PathOver-= ∘-square)) (pair= (gluel p0) (PathOverPathFrom.in-PathOver-= connection)))
                                                              ∘ ap (λ X₁ → transport CodesFor' X₁ sectionZ) (factorcoh (gluel p0) (! (gluel (fst hf))) (gluer (fst hf)))))
                                                            (snd hf)) where


      -- could do this as a composition of lemmas, but it's easier to do it by path ind
      factorcoh : ∀ {A : Type} {a b c d : A} (p : a == b) (q : b == c) (r : c == d) → 
             Path{Path{Σ \ b → Path a b} _ _} (pair= ((r ∘ q) ∘ p) connOver)
                                               (ap (\ x → d , x) (∘-assoc r q p) ∘
                                                pair= r (PathOverPathFrom.in-PathOver-= ∘-square) ∘ 
                                                (pair= q (PathOverPathFrom.in-PathOver-= ∘-square)) ∘ 
                                                pair= p (PathOverPathFrom.in-PathOver-= ∘-square))
      factorcoh id id id = id

      step1coh : {A : Type} {a0 a1 a2 : A} (rp : a0 == a1) (lp : a0 == a2) → Path (! (rp ∘ ! lp) ∘ rp) lp
      step1coh id id = id

      step1 : transport CodesFor' (pair= (gluel p0) connOver) sectionZ == [ p0 ,  step1coh (gluer p0) (gluel p0) ] 
      step1 = _ ≃〈 transport-CodesFor'-gluel p0 connOver 〉 
              fst (glue-m-l p0 connOver) sectionZ  ≃〈 id 〉 
              snde (glue-l-ml p0 (square-to-disc (PathOverPathFrom.out-PathOver-= connOver))) (fst (glue-m-ml p0) sectionZ)  ≃〈 ap (snde (glue-l-ml p0 (square-to-disc (PathOverPathFrom.out-PathOver-= connOver)))) step1a 〉 
              snde (glue-l-ml p0 (square-to-disc (PathOverPathFrom.out-PathOver-= connOver))) [ p0 , !-inv-l (gluel p0) ∘ m-to-ml-triangle-coh1 (gluel p0) (gluel p0) (gluer p0) ] ≃〈 ap (λ x → [ p0 , x ]) (step1b (gluel p0) (gluer p0)) 〉 
              [ p0 , _ ] ∎ where

        step1a : fst (glue-m-ml p0) sectionZ == [ p0 , !-inv-l (gluel p0) ∘ m-to-ml-triangle-coh1 (gluel p0) (gluel p0) (gluer p0) ]
        step1a = -- the first two steps of glue-m-ml reduce well definitionally
                 -- then transpose the problem and then reduce
                 ap [_] (! (fst (equiv-adjunction (glue-ml-ml-total p0)) transposed)) where
            transposed : Path
                           (((_ , p0) , (_ , p0) , p0) ,
                            ap (λ Z₁ → (_ , p0) , Z₁) (ap (λ Z₁ → (_ , p0) , Z₁) (!-inv-l (gluel p0) ∘ m-to-ml-triangle-coh1 (gluel p0) (gluel p0) (gluer p0))))
                           (((_ , p0) , (_ , p0) , p0) ,
                              ap (λ Z₁ → (_ , p0) , Z₁) (ap (λ Z₁ → (_ , p0) , Z₁) (!-inv-l (gluel p0))) ∘
                             ap (λ Q → (_ , p0) , (_ , p0) , Q) (m-to-ml-triangle-coh1 (gluel p0) (gluel p0) (gluer p0)))
            transposed = ap (λ Z₁ → ((_ , p0) , (_ , p0) , p0) , Z₁) 
                         (  ap (λ x → x ∘ ap (λ Q → (_ , p0) , (_ , p0) , Q) (m-to-ml-triangle-coh1 (gluel p0) (gluel p0) (gluer p0))) (ap-o (λ Z₁ → (_ , p0) , Z₁) (λ Z₁ → (_ , p0) , Z₁) (!-inv-l (gluel p0)))
                          ∘ ap-∘ (λ x → (_ , p0) , (_ , p0) , x) (!-inv-l (gluel p0)) (m-to-ml-triangle-coh1 (gluel p0) (gluel p0) (gluer p0))
                          ∘ ! (ap-o (λ Z₁ → (_ , p0) , Z₁) (λ Z₁ → (_ , p0) , Z₁) (!-inv-l (gluel p0) ∘ m-to-ml-triangle-coh1 (gluel p0) (gluel p0) (gluer p0))))

        step1b : {A : Type} {a0 a1 a2 : A} (l : a0 == a1) (r : a0 == a2) → Path (! (! (square-to-disc (PathOverPathFrom.out-PathOver-= (PathOverPathFrom.in-PathOver-= connection)))) ∘ ap (_∘_ (l)) (!-inv-l (l) ∘ m-to-ml-triangle-coh1 (l) (l) (r)) ∘ ! (!-inv-r-front (l) (! (r ∘ ! (l)) ∘ r) ∘ ap (_∘_ (l)) (!-inv-l-front (l) (! (l) ∘ ! (r ∘ ! (l)) ∘ r)) ∘ ap (λ x → l ∘ ! (l) ∘ x) (! (!-inv-r-front (l) (! (r ∘ ! (l)) ∘ r))))) (step1coh (r) (l)) 
        step1b id id = id

      -- reduce the transport, then move things to the other side, and then do something like step 1.
      -- ENH should be able to avoid the duplication with step 1, but I couldn't figure out the common superstatement of which they are both instances;
      -- would need to generalize the path stuff
      step2 : ∀ {y} (px0y : P x0 y) → transport CodesFor' (pair= (! (gluel px0y)) (PathOverPathFrom.in-PathOver-= ∘-square)) [ p0 , step1coh (gluer p0) (gluel p0) ]  == [ Wedge.inl (_ , px0y) , id ]
      step2 px0y = ! (fst (equiv-adjunction (glue-m-l px0y (changeover (Path (inm p0)) (!-invol (gluel px0y)) (!o (PathOverPathFrom.in-PathOver-= ∘-square)))) {a = [ Wedge.inl (_ , px0y) , id ]} {b = [ p0 , step1coh (gluer p0) (gluel p0) ]}) transposed)
                   ∘ transport-CodesFor'-!gluel px0y (PathOverPathFrom.in-PathOver-= ∘-square) {a = [ p0 , step1coh (gluer p0) (gluel p0) ]} where
            transposed : fst (glue-m-l px0y (changeover (Path (inm p0)) (!-invol (gluel px0y)) (!o (PathOverPathFrom.in-PathOver-= ∘-square)))) [ Wedge.inl (_ , px0y) , id ] == [ p0 , step1coh (gluer p0) (gluel p0) ]
            transposed = ap (λ x → [ p0 , x ]) (step2b (gluel px0y) (gluel p0) (gluer p0)) ∘
                         ap (snde (glue-l-ml px0y (square-to-disc (PathOverPathFrom.out-PathOver-= (changeover (Path (inm p0)) (!-invol (gluel px0y)) (!o (PathOverPathFrom.in-PathOver-= ∘-square))))))) step2a  where
              --reduce and then transpose and reduce
              step2a : fst (glue-m-ml px0y) [ Wedge.inl (_ , px0y) , id ] == [ p0 , m-to-ml-triangle-coh1 (gluel px0y) (gluel p0) (gluer p0) ]
              step2a = ap [_] (! (fst (equiv-adjunction (glue-ml-ml-total px0y)) 
                          (ap (λ h → ((_ , p0) , (_ , px0y) , p0) , h)
                            (! (∘-unit-l (ap (λ Q → (_ , p0) , (_ , px0y) , Q) (m-to-ml-triangle-coh1 (gluel px0y) (gluel p0) (gluer p0))))
                             ∘ ! (ap-o (λ Z₁ → ((x0 , y0) , p0) , Z₁) (λ Z₁ → (_ , px0y) , Z₁) (m-to-ml-triangle-coh1 (gluel px0y) (gluel p0) (gluer p0)))))))
              step2b : {A : Type} {a0 a1 a2 a3 : A} (lx0y : a0 == a1) (l0 : a2 == a1) (r0 : a2 == a3) → Path (! (! (square-to-disc (PathOverPathFrom.out-PathOver-= (transport (λ x → x) (changeover= (Path _) (!-invol (lx0y))) (!o (PathOverPathFrom.in-PathOver-=' ∘-square)))))) ∘ ap (_∘_ (lx0y)) (m-to-ml-triangle-coh1 (lx0y) (l0) (r0)) ∘ ! (!-inv-r-front (lx0y) (! (r0 ∘ ! (l0)) ∘ r0) ∘ ap (_∘_ (lx0y)) (!-inv-l-front (lx0y) (! (lx0y) ∘ ! (r0 ∘ ! (l0)) ∘ r0)) ∘ ap (λ x → lx0y ∘ ! (lx0y) ∘ x) (! (!-inv-r-front (lx0y) (! (r0 ∘ ! (l0)) ∘ r0))))) (step1coh (r0) (l0))
              step2b id id id = id
            
      step3 : ∀ {y} (px0y : P x0 y) → transport CodesFor' (pair= (gluer px0y) (PathOverPathFrom.in-PathOver-= ∘-square)) ([ Wedge.inl (_ , px0y) , id ]) == [ px0y , ! (∘-assoc (gluer px0y) (! (gluel px0y)) (gluel p0)) ] 
      step3 px0y = transport CodesFor' (pair= (gluer px0y) (PathOverPathFrom.in-PathOver-= ∘-square)) ([ Wedge.inl (_ , px0y) , id ]) ≃〈 transport-CodesFor'-gluer px0y {αr = gluer px0y ∘ ! (gluel px0y) ∘ gluel p0} {αm = ! (gluel px0y) ∘ gluel p0} (PathOverPathFrom.in-PathOver-= ∘-square)  〉 
                   fst (glue-m-r px0y (PathOverPathFrom.in-PathOver-= ∘-square)) ([ Wedge.inl (_ , px0y) , id ])  ≃〈 ap (\ h → snde (glue-r-mr px0y h) (fst (glue-m-mr px0y) ([ Wedge.inl (_ , px0y) , id ]))) (square-to-disc-∘-square (! (gluel px0y) ∘ gluel p0) (gluer px0y) ∘ ap square-to-disc (IsEquiv.β (snd PathOverPathFrom.PathOver-=-eqv) ∘-square)) 〉 
                   snde (glue-r-mr px0y id) (fst (glue-m-mr px0y) ([ Wedge.inl (_ , px0y) , id ]))  ≃〈 ap (snde (glue-r-mr px0y id)) step3a  〉 
                   snde (glue-r-mr px0y id) [ px0y , m-to-mr-triangle-coh1 (gluer px0y) (gluel px0y) (gluel p0) ]  ≃〈 ap (λ z → [ px0y , z ]) (step3b (gluer px0y) (gluel px0y) (gluel p0)) 〉 
                   [ px0y , ! (∘-assoc (gluer px0y) (! (gluel px0y)) (gluel p0)) ]  ∎ where

        step3a : fst (glue-m-mr px0y) [ Wedge.inl (_ , px0y) , id ]  == [ px0y , m-to-mr-triangle-coh1 (gluer px0y) (gluel px0y) (gluel p0) ] 
        step3a = ap [_] (! (fst (equiv-adjunction (glue-mr-mr-total px0y)) transposed)) where
          transposed = ap (λ h → ((_ , p0) , (_ , px0y) , px0y) , h) 
                          (! (∘-unit-l (ap (λ Q → (_ , p0) , (_ , px0y) , Q) (m-to-mr-triangle-coh1 (gluer px0y) (gluel px0y) (gluel p0))))
                           ∘ ! (ap-o (λ Z₁ → ((x0 , y0) , p0) , Z₁) (λ Z₁ → (_ , px0y) , Z₁) (m-to-mr-triangle-coh1 (gluer px0y) (gluel px0y) (gluel p0))))

        step3b : ∀ {A} {a0 a1 a2 a3 : A} (rx0y : a0 == a1) (lx0y : a0 == a2) (lp0 : a3 == a2) → Id (id ∘ ap (_∘_ rx0y) (m-to-mr-triangle-coh1 rx0y lx0y lp0) ∘ ! (!-inv-r-front rx0y ((rx0y ∘ ! lx0y) ∘ lp0) ∘ ap (_∘_ rx0y) (!-inv-l-front rx0y (! rx0y ∘ (rx0y ∘ ! lx0y) ∘ lp0)) ∘ ap (λ x → rx0y ∘ ! rx0y ∘ x) (! (!-inv-r-front rx0y ((rx0y ∘ ! lx0y) ∘ lp0))))) (! (∘-assoc rx0y (! lx0y) lp0))
        step3b id id id = id 

      step4 : ∀ {y} (px0y : P x0 y) → 
          transport CodesFor' (ap (\ x → _ , x) (∘-assoc (gluer px0y) (! (gluel px0y)) (gluel p0)))
                              [ px0y , ! (∘-assoc (gluer px0y) (! (gluel px0y)) (gluel p0)) ] == [ px0y , id ]
      step4 px0y = (ap [_] (ap (λ x → px0y , x) (!-inv-r (∘-assoc (gluer px0y) (! (gluel px0y)) (gluel p0))) 
                                ∘ ap≃ (transport-HFiber-arg gluer0 (∘-assoc (gluer px0y) (! (gluel px0y)) (gluel p0)))) ∘
                   ap≃ (transport-Trunc (λ x → HFiber gluer0 x) (∘-assoc (gluer px0y) (! (gluel px0y)) (gluel p0))) {_}) ∘
                   ! (ap≃ (transport-ap-assoc' CodesFor' (λ x → _ , x) (∘-assoc (gluer px0y) (! (gluel px0y)) (gluel p0))))

    -- so we need a section and a retraction
    contr-r : (y : Y) (p : Path{W} (inm p0) (inr y)) → Contractible (CodesFor (inr y) p)
    contr-r y p = section (inr y) p , retraction-r y p

    module Unused where
      -- note: it's not used below but he fact that codes is contractible in general follows
      -- from doing it for inr
      contr : (w : W) (p : Path{W} (inm p0) w) → Contractible (CodesFor w p)
      contr w p = transport (\ (wp : (Σ \ (w : W) → Path (inm p0) w)) → Contractible (CodesFor (fst wp) (snd wp))) 
                            (HProp-unique (raise-level (-2<= -1) singleton-contractible) (inr y0 , gluer p0) (w , p))
                            (contr-r y0 (gluer p0))

    -- Step D: what we want is a special case of codes being contractible
    gluer0-connected : (y : Y) → ConnectedMap i+j (gluer0 {y})
    gluer0-connected y = λ α → ntype (contr-r y α)

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
  -- Z -> X is (S _)-connected, so to make an hprop for X, we can do it for the X part of a Z
  glue-connected : (x0 : X) (y : Y) → ConnectedMap i+j (glue{x = x0}{y})
  glue-connected x0 y = Trunc-rec (raise-HProp (Πlevel (\ _ → (NType-is-HProp _)))) (λ yp0 → OverZ.glue-connected' (snd yp0) y)
                                  (fst (use-level (cf x0)))

  -- Working backwards, Step A: work in the slice over X × Y

  glue-map-total : (Σ \ xy → P (fst xy) (snd xy)) → Σ \ xy → Path{W} (inl (fst xy)) (inr (snd xy))
  glue-map-total ((x , y) , p) = ((x , y) , glue p)

  theorem : ConnectedMap i+j glue-map-total
  theorem = ConnectedMap.fiberwise-to-total-connected i+j (λ _ → glue) (λ xy → glue-connected (fst xy) (snd xy))

