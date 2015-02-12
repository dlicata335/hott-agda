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

    sectioncoh : Path { -×WZ}  (((x0 , y0) , p0) , ! (gluel p0) ∘ gluel p0) (((x0 , y0) , p0) , id)
    sectioncoh = (ap (\ Z → ((x0 , y0) , p0) , Z) (!-inv-l (gluel p0)))

    sectionZ : CodesFor (inm p0) id
    sectionZ = [ Wedge.inl (_ , p0) , sectioncoh ]

    section : (w : W) (p : inm p0 == w) → (CodesFor w p)
    section y p = transport CodesFor' (pair= p connOver) sectionZ

  module OverZ {x0 : X} {y0 : Y} (p0 : P x0 y0) where
    open Codes p0
    open Section p0
    open OverZMaps p0

    transport-CodesFor'-gluel : ∀ {y} (px0y : P x0 y) {αl : _} {αm : _} (p : PathOver (λ v → Path (inm p0) v) (gluel px0y) αm αl) {s : _ }
                              → transport CodesFor' (pair= (gluel px0y) p) s == fst (glue-m-l px0y p) s
    transport-CodesFor'-gluel = {!!}

    transport-CodesFor'-!gluel : ∀ {y} (px0y : P x0 y) {αl : _} {αm : _} (p : PathOver (λ v → Path (inm p0) v) (! (gluel px0y)) αl αm) {s : _ }
                              → transport CodesFor' (pair= (! (gluel px0y)) p) s == snde (glue-m-l px0y (changeover _ (!-invol (gluel px0y)) (!o p))) s
    transport-CodesFor'-!gluel = {!!}

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

      step3 : ∀ {y} (px0y : P x0 y) → transport CodesFor' (pair= (gluer px0y) (PathOverPathFrom.in-PathOver-= ∘-square)) [ Wedge.inl (_ , px0y) , id ] == [ px0y , ! (∘-assoc (gluer px0y) (! (gluel px0y)) (gluel p0)) ] 
      step3 = {!!}
{-
            _ ≃〈 transport-CodesFor'-gluel p0 connOver 〉 
              fst (glue-m-l p0 connOver) sectionZ  ≃〈 id 〉 
              snde (glue-l-ml p0 (square-to-disc (PathOverPathFrom.out-PathOver-= connOver))) (fst (glue-m-ml p0) sectionZ)  ≃〈 ap (snde (glue-l-ml p0 (square-to-disc (PathOverPathFrom.out-PathOver-= connOver)))) step3a 〉 
              snde (glue-l-ml p0 (square-to-disc (PathOverPathFrom.out-PathOver-= connOver))) [ p0 , !-inv-l (gluel p0) ∘ m-to-ml-triangle-coh1 (gluel p0) (gluel p0) (gluer p0) ] ≃〈 ap (λ x → [ p0 , x ]) (step3b (gluel p0) (gluer p0)) 〉 
              [ p0 , _ ] ∎ where
-}
{-
        step3a : fst (glue-m-ml p0) sectionZ == [ p0 , !-inv-l (gluel p0) ∘ m-to-ml-triangle-coh1 (gluel p0) (gluel p0) (gluer p0) ]
        step3a = -- the first two steps of glue-m-ml reduce well definitionally
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

        step3b : {A : Type} {a0 a1 a2 : A} (l : a0 == a1) (r : a0 == a2) → Path (! (! (square-to-disc (PathOverPathFrom.out-PathOver-= (PathOverPathFrom.in-PathOver-= connection)))) ∘ ap (_∘_ (l)) (!-inv-l (l) ∘ m-to-ml-triangle-coh1 (l) (l) (r)) ∘ ! (!-inv-r-front (l) (! (r ∘ ! (l)) ∘ r) ∘ ap (_∘_ (l)) (!-inv-l-front (l) (! (l) ∘ ! (r ∘ ! (l)) ∘ r)) ∘ ap (λ x → l ∘ ! (l) ∘ x) (! (!-inv-r-front (l) (! (r ∘ ! (l)) ∘ r))))) (step3coh (r) (l)) 
        step3b id id = id
-}

      step2 : ∀ {y} (px0y : P x0 y) → transport CodesFor' (pair= (! (gluel px0y)) (PathOverPathFrom.in-PathOver-= ∘-square)) [ p0 , step1coh (gluer p0) (gluel p0) ]  == [ Wedge.inl (_ , px0y) , id ]
      step2 px0y = {!!}
{-
transport CodesFor' (pair= (! (gluel px0y)) (PathOverPathFrom.in-PathOver-= ∘-square)) [ p0 , ! section-coh-path ] ≃〈 {!!} 〉
                   snde (glue-m-l px0y {αm = ! (gluel px0y) ∘ gluel p0} {αl = gluel p0} (PathOverPathFrom.in-PathOver-= sq)) [ p0 , ! section-coh-path ] ≃〈 ap (λ H → snde (glue-m-ml px0y) (fst (glue-l-ml px0y {αm = ! (gluel px0y) ∘ gluel p0} {αl = gluel p0} (square-to-disc H)) [ p0 , ! section-coh-path ])) (IsEquiv.β (snd PathOverPathFrom.PathOver-=-eqv) sq) 〉 -- once you reduce the transport and massage this is what you should get
                   snde (glue-m-ml px0y) (fst (glue-l-ml px0y {αm = ! (gluel px0y) ∘ gluel p0} {αl = (gluel p0)} (square-to-disc sq)) [ p0 , ! section-coh-path ]) ≃〈 (ap (snde (glue-m-ml px0y)) step2a) 〉  
                   snde (glue-m-ml px0y) [ p0 , m-to-ml-triangle-coh1 (gluel px0y) (gluel p0) (gluer p0) ] ≃〈 ! (fst (equiv-adjunction (glue-m-ml px0y)) step2b) 〉 --switch sides!
                   [ Wedge.inl (_ , px0y) , id ] ∎ where

            sq : Square (! (gluel px0y) ∘ gluel p0) id (gluel px0y) (gluel p0)
            sq = {!!} 
  
            step2a : (fst (glue-l-ml px0y {αm = ! (gluel px0y) ∘ gluel p0} {αl = (gluel p0)} (square-to-disc sq)) [ p0 , ! section-coh-path ]) == [ p0 , m-to-ml-triangle-coh1 (gluel px0y) (gluel p0) (gluer p0) ]
            step2a = ap (λ x → [ p0 , x ]) {!coh!}

            step2b : fst (glue-m-ml px0y) [ Wedge.inl (_ , px0y) , id ] ==  [ p0 , m-to-ml-triangle-coh1 (gluel px0y) (gluel p0) (gluer p0) ]
            step2b = fst (glue-m-ml px0y) [ Wedge.inl (_ , px0y) , id ] ≃〈 id 〉
                     fst (apTrunc' (!equiv (glue-ml-ml-total px0y)) ∘equiv (glue-m-ml-total px0y) ∘equiv apTrunc' (glue-m-m-total px0y)) [ Wedge.inl (_ , px0y) , id ] ≃〈 id 〉
                     fst (apTrunc' (!equiv (glue-ml-ml-total px0y)) ∘equiv (glue-m-ml-total px0y)) [ fst (glue-m-m-total px0y) (Wedge.inl (_ , px0y) , id) ] ≃〈 id 〉
                     Trunc-func (snde (glue-ml-ml-total px0y)) (fst (glue-m-ml-total px0y) [ (_ , Wedge.inl (_ , px0y)) , id ]) ≃〈 id 〉 
                     Trunc-func (snde (glue-ml-ml-total px0y)) [ m-to-ml (_ , Wedge.inl (_ , px0y)) , id ∘ ap (λ Q → (_ , p0) , (_ , px0y) , Q) (m-to-ml-triangle-coh1 (gluel px0y) (gluel p0) (gluer p0)) ] ≃〈 id 〉 
                     Trunc-func (snde (glue-ml-ml-total px0y)) [ ((_ , p0) , (_ , px0y) , p0) , id ∘ ap (λ Q → (_ , p0) , (_ , px0y) , Q) (m-to-ml-triangle-coh1 (gluel px0y) (gluel p0) (gluer p0)) ] ≃〈 id 〉                       
                     [ (fst (!equiv (glue-ml-ml-total px0y))) (((_ , p0) , (_ , px0y) , p0) , id ∘ ap (λ Q → (_ , p0) , (_ , px0y) , Q) (m-to-ml-triangle-coh1 (gluel px0y) (gluel p0) (gluer p0))) ] ≃〈 ap (λ H → [ fst (!equiv (glue-ml-ml-total px0y)) (((_ , p0) , (_ , px0y) , p0) , H)]) (∘-unit-l (ap (λ Q → (_ , p0) , (_ , px0y) , Q) (m-to-ml-triangle-coh1 (gluel px0y) (gluel p0) (gluer p0)))) 〉                       
                     [ (fst (!equiv (glue-ml-ml-total px0y))) (((_ , p0) , (_ , px0y) , p0) , ap (λ Q → (_ , p0) , (_ , px0y) , Q) (m-to-ml-triangle-coh1 (gluel px0y) (gluel p0) (gluer p0))) ] ≃〈 ap [_] (! (fst (equiv-adjunction (glue-ml-ml-total px0y)) (ap (λ h → ((_ , p0) , (_ , px0y) , p0) , h) (! (ap-o (λ Z₁ → (_ , p0) , Z₁) (λ Z₁ → (_ , px0y) , Z₁) (m-to-ml-triangle-coh1 (gluel px0y) (gluel p0) (gluer p0))))))) 〉 --switch sides!
                     _ ∎
-}

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
  -- Z -> X is (S _)-connected, so to make an hprop for X, we can do it for Z
  glue-connected : (x0 : X) (y : Y) → ConnectedMap i+j (glue{x = x0}{y})
  glue-connected x0 y = Trunc-rec (raise-HProp (Πlevel (\ _ → (NType-is-HProp _)))) (λ yp0 → OverZ.glue-connected' (snd yp0) y)
                                  (fst (use-level (cf x0)))

  -- Working backwards, Step A: work in the slice

  glue-map-total : (Σ \ xy → P (fst xy) (snd xy)) → Σ \ xy → Path{W} (inl (fst xy)) (inr (snd xy))
  glue-map-total ((x , y) , p) = ((x , y) , glue p)

  theorem : ConnectedMap i+j glue-map-total
  theorem = ConnectedMap.fiberwise-to-total-connected i+j (λ _ → glue) (λ xy → glue-connected (fst xy) (snd xy))


