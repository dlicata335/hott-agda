{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open Paths
open import canonicity-prop.Reducibility
open import canonicity-prop.Contexts

module canonicity-prop.Univ where

  module Univ where 

    private 
      data U' : Set 

    El : U' -> Set

    data U' where
        nat' : U'
        sigma'  : (a : U') -> (El a -> U') -> U'

    El nat' = Nat
    El (sigma' a b) = Σ \(x : El a) -> El (b x)

    U = U'

    nat : U
    nat = nat'
    
    sigma  : (a : U') -> (El a -> U') -> U'
    sigma = sigma'

  -- use abstract type so there is no intentional analysis besides El
  open Univ public

  head-expand-CTy-El : ∀ {a b : U} 
                     -> (ra : CTy (El a))
                     -> (E : b ≃ a)
                     -> (ev : Eval E)
                     -> CTy (El b)
  head-expand-CTy-El ra E ev = record {
                                 Red = λ x → Red ra (subst El E x);
                                 propr = propr ra;
                                 Red≃ = λ rM rN α → Red≃ ra rM rN (resp (subst El E) α);
                                 propr≃ = propr≃ ra;
                                 head-expand = λ rN E' ev' → head-expand ra rN (resp (subst El E) E') FIXMEEval;
                                 head-expand≃ = λ rα E' ev' → head-expand≃ ra rα (resp (resp (subst El E)) E') FIXMEEval;
                                 rRefl = rRefl ra;
                                 r! = λ {M}{N}{α} rα → head-expand≃ ra (r! ra rα) (resp-! (subst El E) α) FIXMEEval;
                                 r∘ = {!!};
                                 eval-red≃ = λ α rα → eval-red≃ ra (resp (subst El E) α) FIXMEEval }

  mutual
    record UTy {Γ : Set} (rΓ : CTy Γ) (A : Γ -> U) : Set where
      constructor ty 
      field
        ured  : {θ : Γ} -> (rθ : Red rΓ θ) -> RedU (A θ)
        uresp : {θ1 θ2 : Γ} {α : θ1 ≃ θ2}
                 {rθ1 : Red rΓ θ1} {rθ2 : Red rΓ θ2}
                 (rα  : Red≃ rΓ rθ1 rθ2 α)
              -> Red≃U (ured rθ1) (ured rθ2) (resp A α)
  
    -- FIXME need to squash the derivations
    data RedU (a : U) : Set where
      rnat : (α : a ≃ nat) -> Eval α -> RedU a
      rsigma  : ∀ {a1 a2} -> (α : a ≃ sigma a1 a2) -> Eval α 
           -> (ra1 : RedU a1)
           -> UTy (sEl0 ra1) a2
           -> RedU a

    Red≃U : ∀ {a b} -> RedU a -> RedU b -> (α : Id a b) -> Set
    Red≃U ra rb α = Map (sEl0 ra) (sEl0 rb) (subst El α)
                  × Map (sEl0 rb) (sEl0 ra) (subst El (! α))

    sEl0 : {a : U} -> RedU a -> CTy (El a)     -- FIXME: going to need coherence for the squash elim
    sEl0  (rnat E ev) = 
          head-expand-CTy-El {!!} E ev
    sEl0  (rsigma  {a1}{a2} E ev ra1 ra2) = 
          head-expand-CTy-El 
            (Σc (sEl0 ra1)
                (ty (λ rθ → sEl0 (UTy.ured ra2 rθ)) 
                    (λ {θ1}{θ2}{α}{rθ1}{rθ2} rα → head-expand-map
                                                    (sEl1 (resp a2 α) (UTy.ured ra2 rθ1) (UTy.ured ra2 rθ2)
                                                     (UTy.uresp ra2 rα))
                                                    (subst-o El a2 α) FIXMEEval)))
            E ev

    sEl1 : {a b : U} (α : Id a b)
           (ra : RedU a) (rb : RedU b) →
           Red≃U ra rb α → Map (sEl0 ra) (sEl0 rb) (subst El α)
    sEl1 = λ α ra rb x → (fst x)

  head-expand-U : {a b : U} -> RedU b -> (E : a ≃ b) -> Eval E -> RedU a
  head-expand-U (rnat E1 ev1) E ev = rnat (E1 ∘ E) FIXMEEval
  head-expand-U (rsigma E1 ev1 ra1 ra2) E ev = rsigma (E1 ∘ E) FIXMEEval ra1 ra2

  cU : CTy U
  cU = record {
           Red = RedU;
           propr = FIXMETodo; -- not true yet--need squashing
           Red≃ = Red≃U;
           propr≃ = FIXMETodo;
           head-expand  = head-expand-U;
           head-expand≃ = λ p E ev → (head-expand-map (fst p) (resp (subst El) E) FIXMEEval) , 
                                     head-expand-map (snd p) (resp (λ x → subst El (! x)) E) FIXMEEval;
           rRefl = λ rM → mid (sEl0 rM) , mid (sEl0 rM);
           r! = λ {a}{b}{α} rα → snd rα , head-expand-map (fst rα) (resp (subst El) (!-invol α)) FIXMEEval;
           r∘ = λ {P}{M}{N}{β}{α}{rP}{rN}{rM} rβ rα → head-expand-map
                                                        (mo (sEl0 rM) (sEl0 rN) (sEl0 rP) (subst El α) (subst El β)
                                                         (fst rβ) (fst rα))
                                                        (subst-∘ El α β) FIXMEEval , 
                                                     head-expand-map
                                                       (mo (sEl0 rP) (sEl0 rN) (sEl0 rM) (subst El (! β)) (subst El (! α))
                                                        (snd rα) (snd rβ))
                                                       FIXMEChecked FIXMEEval;
           eval-red≃ = {!!} } -- hard

  sEl : Ty cU El
  sEl = ty sEl0 (λ {a}{b}{α}{ra}{rb} rα → sEl1 α ra rb rα)

  uty-map : {Γ : Set} {rΓ : CTy Γ} {A : Γ -> U} -> UTy rΓ A -> Map rΓ cU A
  uty-map uA = smap (UTy.ured uA) (UTy.uresp uA)

{-
  U = Set -- FIXME level issues

  data Value≃U {A B : Set} (vA : ValuableTy A) (vB : ValuableTy B) : Id A B -> Set where
    univ : ∀ {f : A -> B} 
             -> {isa : IsAEq f}
             -> Map vA vB f  -- FIXME need this for the rest, too
             -> Value≃U vA vB (ua (f , isa)) 

  cU : ValuableTy U -- lazy
  cU = valuablety U (record { Value = ValuableTy; 
                              Value≃ = Value≃U; 
                              vRefl = {!!}; v! = {!!}; v∘ = {!!} })
                      Refl FIXMEEval

  sU : ∀ {Γ} {vΓ : ValuableTy Γ} -> Ty vΓ (\ _ -> U)
  sU {vΓ} = ty (λ _ → cU) (λ vα → smap (λ x → valuable _ x {!!} FIXMEEval) 
                                     (λ vα' → valuable≃ _ vα' {!!} FIXMEEval))

  sEl : ∀ {Γ} (vΓ : ValuableTy Γ) -> Ty (Σc vΓ sU) snd
  sEl = λ vΓ → ty (λ { {x , A} (cpair vx vA) → head-expand-ty (val vA) (ev vA ∘ {!!}) FIXMEEval })
                  (λ { {._} (cpair≃ vα (valuable≃ ._ (univ sf) eβ _)) → 
          smap (λ vA → valuable _ (val (mred sf vA)) (ev (mred sf vA) ∘ FIXMETodo) FIXMEEval) -- OK modulo adjustments
               (λ { {_}{_}{_}{_}{_} vα' → valuable≃ _ (val≃ (mresp sf vα')) (ev≃ (mresp sf vα') ∘ {!!}) FIXMEEval}) } ) -- easy if you J α'
-}