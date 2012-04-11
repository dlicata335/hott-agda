{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open Paths
open import canonicity-prop.Reducibility


module canonicity-prop.Univ where

  module Univ where 

    private 
      data U' : Set 

    El : U' -> Set

    data U' where
        nat' : U'
        pi'  : (a : U') -> (El a -> U') -> U'

    El nat' = Nat
    El (pi' a b) = (x : El a) -> El (b x)

    U = U'

    nat : U
    nat = nat'
    
    pi  : (a : U') -> (El a -> U') -> U'
    pi = pi'

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
                                 head-expand≃ = {!!};
                                 rRefl = rRefl ra;
                                 r! = λ {M}{N}{α} rα → head-expand≃ ra (r! ra rα) (resp-! (subst El E) α) FIXMEEval;
                                 r∘ = {!!};
                                 eval-red≃ = λ α rα → eval-red≃ ra (resp (subst El E) α) FIXMEEval }

  mutual
    record UTy {Γ : Set} (rΓ : CTy Γ) (A : Γ -> U) : Set where
      constructor ty 
      field
        utred : {θ : Γ} -> (rθ : Red rΓ θ) -> RedU (A θ)
        uresp : {θ1 θ2 : Γ} {α : θ1 ≃ θ2}
                 {rθ1 : Red rΓ θ1} {rθ2 : Red rΓ θ2}
                 (rα  : Red≃ rΓ rθ1 rθ2 α)
              -> Red≃U (utred rθ1) (utred rθ2) (resp A α)
  
    -- FIXME need to squash the derivations
    data RedU (a : U) : Set where
      rnat : (α : a ≃ nat) -> Eval α -> RedU a
      rpi  : ∀ {a1 a2} -> (α : a ≃ pi a1 a2) -> Eval α 
           -> (ra1 : RedU a1)
           -> UTy (cEl ra1) a2
           -> RedU a

    Red≃U : ∀ {a b} -> RedU a -> RedU b -> (α : Id a b) -> Set
    Red≃U = {!!}

    cEl : {a : U} -> RedU a -> CTy (El a)     -- FIXME: going to need coherence for the squash elim
    cEl  (rnat E ev) = head-expand-CTy-El {!!} E ev
    cEl  (rpi  {a1}{a2} E ev ra1 ra2) = head-expand-CTy-El {!!} E ev

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