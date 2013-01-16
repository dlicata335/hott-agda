{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open Paths

module canonicity.Reducibility where

  postulate
    FIXMETodo    : ∀ {A : Set} -> A -- not sure this can be filled in
    FIXMEChecked : ∀ {A : Set} -> A -- checked on paper; to formalize

  -- this doesn't really work, because we don't want
  -- Value and Value≃ to respect equivalence.
  --
  -- If they do, then anything that is equivalent to a value
  -- by any means (not just evaluation) is a value.
  --
  -- So we need to be careful never to use
  -- subst/resp with Value and Value≃.  
  --
  -- It's still worthhile to use Agda for generating proof obligations,
  -- and for pushing definitonal equalities around.  
  --
  -- could do it all for an encoded language to get around this

  -- needs to classify individual steps, not just evaluation to a value.
  -- or we could use a different judgement in head-expand
  data Eval : {A : Set} {M N : A} -> M ≃ N -> Set where
    evRefl : {A : _} {M : A} -> Eval (Refl{_}{M})
    FIXMEEval : {A : Set} {M N : A} -> {α : M ≃ N} -> Eval α

  -- unification works better if the valuable things are explicit records
  -- than if they use a common abstraction

  -- need to use this abbreviation in the definition of ValueTy
  module Valuable≃ValuesM {A : Set}
                          {Value : A -> Set}
                          {Value≃ : {M N : A} -> Value M -> Value N -> M ≃ N -> Set}
                       where 
    record Valuable≃Values {M : A} {N : A} (vM : Value M) (vN : Value N) 
                           (α : M ≃ N)
                           : Set where
        constructor valuable≃0 
        field
          v≃0    : M ≃ N
          val≃0  : Value≃ vM vN v≃0
          ev≃0   : α ≃ v≃0
          eval≃0 : Eval ev≃0

  -- semantic type value
  record ValueTy (A : Set) : Set1 where
    field
     Value  : A -> Set
     Value≃ : {M N : A} -> Value M -> Value N -> M ≃ N -> Set
    open Valuable≃ValuesM {A} {Value} {Value≃}
    field
     vRefl  : {M : A} (vM : Value M) -> Valuable≃Values vM vM (Refl{_}{M})
     v!     : {M N : A} {α : M ≃ N} {vM : Value M}{vN : Value N} 
               (vα : Value≃ vM vN α)
            -> Valuable≃Values vN vM (! α)
     v∘     : {P M N : A} {β : N ≃ P} {α : M ≃ N} {vP : Value P}{vN : Value N}{vM : Value M} 
              (vβ : Value≃ vN vP β)(vα : Value≃ vM vN α)
            -> Valuable≃Values vM vP (β ∘ α)

  open Valuable≃ValuesM public
  open Valuable≃Values public
            
  open ValueTy public

  record ValuableTy (A : Set) : Set1 where
    constructor valuablety 
    field
      vty    : Set
      valty  : ValueTy vty
      evty   : A ≃ vty
      evalty : Eval evty
  open ValuableTy public

  move : ∀ {A} -> (vA : ValuableTy A) -> (A -> vty vA)
  move vA = coe (evty vA)

  unmove : ∀ {A} -> (vA : ValuableTy A) -> (vty vA -> A)
  unmove vA = coe (! (evty vA))

  record Valuable {A : Set} (vA : ValuableTy A) (M : A) : Set where
    constructor valuable 
    field
      v    : vty vA
      val  : Value (valty vA) v
      ev   : move vA M ≃ v
      eval : Eval ev
  open Valuable public

  record Valuable≃ {A : Set} (vA : ValuableTy A) {M N : A} (vM : Valuable vA M) (vN : Valuable vA N) (α : M ≃ N) : Set where
    constructor valuable≃
    field 
      v≃    : v vM ≃ v vN
      val≃  : Value≃ (valty vA) (val vM) (val vN) v≃
      ev≃   : ev vN ∘ resp (move vA) α ∘ ! (ev vM) ≃ v≃
      eval≃ : Eval ev≃
  open Valuable≃ public

  -- simply typed terms; call by value
  record Map {A B : Set} (vA : ValuableTy A) (vB : ValuableTy B) (F : A -> B) : Set where
    constructor smap
    field
      mred  : {M : vty vA} -> Value (valty vA) M -> Valuable vB (F (unmove vA M))
      mresp : {M N : vty vA} {α : M ≃ N} {vM : Value (valty vA) M} {vN : Value (valty vA) N}
              (vα : Value≃ (valty vA) vM vN α)
           -> Valuable≃ vB (mred vM) (mred vN) (resp (F o (unmove vA)) α)
  open Map public

  mred' : {A B : Set} {As : ValuableTy A} {Bs : ValuableTy B} {F : A -> B}
        -> Map As Bs F
        -> ({M : A} -> Valuable As M -> Valuable Bs (F M))
  mred' {As = As} {Bs = Bs} {F = F} (smap fo fa) sM  = 
                 valuable (v (fo (val sM)))
                          (val (fo (val sM)))
                          (ev (fo (val sM)) 
                           ∘ resp (move Bs o (F o (unmove As))) (ev sM) 
                           ∘ resp (λ x → move Bs (F x)) (! (coe-inv-1 (evty As)))) 
                          (FIXMEEval)

  mresp' : {A B : Set} {vA : ValuableTy A} {vB : ValuableTy B} {F : A -> B}
         -> (sF : Map vA vB F)
         -> {M N : A} {α : M ≃ N} {vM : Valuable vA M} {vN : Valuable vA N}
           (vα : Valuable≃ vA vM vN α)
           -> Valuable≃ vB (mred' sF vM) (mred' sF vN) (resp F α)
  mresp' = λ sF vα → valuable≃ _ (val≃ (mresp sF (val≃ vα)))
                                 (ev≃ (mresp sF (val≃ vα)) ∘ FIXMEChecked) -- ev≃ vα and LOTS of massaging, including resp-by-id with coe-inv-1; checked on paper
                                 FIXMEEval


  record Ty {Γ : Set} (vΓ : ValuableTy Γ) (A : Γ -> Set) : Set1 where
    constructor ty 
    field
      tred   : {θ : (vty vΓ)} -> (vθ : Value (valty vΓ) θ) -> ValuableTy (A (unmove vΓ θ))
      ssubst : {θ1 θ2 : vty vΓ} {α : θ1 ≃ θ2}
               {vθ1 : Value (valty vΓ) θ1} {vθ2 : Value (valty vΓ) θ2}
               (vα  : Value≃ (valty vΓ) vθ1 vθ2 α)
            -> Map (tred vθ1) (tred vθ2) (subst A (resp (unmove vΓ) α))
  open Ty public

  -- lift to valuables
  tred' : {Γ : Set} {vΓ : ValuableTy Γ} {A : Γ -> Set} 
        -> Ty vΓ A
        -> {θ : Γ} -> (vθ : Valuable vΓ θ) -> ValuableTy (A θ)
  tred' {vΓ = vΓ} {A = A} vA vθ = valuablety (vty (tred vA (val vθ))) 
                           (valty (tred vA (val vθ)))
                           (evty (tred vA (val vθ)) 
                            ∘ resp (A o unmove vΓ) (ev vθ) ∘ resp A (! (coe-inv-1 (evty vΓ))))
                           FIXMEEval

  ssubst' :  {Γ : Set} {vΓ : ValuableTy Γ} {A : Γ -> Set} -> (sA : Ty vΓ A)
          -> {θ1 θ2 : Γ} {α : θ1 ≃ θ2}
             {vθ1 : Valuable vΓ θ1} {vθ2 : Valuable vΓ θ2}
             (vα  : Valuable≃ vΓ vθ1 vθ2 α)
          -> Map (tred' sA vθ1) (tred' sA vθ2) (subst A α)
  ssubst' = λ sA vα → smap (λ x → valuable _ (val (mred (ssubst sA (val≃ vα)) x))
                                              (ev (mred (ssubst sA (val≃ vα)) x) ∘ FIXMETodo) -- ev≃ vα
                                              FIXMEEval) 
                           (λ vα' → valuable≃ _ (val≃ (mresp (ssubst sA (val≃ vα)) vα')) (ev≃ (mresp (ssubst sA (val≃ vα)) vα') ∘ FIXMETodo) FIXMEEval)

  record Tm {Γ : Set} (Γs : ValuableTy Γ) {A : Γ -> Set} (As : Ty Γs A) (M : (x : Γ) -> A x) : Set where
    constructor tm 
    field
      red   : {θ : vty Γs} -> (vθ : Value (valty Γs) θ) -> Valuable (tred As vθ) (M (unmove Γs θ))
      sresp : {θ1 θ2 : vty Γs} {α : θ1 ≃ θ2} {vθ1 : Value (valty Γs) θ1} {vθ2 : Value (valty Γs) θ2} 
              (vα : Value≃ (valty Γs) vθ1 vθ2 α) 
             → Valuable≃ (tred As vθ2)
                         (mred' (ssubst As vα) (red vθ1))
                         (red vθ2)
                         (respd M (resp (unmove Γs) α))
  open Tm public

  vRefl' : ∀ {A} {vA : ValuableTy A} {M : A} (vM : Valuable vA M) -> Valuable≃ vA vM vM (Refl{_}{M})
  vRefl' {_}{vA} vM = valuable≃ 
                      _ (val≃0 (vRefl (valty vA) (val vM))) (ev≃0 (vRefl (valty vA) (val vM)) ∘ FIXMEChecked)
                      FIXMEEval
       
  v!' : ∀ {A} (vA : ValuableTy A) {M N : A} {α : M ≃ N} {vM : Valuable vA M}{vN : Valuable vA N} 
          (vα : Valuable≃ vA vM vN α)
        -> Valuable≃ vA vN vM (! α)
  v!' vA vα = valuable≃ _ (val≃0 (v! (valty vA) (val≃ vα))) 
                          (ev≃0 (v! (valty vA) (val≃ vα)) ∘ resp ! (ev≃ vα) ∘ FIXMEChecked) -- massage
                          FIXMEEval

  v∘'     : ∀ {A} (vA : ValuableTy A)
              {P M N : A} {β : N ≃ P} {α : M ≃ N} 
              {vP : Valuable vA P}{vN : Valuable vA N}{vM : Valuable vA M} 
              (vβ : Valuable≃ vA vN vP β)(vα : Valuable≃ vA vM vN α)
            -> Valuable≃ vA vM vP (β ∘ α)
  v∘' vA vβ vα = valuable≃ _ (val≃0 (v∘ (valty vA) (val≃ vβ) (val≃ vα))) 
                                 (ev≃0 (v∘ (valty vA) (val≃ vβ) (val≃ vα)) ∘ resp∘ (ev≃ vβ) (ev≃ vα) ∘ FIXMEChecked) FIXMEEval

  -- "return" for valuabile types
  retty : ∀ {Γ} -> ValueTy Γ -> ValuableTy Γ
  retty v = valuablety _ v Refl evRefl

  valuable-unmove :  ∀ {A} (vA : ValuableTy A) -> ∀ {M} 
          -> Value (valty vA) M -> Valuable vA (unmove vA M)
  valuable-unmove vA vM = valuable _ vM (coe-inv-2 (evty vA)) FIXMEEval

  head-expand : ∀ {A M N} {vA : ValuableTy A}
                -> (vN : Valuable vA N)
                -> (α : M ≃ N)
                -> Eval α 
                -> Valuable vA M
  head-expand {vA = vA} vN α e = valuable (v vN) (val vN) (ev vN ∘ resp (move vA) α) FIXMEEval

  head-expand-ty : ∀ {A B} (vB : ValuableTy B)
                 -> (α : A ≃ B)
                 -> Eval α 
                 -> ValuableTy A
  head-expand-ty vB α e = valuablety _ (valty vB) (evty vB ∘ α) FIXMEEval

  head-expand≃ : {A : Set} {vA : ValuableTy A} {M N : A} 
                 {vM : Valuable vA M} {vN : Valuable vA N} {α β : M ≃ N}
               -> Valuable≃ vA vM vN α
               -> (eβ : β ≃ α)
               -> Eval eβ
               -> Valuable≃ vA vM vN β
  head-expand≃ {_}{vA}{_}{_}{vM}{vN} vα eβ _ = 
    valuable≃ _ (val≃ vα) (ev≃ vα ∘ resp (λ x → ev vN ∘ resp (subst (λ x' → x') (evty vA)) x ∘ ! (ev vM)) eβ) FIXMEEval


  mo : {A B C : Set} (As : ValuableTy A) (Bs : ValuableTy B) (Cs : ValuableTy C) 
         (f : A -> B) (g : B -> C)
       -> Map Bs Cs g
       -> Map As Bs f
       -> Map As Cs (g o f)
  mo As Bs Cs f g sg sf = 
    smap (λ vM → mred' sg (mred sf vM) ) 
         (λ {_} {_} {α} {vM} {vN} vα → valuable≃ _ (val≃ (mresp' sg (mresp sf vα))) 
                             (ev≃ (mresp' sg (mresp sf vα)) 
                              ∘ resp
                                  (λ x →
                                     ev (mred' sg (mred sf vN)) ∘
                                     resp (subst (λ x' → x') (evty Cs)) x ∘
                                     ! (ev (mred' sg (mred sf vM))))
                                  (resp-o g (f o unmove As) α)) 
                             FIXMEEval
                             ) 

  head-expand-map : {A B : Set} {vA : ValuableTy A} {vB : ValuableTy B}
                    {F G : A -> B}
                  -> Map vA vB F 
                  -> (α : F ≃ G)
                  -> Eval α
                  -> Map vA vB G
  head-expand-map = λ sM α _ → smap (λ x → valuable _ (val (mred sM x)) (ev (mred sM x) ∘ FIXMEChecked) FIXMEEval) 
                                    (λ vα → valuable≃ _ (val≃ (mresp sM vα)) (ev≃ (mresp sM vα) ∘ FIXMETodo) FIXMEEval)

  mto : {Γ Δ : Set} {sΓ : ValuableTy Γ} {sΔ : ValuableTy Δ}
         {θ : Γ -> Δ} {A : Δ -> Set}
       -> (sA : Ty sΔ A)
       -> (sθ : Map sΓ sΔ θ)
       -> Ty sΓ (A o θ)
  mto sA sθ = ty (λ vθ' → tred' sA (mred sθ vθ')) 
                 (\ v -> head-expand-map (ssubst' sA (mresp sθ v)) 
                                         FIXMEChecked FIXMEEval)

