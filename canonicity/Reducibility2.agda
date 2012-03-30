{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open Paths

module canonicity.Reducibility2 where

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

  open Valuable≃ValuesM
  open Valuable≃Values
            
  open ValueTy

  record ValuableTy (A : Set) : Set1 where
    constructor valuablety 
    field
      vty    : Set
      valty  : ValueTy vty
      evty   : A ≃ vty
      evalty : Eval evty
  open ValuableTy

  record Valuable {A : Set} (vA : ValuableTy A) (M : A) : Set where
    constructor valuable 
    field
      v    : vty vA
      val  : Value (valty vA) v
      ev   : coe (evty vA) M ≃ v
      eval : Eval ev
  open Valuable

  record Valuable≃ {A : Set} (vA : ValuableTy A) {M N : A} (vM : Valuable vA M) (vN : Valuable vA N) (α : M ≃ N) : Set where
    constructor valuable≃
    field 
      v≃    : v vM ≃ v vN
      val≃  : Value≃ (valty vA) (val vM) (val vN) v≃
      ev≃   : ev vN ∘ resp (coe (evty vA)) α ∘ ! (ev vM) ≃ v≃
      eval≃ : Eval ev≃
  open Valuable≃ 

  -- simply typed terms; call by value
  record Map {A B : Set} (vA : ValuableTy A) (vB : ValuableTy B) (F : A -> B) : Set where
    constructor smap
    field
      mred  : {M : vty vA} -> Value (valty vA) M -> Valuable vB (F (coe (! (evty vA)) M))
      mresp : {M N : vty vA} {α : M ≃ N} {vM : Value (valty vA) M} {vN : Value (valty vA) N}
              (vα : Value≃ (valty vA) vM vN α)
           -> Valuable≃ vB (mred vM) (mred vN) (resp (F o (coe (! (evty vA)))) α)
  open Map

  mred' : {A B : Set} {As : ValuableTy A} {Bs : ValuableTy B} {F : A -> B}
        -> Map As Bs F
        -> ({M : A} -> Valuable As M -> Valuable Bs (F M))
  mred' {As = As} {Bs = Bs} {F = F} (smap fo fa) sM  = 
                 valuable (v (fo (val sM)))
                          (val (fo (val sM)))
                          (ev (fo (val sM)) 
                           ∘ resp (coe (evty Bs) o (F o (coe (! (evty As))))) (ev sM) 
                           ∘ resp (λ x → coe (evty Bs) (F x)) (! (coe-inv-1 (evty As)))) 
                          (FIXMEEval)

  mresp' : {A B : Set} {vA : ValuableTy A} {vB : ValuableTy B} {F : A -> B}
         -> (sF : Map vA vB F)
         -> {M N : A} {α : M ≃ N} {vM : Valuable vA M} {vN : Valuable vA N}
           (vα : Valuable≃ vA vM vN α)
           -> Valuable≃ vB (mred' sF vM) (mred' sF vN) (resp F α)
  mresp' = λ sF vα → valuable≃ _ (val≃ (mresp sF (val≃ vα)))
                                 (ev≃ (mresp sF (val≃ vα)) ∘ {!ev≃ vα!}) -- and LOTS of massaging, including resp-by-id with coe-inv-1; checked on paper
                                 FIXMEEval


  record Ty {Γ : Set} (vΓ : ValuableTy Γ) (A : Γ -> Set) : Set1 where
    constructor ty 
    field
      tred   : {θ : (vty vΓ)} -> (vθ : Value (valty vΓ) θ) -> ValuableTy (A (coe (! (evty vΓ)) θ))
      ssubst : {θ1 θ2 : vty vΓ} {α : θ1 ≃ θ2}
               {vθ1 : Value (valty vΓ) θ1} {vθ2 : Value (valty vΓ) θ2}
               (vα  : Value≃ (valty vΓ) vθ1 vθ2 α)
            -> Map (tred vθ1) (tred vθ2) (subst A (resp (coe (! (evty vΓ))) α))
  open Ty

  -- lift to valuables
  tred' : {Γ : Set} {vΓ : ValuableTy Γ} {A : Γ -> Set} 
        -> Ty vΓ A
        -> {θ : Γ} -> (vθ : Valuable vΓ θ) -> ValuableTy (A θ)
  tred' {vΓ = vΓ} {A = A} vA vθ = valuablety (vty (tred vA (val vθ))) 
                           (valty (tred vA (val vθ)))
                           (evty (tred vA (val vθ)) 
                            ∘ resp (A o coe (! (evty vΓ))) (ev vθ) ∘ resp A (! (coe-inv-1 (evty vΓ))))
                           FIXMEEval

  ssubst' :  {Γ : Set} {vΓ : ValuableTy Γ} {A : Γ -> Set} -> (sA : Ty vΓ A)
          -> {θ1 θ2 : Γ} {α : θ1 ≃ θ2}
             {vθ1 : Valuable vΓ θ1} {vθ2 : Valuable vΓ θ2}
             (vα  : Valuable≃ vΓ vθ1 vθ2 α)
          -> Map (tred' sA vθ1) (tred' sA vθ2) (subst A α)
  ssubst' = λ sA vα → smap (λ x → valuable _ (val (mred (ssubst sA (val≃ vα)) x))
                                              (ev (mred (ssubst sA (val≃ vα)) x) ∘ {!ev≃ vα!})
                                              FIXMEEval) 
                           (λ vα' → valuable≃ {!!} {!!} {!!} {!!})

  record Tm {Γ : Set} (Γs : ValuableTy Γ) {A : Γ -> Set} (As : Ty Γs A) (M : (x : Γ) -> A x) : Set where
    constructor tm 
    field
      red   : {θ : vty Γs} -> (vθ : Value (valty Γs) θ) -> Valuable (tred As vθ) (M (coe (! (evty Γs)) θ))
      sresp : {θ1 θ2 : vty Γs} {α : θ1 ≃ θ2} {vθ1 : Value (valty Γs) θ1} {vθ2 : Value (valty Γs) θ2} 
              (vα : Value≃ (valty Γs) vθ1 vθ2 α) 
             → Valuable≃ (tred As vθ2)
                         (mred' (ssubst As vα) (red vθ1))
                         (red vθ2)
                         (respd M (resp (coe (! (evty Γs))) α))
  open Tm


  vRefl' : ∀ {A} {vA : ValuableTy A} {M : A} (vM : Valuable vA M) -> Valuable≃ vA vM vM (Refl{_}{M})
  vRefl' {_}{vA} vM = valuable≃ 
                      _ (val≃0 (vRefl (valty vA) (val vM))) (ev≃0 (vRefl (valty vA) (val vM)) ∘ {!!})
                      FIXMEEval
       
  v!' : ∀ {A} (vA : ValuableTy A) {M N : A} {α : M ≃ N} {vM : Valuable vA M}{vN : Valuable vA N} 
          (vα : Valuable≃ vA vM vN α)
        -> Valuable≃ vA vN vM (! α)
  v!' vA vα = valuable≃ _ (val≃0 (v! (valty vA) (val≃ vα))) 
                          (ev≃0 (v! (valty vA) (val≃ vα)) ∘ resp ! (ev≃ vα) ∘ {!!}) -- massage
                          FIXMEEval

  v∘'     : ∀ {A} (vA : ValuableTy A)
              {P M N : A} {β : N ≃ P} {α : M ≃ N} 
              {vP : Valuable vA P}{vN : Valuable vA N}{vM : Valuable vA M} 
              (vβ : Valuable≃ vA vN vP β)(vα : Valuable≃ vA vM vN α)
            -> Valuable≃ vA vM vP (β ∘ α)
  v∘' vA vβ vα = valuable≃ _ (val≃0 (v∘ (valty vA) (val≃ vβ) (val≃ vα))) 
                                 (ev≃0 (v∘ (valty vA) (val≃ vβ) (val≃ vα)) ∘ resp∘ (ev≃ vβ) (ev≃ vα) ∘ {!!}) FIXMEEval

  -- examples

  mid : {A : Set} (As : ValuableTy A) -> Map As As (\ x -> x)
  mid As = smap (λ vM → valuable _ vM (coe-inv-2 (evty As)) FIXMEEval) 
                (λ {_}{_}{α} vα → valuable≃ _ vα {!!} FIXMEEval) -- massage using resp-by-id coe-inv-2 

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
                                  (resp-o g (f o coe (! (evty As))) α)) 
                             FIXMEEval
                             ) 

  head-expand-map : {A B : Set} {vA : ValuableTy A} {vB : ValuableTy B}
                    {F G : A -> B}
                  -> Map vA vB F 
                  -> (α : F ≃ G)
                  -> Eval α
                  -> Map vA vB G
  head-expand-map = λ sM α _ → smap (λ x → valuable _ (val (mred sM x)) (ev (mred sM x) ∘ {!!}) FIXMEEval) 
                                    {!!}

  mto : {Γ Δ : Set} {sΓ : ValuableTy Γ} {sΔ : ValuableTy Δ}
         {θ : Γ -> Δ} {A : Δ -> Set}
       -> (sA : Ty sΔ A)
       -> (sθ : Map sΓ sΔ θ)
       -> Ty sΓ (A o θ)
  mto sA sθ = ty (λ vθ' → tred' sA (mred sθ vθ')) 
                 (\ v -> head-expand-map (ssubst' sA (mresp sθ v)) 
                                         {!!} FIXMEEval)


{-
  Value× : {A B : Set} (As : ValueTy A) (Bs : ValueTy B)
                -> A × B -> Set 
  Value× As Bs (x , y) = Value As x × Value Bs y  -- really want them to be EQUAL to a pair

  Value×≃ : {A B : Set} (As : ValueTy A) (Bs : ValueTy B)
            {p1 : A × B} {p2 : A × B}
            (p1v : Value× As Bs p1) (p2v : Value× As Bs p2)
            (α : p1 ≃ p2) -> Set
  Value×≃ As Bs {p1 = x1 , y1} {p2 = x2 , y2} vp1 vp2 α = 
    Σ (λ (α1 : x1 ≃ x2) →
    Σ (λ (α2 : y1 ≃ y2) →
      (α ≃ resp2 _,_ α1 α2) ×   -- really want an equality
      Value≃ As (fst vp1) (fst vp2) α1 ×
      Value≃ Bs (snd vp1) (snd vp2) α2))

  _×c_ : {A B : Set} -> ValueTy A -> ValueTy B -> ValueTy (A × B)
  As ×c Bs = record { Value = Value× As Bs;
                      Value≃ = Value×≃ As Bs}

  fst_ok : {A B : Set} (As : ValueTy A) (Bs : ValueTy B) -> Map (As ×c Bs) As fst
  fst_ok As Bs = smap (λ { {(M , N)} (vM , vN) → valuable M vM Refl evRefl})
                      (λ { {(M1 , N1)} {(M2 , N2)} {α} {vM1} {vM2} (α1 , α2 , αis , vα1 , vα2) -> 
                                 valuable≃ α1 vα1 {!!} } -- resp fst (resp2 _,_ α1 α2) ≃ α1
                      )

  pair_ok : {Γ A B : Set} (Γs : ValueTy Γ) (As : ValueTy A) (Bs : ValueTy B) 
            (M : Γ -> A) (N : Γ -> B)
          -> Map Γs As M
          -> Map Γs Bs N
          -> Map Γs (As ×c Bs) (\ x -> M x , N x)
  pair_ok {Γ} {A} {B} Γs As Bs M N (smap Mo Ma) (smap No Na) = 
    smap (λ vg → valuable _ (val (Mo vg) , val (No vg)) 
                            (resp2 _,_ (ev (Mo vg)) (ev (No vg))) 
                            FIXMEEval) 
           (λ vα → valuable≃ _
                             (_ , 
                              _ , 
                              Refl , -- this MUST be Refl; this should be equality not equiv
                              val≃ (Ma vα) , 
                              val≃ (Na vα)) 
                             {!!}) -- massage and use comm (Ma vα) and comm (Na vα)
-}

  -- "return" for valuabile types
  retty : ∀ {Γ} -> ValueTy Γ -> ValuableTy Γ
  retty v = valuablety _ v Refl evRefl

  move : ∀ {A} -> (vA : ValuableTy A) -> (A -> vty vA)
  move vA = coe (evty vA)

  unmove : ∀ {A} -> (vA : ValuableTy A) -> (vty vA -> A)
  unmove vA = coe (! (evty vA))

  valuable-unmove :  ∀ {A} (vA : ValuableTy A) -> ∀ {M} 
          -> Value (valty vA) M -> Valuable vA (unmove vA M)
  valuable-unmove vA vM = valuable _ vM (coe-inv-2 (evty vA)) FIXMEEval

  head-expand : ∀ {A M N} {vA : ValuableTy A}
                -> (vN : Valuable vA N)
                -> (α : M ≃ N)
                -> Eval α 
                -> Valuable vA M
  head-expand {vA = vA} vN α e = valuable (v vN) (val vN) (ev vN ∘ resp (move vA) α) FIXMEEval

  head-expand≃ : {A : Set} {vA : ValuableTy A} {M N : A} 
                 {vM : Valuable vA M} {vN : Valuable vA N} {α β : M ≃ N}
               -> Valuable≃ vA vM vN α
               -> (g : β ≃ α)
               -> Eval g
               -> Valuable≃ vA vM vN β
  head-expand≃ = λ vα g _ → valuable≃ _ (val≃ vα) {!!} FIXMEEval

{-                
  module StrictSigma where
    -- WARNING: never use subst/resp on these
    data ΣValue {Γ : Set} (vΓ : ValueTy Γ) {A : Γ -> Set} (sA : Ty (retty vΓ) A) : (Σ A) -> Set where
      cpair : {M : _} 
              -> (vM : Value vΓ M) -> {N : _} -> Value (valty (tred sA vM)) N 
              -> ΣValue vΓ sA (M , unmove (tred sA vM) N)
  
    data ΣValue≃ {Γ : Set} (vΓ : ValueTy Γ) {A : Γ -> Set} (sA : Ty (retty vΓ) A) 
                 : {M N : (Σ A)} (vM : ΣValue vΓ sA M) (vN : ΣValue vΓ sA N) (α : M ≃ N) -> Set where
      cpair≃ : ∀ {M1 M2 α} {vM1 : Value vΓ M1} {vM2 : Value vΓ M2} 
              -> (vα : Value≃ vΓ vM1 vM2 α)
              -> ∀ {N1 N2 β} {vN1 : Value (valty (tred sA vM1)) N1} {vN2 : Value (valty (tred sA vM2)) N2 }
              -> Valuable≃ (tred sA vM2) (head-expand (mred (ssubst sA vα) vN1) 
                                                      (resp (λ x → subst A x (unmove (tred sA vM1) N1)) (! (resp-id α)))
                                                      FIXMEEval)
                                         (valuable-unmove (tred sA vM2) vN2)
                                         β
              -> ΣValue≃ vΓ sA (cpair vM1 vN1) (cpair vM2 vN2) (pair≃ α β) 
  
    Σval : {Γ : Set} (vΓ : ValueTy Γ) {A : Γ -> Set} (sA : Ty (retty vΓ) A) -> ValueTy (Σ A)
    Σval vΓ sA = record { Value = ΣValue vΓ sA; 
                          Value≃ = ΣValue≃ vΓ sA; 
                          vRefl = {!!}; v! = {!!}; v∘ = {!!} }
    
    Σc : {Γ : Set} (vΓ : ValuableTy Γ) {A : Γ -> Set} (sA : Ty vΓ A) -> ValuableTy (Σ A)
    Σc {Γ} vΓ {A} sA = valuablety (Σ (\ (x : vty vΓ) -> A (unmove vΓ x)))
                                  (Σval (valty vΓ) {!sA!}) {!!} FIXMEEval
-}

  -- both Σ itself is lazy,
  -- and values of Σ type are lazy
  module LazySigma where
    -- WARNING: never use subst/resp on these
    data ΣValue {Γ : Set} (vΓ : ValuableTy Γ) {A : Γ -> Set} (sA : Ty vΓ A) : (Σ A) -> Set where
      cpair : {M : _} 
              -> (vM : Valuable vΓ M) -> {N : _} -> Valuable (tred' sA vM) N 
              -> ΣValue vΓ sA (M , N)
  
    data ΣValue≃ {Γ : Set} (vΓ : ValuableTy Γ) {A : Γ -> Set} (sA : Ty vΓ A) 
                 : {M N : (Σ A)} (vM : ΣValue vΓ sA M) (vN : ΣValue vΓ sA N) (α : M ≃ N) -> Set where
      cpair≃ : ∀ {M1 M2 α} {vM1 : Valuable vΓ M1} {vM2 : Valuable vΓ M2} 
              -> (vα : Valuable≃ vΓ vM1 vM2 α)
              -> ∀ {N1 N2 β} {vN1 : Valuable (tred' sA vM1) N1} {vN2 : Valuable (tred' sA vM2) N2 }
              -> Valuable≃ (tred' sA vM2) (mred' (ssubst' sA vα) vN1)
                                          vN2
                                          β
              -> ΣValue≃ vΓ sA (cpair vM1 vN1) (cpair vM2 vN2) (pair≃ α β) 
  
    Σval : {Γ : Set} (vΓ : ValuableTy Γ) {A : Γ -> Set} (sA : Ty vΓ A) -> ValueTy (Σ A)
    Σval vΓ sA = record { Value = ΣValue vΓ sA; 
                          Value≃ = ΣValue≃ vΓ sA; 
                          vRefl = {!!}; v! = {!!}; v∘ = {!!} }
    
    Σc : {Γ : Set} (vΓ : ValuableTy Γ) {A : Γ -> Set} (sA : Ty vΓ A) -> ValuableTy (Σ A)
    Σc {Γ} vΓ {A} sA = valuablety (Σ (\ (x : Γ) -> A x))
                                  (Σval vΓ sA) Refl FIXMEEval


    mfst :  {Γ : Set} (sΓ : ValuableTy Γ) {A : Γ -> Set} (sA : Ty sΓ A) 
         -> Map (Σc sΓ sA) sΓ fst
    mfst sΓ sA = smap (λ {(cpair vM vN) → vM})
                      (λ { {._} (cpair≃{_}{_}{α} vα{_}{_}{β} vβ) → head-expand≃ vα (Σ≃β1 α β) FIXMEEval}) -- head-expand
                    

    svar : {Γ : Set} (sΓ : ValuableTy Γ) {A : Γ -> Set} (sA : Ty sΓ A) 
        -> Tm (Σc sΓ sA) (mto sA (mfst sΓ sA)) snd
    svar sΓ sA = tm (λ {(cpair vM vN) → vN})
                    (λ { {._} (cpair≃ vα vβ) → valuable≃ _ (val≃ vβ) (ev≃ vβ ∘ {!!}) FIXMEEval})


  -- lazy identity types:
  -- this makes the definitions work out better, and
  -- makes sense because type theory is missing the injection from paths to elements of the identity types;
  -- if that were there, the path sitting under it would be lazy by
  -- analogy to Σ
  -- 
  -- Never use subst/resp for this!
  Idc : {A : Set} {vA : ValuableTy A} {M N : A} (vM : Valuable vA M) (vN : Valuable vA N) -> ValueTy (Id M N)
  Idc {_}{vA} vM vN = record { Value = Valuable≃ vA vM vN ; 
                       Value≃ = λ _ _ _ → Unit; 
                       vRefl = λ vM' → valuable≃0 Refl <> Refl evRefl;
                       v∘ = λ vβ vα → valuable≃0 _ _ Refl evRefl;
                       v! = λ vα → valuable≃0 _ <> Refl evRefl}

  sId : {Γ : Set} {Γs : ValuableTy Γ}
         {A : Γ -> Set} {As : Ty Γs A} 
         {M N : (g : Γ) -> A g} (Ms : Tm Γs As M) (Ns : Tm Γs As N) 
         -> Ty Γs (\ x -> Id (M x) (N x))
  sId {Γ} {Γs} {A} {As} {M} {N} Ms Ns = 
               ty (λ θs → retty (Idc (red Ms θs) (red Ns θs))) 
                  (λ {θ1} {θ2} {α} {vθ1} {vθ2} vα → smap (λ vM → valuable _ (v∘' (tred As vθ2) (v∘' (tred As vθ2) (sresp Ns vα) (mresp' (ssubst As vα) vM)) (v!' (tred As vθ2) (sresp Ms vα)))
                                                                         {!!} FIXMEEval)
                                                         (λ vα' → valuable≃ _ _ Refl FIXMEEval))
                     --         ({!!} ∘ subst-Id-d M N α _) 
  
  sRefl : {Γ : Set} {Γs : ValuableTy Γ}
          {A : Γ -> Set} {As : Ty Γs A} 
          {M : (g : Γ) -> A g} (sM : Tm Γs As M) 
        -> Tm Γs (sId sM sM) (\ θ -> Refl{_}{M θ})
  sRefl {As = As} sM = tm (λ vθ → valuable _ (vRefl' (red sM vθ)) Refl FIXMEEval)
                          (λ vα → valuable≃ _ _ {!!} FIXMEEval) -- there would need to be work here if the Value≃'s of Id didn't accept everything
