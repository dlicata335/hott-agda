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

  -- simply typed terms
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

  -- simply typed terms
  record Map {A B : Set} (vA : ValuableTy A) (vB : ValuableTy B) (F : A -> B) : Set where
    constructor smap
    field
      mred  : {M : vty vA} -> Value (valty vA) M -> Valuable vB (F (coe (! (evty vA)) M))
      mresp : {M N : vty vA} {α : M ≃ N} {vM : Value (valty vA) M} {vN : Value (valty vA) N}
              (vα : Value≃ (valty vA) vM vN α)
           -> Valuable≃ vB (mred vM) (mred vN) (resp (F o (coe (! (evty vA)))) α)
  open Map

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
                           (evty (tred vA (val vθ)) ∘ resp (A o coe (! (evty vΓ))) (ev vθ) ∘ {!!})
                           FIXMEEval

  mred' : {A B : Set} {As : ValuableTy A} {Bs : ValuableTy B} {F : A -> B}
        -> Map As Bs F
        -> ({M : A} -> Valuable As M -> Valuable Bs (F M))
  mred' {As = As} {Bs = Bs} {F = F} sF sM  = 
                 valuable (v (mred sF (val sM)))
                          (val (mred sF (val sM)))
                          (ev (mred sF (val sM)) ∘ resp (coe (evty Bs) o (F o (coe (! (evty As))))) (ev sM) ∘ {!!}) 
                          (FIXMEEval)

{-
  record Tm {Γ : Set} (Γs : ValueTy Γ) {A : Γ -> Set} (As : Ty Γs A) (M : (x : Γ) -> A x) : Set where
    constructor tm 
    field
      red   : {θ : Γ} -> (vθ : Value Γs θ) -> Valuable (tred As vθ) (M θ)
      sresp : {θ1 θ2 : Γ} {α : θ1 ≃ θ2} {vθ1 : Value Γs θ1} {vθ2 : Value Γs θ2} (vα : Value≃ Γs vθ1 vθ2 α) 
             → Valuable≃ _ (mred' (ssubst As vα) (red vθ1))
                           (red vθ2)
                           (respd M α)
  open Tm

  -- examples

  mid : {A : Set} (As : ValueTy A) -> Map As As (\ x -> x)
  mid As = smap (λ vM → valuable _ vM Refl evRefl) 
                (λ {_}{_}{α} vα → valuable≃ _ vα (resp-id α ∘ ∘-unit-l (resp (λ x → x) α)))

  mo : {A B C : Set} (As : ValueTy A) (Bs : ValueTy B) (Cs : ValueTy C) 
         (f : A -> B) (g : B -> C)
       -> Map Bs Cs g
       -> Map As Bs f
       -> Map As Cs (g o f)
  mo As Bs Cs f g (smap go ga) (smap fo fa) = 
    smap (λ vM → valuable _ 
                           (val (go (val (fo vM)))) 
                           (ev (go (val (fo vM))) ∘ resp g (ev (fo vM))) 
                           FIXMEEval) 
           (λ vα → 
             valuable≃ _
                       (val≃ (ga (val≃ (fa vα)))) 
                       (comm (ga (val≃ (fa vα))) ∘ {!!})) -- massage and use comm (fa M N α vM vN vα)

  mto : {Γ Δ : Set} {sΓ : ValueTy Γ} {sΔ : ValueTy Δ}
         {θ : Γ -> Δ} {A : Δ -> Set}
       -> (sA : Ty sΔ A)
       -> (sθ : Map sΓ sΔ θ)
       -> Ty sΓ (A o θ)
  mto sA sθ = ty (λ vθ' → tred' sA (mred sθ vθ')) 
                 (λ vα → {!ssubst sA  !})

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

  -- WARNING: never use subst/resp on these
  data ΣValue {Γ : Set} (sΓ : ValueTy Γ) {A : Γ -> Set} (sA : Ty sΓ A) : (Σ A) -> Set where
    cpair : ∀ {M N} -> (vM : Value sΓ M) -> Value (tred sA vM) N -> ΣValue sΓ sA (M , N)

  data ΣValue≃ {Γ : Set} (sΓ : ValueTy Γ) {A : Γ -> Set} (sA : Ty sΓ A) 
               : {M N : (Σ A)} (vM : ΣValue sΓ sA M) (vN : ΣValue sΓ sA N) (α : M ≃ N) -> Set where
    cpair≃ : ∀ {M1 N1 M2 N2 α β vM1 vN1 vM2 vN2} 
           -> (vα : Value≃ sΓ vM1 vM2 α)
           -> Valuable≃ (tred sA vM2) (mred (ssubst sA vα) vN1) (valuable _ vN2 Refl evRefl) β
           -> ΣValue≃ sΓ sA {(M1 , N1)} {(M2 , N2)} (cpair vM1 vN1) (cpair vM2 vN2) (pair≃ α β) 

  Σc : {Γ : Set} (sΓ : ValueTy Γ) {A : Γ -> Set} (sA : Ty sΓ A) -> ValueTy (Σ A)
  Σc sΓ sA = record { Value = ΣValue sΓ sA; 
                      Value≃ = ΣValue≃ sΓ sA; 
                      vRefl = {!!}; v! = {!!}; v∘ = {!!} }

  mfst :  {Γ : Set} (sΓ : ValueTy Γ) {A : Γ -> Set} (sA : Ty sΓ A) 
       -> Map (Σc sΓ sA) sΓ fst
  mfst sΓ sA = smap (λ {(cpair v1 _) → valuable _ v1 Refl evRefl})
                    (λ { {._} (cpair≃ {_}{_}{_}{_}{α}{β} vα vβ) → valuable≃ _ vα (Σ≃β1 α β ∘ ∘-unit-l (resp fst (pair≃ α β))) })

  valar : {Γ : Set} (sΓ : ValueTy Γ) {A : Γ -> Set} (sA : Ty sΓ A) 
       -> Tm (Σc sΓ sA) {!!} snd
  valar = {!!}

  -- Never use subst/resp for this!
  data IdValue {A : Set} {As : ValueTy A} {M N : A} (vM : Valuable As M) (vN : Valuable As N) : 
                Id M N -> Set where
       idValue : (α : v vM ≃ v vN) 
               -> Value≃ As (val vM) (val vN) α
               -> IdValue vM vN (! (ev vN) ∘ α ∘ ev vM)

  Idc : {A : Set} {As : ValueTy A} {M N : A} (vM : Valuable As M) (vN : Valuable As N) -> ValueTy (Id M N)
  Idc vM vN = record { Value = IdValue vM vN; 
                       Value≃ = λ _ _ _ → Unit; 
                       vRefl = λ vM' → valuable≃0 Refl <> Refl evRefl;
                       v∘ = λ vβ vα → valuable≃0 _ _ Refl evRefl;
                       v! = λ vα → valuable≃0 _ <> Refl evRefl}
  
  sId : {Γ : Set} {Γs : ValueTy Γ}
         {A : Γ -> Set} {As : Ty Γs A} 
         {M N : (g : Γ) -> A g} (Ms : Tm Γs As M) (Ns : Tm Γs As N) 
         -> Ty Γs (\ x -> Id (M x) (N x))
  sId {Γ} {Γs} {A} {As} {M} {N} Ms Ns = 
               ty (λ θs → Idc (red Ms θs) (red Ns θs)) 
                  (λ {θ1} {θ2} {α} {vθ1} {vθ2} vα → 
                     smap (λ { {._} (idValue α' α's)  → 
                             valuable 
                             (! (ev (red Ns vθ2)) 
                             ∘ (v≃0 (v∘ (tred As vθ2)
                                      (val≃ (sresp Ns vα)) 
                                      (val≃0 (v∘ (tred As vθ2)
                                           (val≃ (mresp (ssubst As vα) α's)) 
                                           (val≃0 (v! (tred As vθ2) (val≃ (sresp Ms vα))))))))
                             ∘ ev (red Ms vθ2))
                             (idValue _ (val≃0
                                           (v∘ (tred As vθ2) (val≃ (sresp Ns vα))
                                            (val≃0
                                             (v∘ (tred As vθ2) (val≃ (mresp (ssubst As vα) α's))
                                              (val≃0 (v! (tred As vθ2) (val≃ (sresp Ms vα))))))))) -- need Value≃ to be closed under ∘ and !
                             ({!!} ∘ subst-Id-d M N α _) 
                             FIXMEEval }) 
                          (λ _ → valuable≃ _ _ Refl))
  

  sRefl : {Γ : Set} {Γs : ValueTy Γ}
          {A : Γ -> Set} {As : Ty Γs A} 
          {M : (g : Γ) -> A g} (sM : Tm Γs As M) 
        -> Tm Γs (sId sM sM) (\ θ -> Refl{_}{M θ})
  sRefl {As = As} sM = tm (λ vθ → valuable (! (ev (red sM vθ)) ∘
                                              v≃0 (vRefl (tred As vθ) (val (red sM vθ))) ∘ ev (red sM vθ))
                                           (idValue _ (val≃0 (vRefl (tred As vθ) (val (red sM vθ))))) 
                                           {!!}  -- move the ev's to the other side and cancel, and then use (ev≃0 (vRefl (tred As vθ) (val (red sM vθ))))
                                           FIXMEEval)
                          (λ vα → valuable≃ _ _ Refl) -- there would need to be work here if the Value≃'s of Id didn't accept everything


-}