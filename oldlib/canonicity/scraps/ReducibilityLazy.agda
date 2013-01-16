{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open Paths

module canonicity.ReducibilityLazy where

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
  data Eval : {A : Set} {M N : A} -> (M ≃ N) -> Set where
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

  -- simply typed terms; call by value
  record Map {A B : Set} (vA : ValuableTy A) (vB : ValuableTy B) (F : A -> B) : Set where
    constructor smap
    field
      mred  : {M : A} -> Valuable vA M -> Valuable vB (F M)
      mresp : {M N : A} {α : M ≃ N} {vM : Valuable vA M} {vN : Valuable vA N}
              (vα : Valuable≃ vA vM vN α)
           -> Valuable≃ vB (mred vM) (mred vN) (resp F α)
  open Map

  -- mred' : {A B : Set} {As : ValuableTy A} {Bs : ValuableTy B} {F : A -> B}
  --       -> Map As Bs F
  --       -> ({M : A} -> Valuable As M -> Valuable Bs (F M))
  -- mred' {As = As} {Bs = Bs} {F = F} (smap fo fa) sM  = 
  --                valuable (v (fo (val sM)))
  --                         (val (fo (val sM)))
  --                         (ev (fo (val sM)) 
  --                          ∘ resp (coe (evty Bs) o (F o (coe (! (evty As))))) (ev sM) 
  --                          ∘ resp (λ x → coe (evty Bs) (F x)) (! (coe-inv-1 (evty As)))) 
  --                         (FIXMEEval)

  -- mresp' : {A B : Set} {vA : ValuableTy A} {vB : ValuableTy B} {F : A -> B}
  --        -> (sF : Map vA vB F)
  --        -> {M N : A} {α : M ≃ N} {vM : Valuable vA M} {vN : Valuable vA N}
  --          (vα : Valuable≃ vA vM vN α)
  --          -> Valuable≃ vB (mred' sF vM) (mred' sF vN) (resp F α)
  -- mresp' = λ sF vα → valuable≃ _ (val≃ (mresp sF (val≃ vα)))
  --                                (ev≃ (mresp sF (val≃ vα)) ∘ {!ev≃ vα!}) -- and LOTS of massaging, including resp-by-id with coe-inv-1; checked on paper
  --                                FIXMEEval


  record Ty {Γ : Set} (vΓ : ValuableTy Γ) (A : Γ -> Set) : Set1 where
    constructor ty 
    field
      tred   : {θ : Γ} -> (vθ : Valuable vΓ θ) -> ValuableTy (A θ)
      ssubst : {θ1 θ2 : Γ} {α : θ1 ≃ θ2}
               {vθ1 : Valuable vΓ θ1} {vθ2 : Valuable vΓ θ2}
               (vα  : Valuable≃ vΓ vθ1 vθ2 α)
            -> Map (tred vθ1) (tred vθ2) (subst A α)
  open Ty

{-
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

-}

  record Tm {Γ : Set} (Γs : ValuableTy Γ) {A : Γ -> Set} (As : Ty Γs A) (M : (x : Γ) -> A x) : Set where
    constructor tm 
    field
      red   : {θ : Γ} -> (vθ : Valuable Γs θ) -> Valuable (tred As vθ) (M θ)
      sresp : {θ1 θ2 : Γ} {α : θ1 ≃ θ2} {vθ1 : Valuable Γs θ1} {vθ2 : Valuable Γs θ2} 
              (vα : Valuable≃ Γs vθ1 vθ2 α) 
             → Valuable≃ (tred As vθ2)
                         (mred (ssubst As vα) (red vθ1))
                         (red vθ2)
                         (respd M α)
  open Tm


  mid : {A : Set} (As : ValuableTy A) -> Map As As (\ x -> x)
  mid As = smap (λ vM → vM) 
                (λ vα → {!!}) -- head expand 

  mo : {A B C : Set} (As : ValuableTy A) (Bs : ValuableTy B) (Cs : ValuableTy C) 
         (f : A -> B) (g : B -> C)
       -> Map Bs Cs g
       -> Map As Bs f
       -> Map As Cs (g o f)
  mo As Bs Cs f g sg sf = 
    smap (λ vM → mred sg (mred sf vM) ) 
         (λ vα → {!mresp sg (mresp sf vα)!}) -- head expand

  mto : {Γ Δ : Set} {sΓ : ValuableTy Γ} {sΔ : ValuableTy Δ}
         {θ : Γ -> Δ} {A : Δ -> Set}
       -> (sA : Ty sΔ A)
       -> (sθ : Map sΓ sΔ θ)
       -> Ty sΓ (A o θ)
  mto sA sθ = ty (λ vθ' → tred sA (mred sθ vθ')) 
                 (λ vα → {!ssubst sA (mresp sθ vα) !}) -- head expand

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

{-
  -- "return" for valuabile types
  retty : ∀ {Γ} -> ValueTy Γ -> ValuableTy Γ
  retty v = valuablety _ v Refl evRefl
-}

  move : ∀ {A} -> (vA : ValuableTy A) -> (A -> vty vA)
  move vA = coe (evty vA)

  unmove : ∀ {A} -> (vA : ValuableTy A) -> (vty vA -> A)
  unmove vA = coe (! (evty vA))

{-
  valuable-unmove :  ∀ {A} (vA : ValuableTy A) -> ∀ {M} 
          -> Value (valty vA) M -> Valuable vA (unmove vA M)
  valuable-unmove vA vM = valuable _ vM (coe-inv-2 (evty vA)) FIXMEEval
-}

  head-expand : ∀ {A M N} {vA : ValuableTy A}
                -> (vN : Valuable vA N)
                -> (α : M ≃ N)
                -> Eval α 
                -> Valuable vA M
  head-expand {vA = vA} vN α e = valuable (v vN) (val vN) (ev vN ∘ resp (move vA) α) FIXMEEval

  head-expand≃ : ∀ {A M1 M2 N1 N2} {vA : ValuableTy A}
                -> (vN1 : Valuable vA N1) (vN2 : Valuable vA N2)
                -> (α1 : M1 ≃ N1) -> (ev1 : Eval α1) 
                -> (α2 : M2 ≃ N2) -> (ev2 : Eval α2)
                -> {β  : N1 ≃ N2}
                -> Valuable≃ vA vN1 vN2 β
                -> Valuable≃ vA (head-expand vN1 α1 ev1) (head-expand vN2 α2 ev2) (! α2 ∘ β ∘ α1)
  head-expand≃ = {!!}


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
              -> (vM : Valuable vΓ M) -> {N : _} -> Valuable (tred sA vM) N 
              -> ΣValue vΓ sA (M , N)
  
    data ΣValue≃ {Γ : Set} (vΓ : ValuableTy Γ) {A : Γ -> Set} (sA : Ty vΓ A) 
                 : {M N : (Σ A)} (vM : ΣValue vΓ sA M) (vN : ΣValue vΓ sA N) (α : M ≃ N) -> Set where
      cpair≃ : ∀ {M1 M2 α} {vM1 : Valuable vΓ M1} {vM2 : Valuable vΓ M2} 
              -> (vα : Valuable≃ vΓ vM1 vM2 α)
              -> ∀ {N1 N2 β} {vN1 : Valuable (tred sA vM1) N1} {vN2 : Valuable (tred sA vM2) N2 }
              -> Valuable≃ (tred sA vM2) (mred (ssubst sA vα) vN1)
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
    mfst sΓ sA = smap (λ { (valuable (M , N) (cpair vM vN) D _) → head-expand vM (resp fst D) FIXMEEval })
                      (λ { {P1}{P2}{αp}{valuable vp1 ._ evp1 _}{valuable vp2 ._ evp2 _} (valuable≃ (._) (cpair≃{._}{._}{_}{vM1}{vM2} vα vβ) D _) 
                         → {! head-expand≃ vM1 vM2 (resp fst evp1) FIXMEEval (resp fst evp2) FIXMEEval vα !} }) -- valuable≃ _ (val≃ vα) (ev≃ vα ∘ {!? ∘ (resp fst D) ∘ ?!}) FIXMEEval}) -- head-expand
                    

    svar : {Γ : Set} (sΓ : ValuableTy Γ) {A : Γ -> Set} (sA : Ty sΓ A) 
        -> Tm (Σc sΓ sA) (mto sA (mfst sΓ sA)) snd
    svar sΓ sA = tm (\ { (valuable (M , N) (cpair vM vN) D _) → {!vN!} }) -- STUCK: looks like the type depends on the evaluation derivation
                    {!!}

{-
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

