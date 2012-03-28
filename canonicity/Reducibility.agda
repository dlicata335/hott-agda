{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open Paths

module canonicity.Reducibility where

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

  -- semantic closed type
  record CTy (A : Set) : Set1 where
    field
     Value  : A -> Set
     Value≃ : {M N : A} -> Value M -> Value N -> M ≃ N -> Set
  open CTy

  record Valuable {A : Set} (As : CTy A) (M : A) : Set where
    constructor valuable 
    field
      v    : A
      sv   : Value As v
      ev   : M ≃ v
      eval : Eval ev
  open Valuable

  record Valuable≃ {A : Set} {As : CTy A} {M N : A} (vM : Valuable As M) (vN : Valuable As N) (α : M ≃ N) : Set where
    constructor valuable≃
    field 
      v≃   : v vM ≃ v vN
      sv≃  : Value≃ As (sv vM) (sv vN) v≃
      comm : ev vN ∘ α ∘ ! (ev vM) ≃ v≃
      -- FIXME: need comm to be in Eval? check case for type formation for Id  
  open Valuable≃ 

  -- simply typed terms
  record Map {A B : Set} (As : CTy A) (Bs : CTy B) (F : A -> B) : Set where
    constructor smap
    field
      mred  : {M : A} -> Value As M -> Valuable Bs (F M)
      mresp : {M N : A} {α : M ≃ N} {vM : Value As M} {vN : Value As N}
              (vα : Value≃ As vM vN α)
           -> Valuable≃ (mred vM) (mred vN) (resp F α)
  open Map

  record Ty {Γ : Set} (Γs : CTy Γ) (A : Γ -> Set) : Set1 where
    constructor ty 
    field
      tred   : {θ : Γ} -> (vθ : Value Γs θ) -> CTy (A θ)
      ssubst : {θ1 θ2 : Γ} {α : θ1 ≃ θ2}
               {vθ1 : Value Γs θ1} {vθ2 : Value Γs θ2}
               (vα  : Value≃ Γs vθ1 vθ2 α)
            -> Map (tred vθ1) (tred vθ2) (subst A α)
  open Ty

  record Tm {Γ : Set} (Γs : CTy Γ) {A : Γ -> Set} (As : Ty Γs A) (M : (x : Γ) -> A x) : Set where
    constructor tm 
    field
      red   : {θ : Γ} -> (vθ : Value Γs θ) -> Valuable (tred As vθ) (M θ)
{-
      sresp : {θ1 θ2 : Γ} {α : θ1 ≃ θ2} {vθ1 : Value Γs θ1} {vθ2 : Value Γs θ2} (vα : Value≃ Γs vθ1 vθ2 α) 
             → Valuable≃ {!!} -- {! (Map.ob (OType.arr As _ _ _ vθ1 vθ2 vα) (M θ1) (ob _ vθ1) ) !}
                         (red vθ2)
                         (respd M α)
-}
  open Tm

  -- examples

  id_ok : {A : Set} (As : CTy A) -> Map As As (\ x -> x)
  id_ok As = smap (λ vM → valuable _ vM Refl evRefl) 
                 (λ {_}{_}{α} vα → valuable≃ _ vα (resp-id α ∘ ∘-unit-l (resp (λ x → x) α)))

  o_ok : {A B C : Set} (As : CTy A) (Bs : CTy B) (Cs : CTy C) 
         (f : A -> B) (g : B -> C)
       -> Map Bs Cs g
       -> Map As Bs f
       -> Map As Cs (g o f)
  o_ok As Bs Cs f g (smap go ga) (smap fo fa) = 
    smap (λ vM → valuable _ 
                           (sv (go (sv (fo vM)))) 
                           (ev (go (sv (fo vM))) ∘ resp g (ev (fo vM))) 
                           {!!}) 
           (λ vα → 
             valuable≃ _
                       (sv≃ (ga (sv≃ (fa vα)))) 
                       (comm (ga (sv≃ (fa vα))) ∘ {!!})) -- massage and use comm (fa M N α vM vN vα)

  Value× : {A B : Set} (As : CTy A) (Bs : CTy B)
                -> A × B -> Set 
  Value× As Bs (x , y) = Value As x × Value Bs y  -- really want them to be EQUAL to a pair

  Value×≃ : {A B : Set} (As : CTy A) (Bs : CTy B)
            {p1 : A × B} {p2 : A × B}
            (p1v : Value× As Bs p1) (p2v : Value× As Bs p2)
            (α : p1 ≃ p2) -> Set
  Value×≃ As Bs {p1 = x1 , y1} {p2 = x2 , y2} vp1 vp2 α = 
    Σ (λ (α1 : x1 ≃ x2) →
    Σ (λ (α2 : y1 ≃ y2) →
      (α ≃ resp2 _,_ α1 α2) ×   -- really want an equality
      Value≃ As (fst vp1) (fst vp2) α1 ×
      Value≃ Bs (snd vp1) (snd vp2) α2))

  _×c_ : {A B : Set} -> CTy A -> CTy B -> CTy (A × B)
  As ×c Bs = record { Value = Value× As Bs;
                      Value≃ = Value×≃ As Bs}

  fst_ok : {A B : Set} (As : CTy A) (Bs : CTy B) -> Map (As ×c Bs) As fst
  fst_ok As Bs = smap (λ { {(M , N)} (vM , vN) → valuable M vM Refl evRefl})
                     (λ { {(M1 , N1)} {(M2 , N2)} {α} {vM1} {vM2} (α1 , α2 , αis , vα1 , vα2) -> 
                                valuable≃ α1 vα1 {!!} } -- resp fst (resp2 _,_ α1 α2) ≃ α1
                     )

  pair_ok : {Γ A B : Set} (Γs : CTy Γ) (As : CTy A) (Bs : CTy B) 
            (M : Γ -> A) (N : Γ -> B)
          -> Map Γs As M
          -> Map Γs Bs N
          -> Map Γs (As ×c Bs) (\ x -> M x , N x)
  pair_ok {Γ} {A} {B} Γs As Bs M N (smap Mo Ma) (smap No Na) = 
    smap (λ vg → valuable _ (sv (Mo vg) , sv (No vg)) 
                            (resp2 _,_ (ev (Mo vg)) (ev (No vg))) 
                            {!!}) 
           (λ vα → valuable≃ _
                             (_ , 
                              _ , 
                              Refl , -- this MUST be Refl; this should be equality not equiv
                              sv≃ (Ma vα) , 
                              sv≃ (Na vα)) 
                             {!!}) -- massage and use comm (Ma vα) and comm (Na vα)

  -- Never use subst/resp for this!
  data IdValue {A : Set} {As : CTy A} {M N : A} (vM : Valuable As M) (vN : Valuable As N) : 
                Id M N -> Set where
       idValue : (α : v vM ≃ v vN) 
               -> Value≃ As (sv vM) (sv vN) α
               -> IdValue vM vN (! (ev vN) ∘ α ∘ ev vM)

  Idc : {A : Set} {As : CTy A} {M N : A} (vM : Valuable As M) (vN : Valuable As N) -> CTy (Id M N)
  Idc vM vN = record { Value = IdValue vM vN; 
                       Value≃ = λ _ _ _ → Unit }
  
  IdTy : {Γ : Set} {Γs : CTy Γ}
         {A : Γ -> Set} {As : Ty Γs A} 
         {M N : (g : Γ) -> A g} (Ms : Tm Γs As M) (Ns : Tm Γs As N) 
         -> Ty Γs (\ x -> Id (M x) (N x))
  IdTy {Γ} {Γs} {A} {As} {M} {N} Ms Ns = ty (λ θs → Idc (red Ms θs) (red Ns θs)) 
                  (λ {θ1} {θ2} {α} {vθ1} {vθ2} vα → 
                     smap (λ {α'} α's → valuable 
                                        (! (ev (red Ns vθ2)) ∘ {!!} ∘ ev (red Ms vθ2))
                                        (idValue _ {!!}) 
                                        ({!respd N α!} ∘ subst-Id-d M N α α') 
                                        {!!}) 
                          (λ _ → valuable≃ _ _ Refl))
  
