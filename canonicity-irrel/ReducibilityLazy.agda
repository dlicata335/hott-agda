{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude 
open Paths

module canonicity-irrel.ReducibilityLazy where

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

  -- meta-level equality: don't want homotopy stuff here
  Eq : ∀ {A : Set} -> A -> A -> Set
  Eq = Id

  Propo : (A : Set) -> Set
  Propo A = (M N : A) -> Eq M N

  U2 : Set
  U2 = Set

  -- semantic type value
  record ValuableTy (A : U2) : Set1 where
    field
     Valuable  : A -> Set
     propv  : ∀ {M} -> Propo (Valuable M)
     Valuable≃ : {M N : A} -> (Valuable M) -> (Valuable N) -> M ≃ N -> Set
     propv≃  : ∀ {M N} {vM : Valuable M} {vN : Valuable N} -> ∀ {α} -> Propo (Valuable≃ vM vN α)
     head-expand : ∀ {M N} -> Valuable N -> M ≃ N -> Valuable M
     head-expand≃ : {M N : A} 
                    {vM : Valuable M} {vN : Valuable N} {α β : M ≃ N}
                  -> Valuable≃ vM vN α
                  -> (eβ : β ≃ α)
                  -> Valuable≃ vM vN β
     vRefl  : {M : A} (vM : Valuable M) -> Valuable≃ vM vM (Refl{_}{M})
     v!     : {M N : A} {α : M ≃ N} {vM : Valuable M} {vN : Valuable N} 
               (vα : Valuable≃ vM vN α)
            -> Valuable≃ vN vM (! α)
     v∘     : {P M N : A} {β : N ≃ P} {α : M ≃ N} {vP : Valuable P} {vN : Valuable N} {vM : Valuable M} 
              (vβ : Valuable≃ vN vP β)(vα : Valuable≃ vM vN α)
            -> Valuable≃ vM vP (β ∘ α)

    retype≃1 : {M N : A} -> {vM1 : (Valuable M)} {vM2 : (Valuable M)} {vN : Valuable N} {α : M ≃ N}
            -> Valuable≃ vM1 vN α -> Valuable≃ vM2 vN α 
    retype≃1 {_}{_}{vM1}{vM2}{vN}{α} vα = subst (λ x → Valuable≃ x vN α) (propv vM1 vM2) vα
    -- NOTE: this means we wont' be able to run the algorithm in Agda,
    -- because this subst will be stuck.  
    -- but it would work in OTT

  open ValuableTy public

  -- simply typed terms; call by value
  record Map {A B : Set} (vA : ValuableTy A) (vB : ValuableTy B) (F : A -> B) : Set where
    constructor smap
    field
      mred  : {M : A} -> (Valuable vA M) -> Valuable vB (F M)
      mresp : {M N : A} {α : M ≃ N} {vM : Valuable vA M} {vN : Valuable vA N}
              (vα : Valuable≃ vA vM vN α)
           -> Valuable≃ vB (mred vM) (mred vN) (resp F α)
  open Map public

  -- record NT {A B : Set} {vA : ValuableTy A} {vB : ValuableTy B} {F G : A -> B} 
  --           (sf : Map vA vB F) (sg : Map vA vB G) (α : (x : A) -> F x ≃ G x)
  --           : Set where
  --   constructor nat
  --   field 
  --     unnat : {M : A} (vM : Valuable vA M)
  --          -> Valuable≃ vB (mred sf vM) (mred sg vM) (α M)

  record Ty {Γ : Set} (vΓ : ValuableTy Γ) (A : Γ -> Set) : Set1 where
    constructor ty 
    field
      tred   : {θ : Γ} -> (vθ : Valuable vΓ θ) -> ValuableTy (A θ)
      ssubst : {θ1 θ2 : Γ} {α : θ1 ≃ θ2}
               {vθ1 : Valuable vΓ θ1} {vθ2 : Valuable vΓ θ2}
               (vα  : Valuable≃ vΓ vθ1 vθ2 α)
            -> Map (tred vθ1) (tred vθ2) (subst A α)
-- FIXME: need to say that subst behaves right on compositions:
-- {x : A (θ _)} (vx : Valuable (tred sA (mred sθ .vθ1)) x) →
-- Valuable≃ (tred sA (mred sθ .vθ2))
-- (head-expand (tred sA (mred sθ .vθ2))
--  (mred (ssubst sA (mresp sθ vα)) vx)
--  (resp (λ f → f x) (subst-o A θ α)))
-- (mred (ssubst sA (mresp sθ vα)) vx)
-- (resp (λ f → f x) (subst-o A θ α))
  open Ty public

  record Tm {Γ : Set} (vΓ : ValuableTy Γ) {A : Γ -> Set} (As : Ty vΓ A) (M : (x : Γ) -> A x) : Set where
    constructor tm 
    field
      red   : {θ : Γ} -> (vθ : Valuable vΓ θ) -> Valuable (tred As vθ) (M θ)
      sresp : {θ1 θ2 : Γ} {α : θ1 ≃ θ2} {vθ1 : Valuable vΓ θ1} {vθ2 : Valuable vΓ θ2} 
              (vα : Valuable≃ vΓ vθ1 vθ2 α) 
             → Valuable≃ (tred As vθ2)
                         (mred (ssubst As vα) (red vθ1))
                         (red vθ2)
                         (respd M α)
  open Tm public

  mo : {A B C : Set} (As : ValuableTy A) (Bs : ValuableTy B) (Cs : ValuableTy C) 
         (f : A -> B) (g : B -> C)
       -> Map Bs Cs g
       -> Map As Bs f
       -> Map As Cs (g o f)
  mo As Bs Cs f g sg sf = smap (λ x → mred sg (mred sf x)) 
                               (λ {_}{_}{α} vα → head-expand≃ Cs (mresp sg (mresp sf vα)) (resp-o g f α))

  head-expand-map : {A B : Set} {vA : ValuableTy A} {vB : ValuableTy B} {F G : A -> B}
                  -> (sf : Map vA vB F)
                  -> (β : G ≃ F)
                  -> (βcomp : {x : A} (vx : Valuable vA x) 
                          -> Valuable≃ vB (head-expand vB (mred sf vx) (app≃ β)) (mred sf vx) (app≃ β)) 
                  -> Map vA vB G
  head-expand-map {vB = vB}{F}{G} sf β βcomp = smap (λ x → head-expand vB (mred sf x) (app≃ β)) 
                                                    (λ {M}{N}{α}{vM}{vN} vα → head-expand≃ vB (v∘ vB (v! vB (βcomp vN)) (v∘ vB (mresp sf vα) (βcomp vM))) 
                                                                              FIXMEChecked) -- naturality in syntax


  mto : {Γ Δ : Set} {sΓ : ValuableTy Γ} {sΔ : ValuableTy Δ}
         {θ : Γ -> Δ} {A : Δ -> Set}
       -> (sA : Ty sΔ A)
       -> (sθ : Map sΓ sΔ θ)
       -> Ty sΓ (A o θ)
  mto {θ = θ}{A = A} sA sθ = ty (λ vθ' → tred sA (mred sθ vθ')) 
                                (λ {_}{_}{α} vα → head-expand-map (ssubst sA (mresp sθ vα)) 
                                                                  (subst-o A θ α) FIXMETodo) -- need to put something in the signature about subst
  


