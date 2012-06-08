{-# OPTIONS --type-in-type #-}

open import lib.Prelude 
open Paths

module canonicity-prop.Reducibility where

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

{-
  test : {A B : Set} (C : B -> Set) (f : A -> B)
         {M N : A} (α : M ≃ N)
         {E' : Id (subst (λ x → C (f x)) α) (subst C (resp f α))}
         -> (subst-o C f α) ≃ E'
  test C f Refl = {!!}
-}

  -- needs to classify individual steps, not just evaluation to a value.
  -- or we could use a different judgement in head-expand
  data Eval : {A : Set} {M N : A} -> M ≃ N -> Set where
    evRefl : {A : _} {M : A} -> Eval (Refl{_}{M})
    ev-resp-o : {A B C : Set} (g : B -> C) (f : A -> B)
                {M N : A} (α : M ≃ N) -> Eval (resp-o g f α)
    ev-app≃ : ∀ {A} {B : A -> Set} {f g : (x : A) -> B x} 
              -> (α : Id f g) -> {x : A} -> Eval (app≃ α {x})
    ev-subst-o : {A B : Set} (C : B -> Set) (f : A -> B)
                 {M N : A} (α : M ≃ N)
                 -> Eval (subst-o C f α)
    ev-naturality1 : {A B : Set} {F G : A -> B}
                     -> (β : G ≃ F) 
                     -> {M N : A} (α : M ≃ N) 
                     -> Eval (naturality1 β α)
    ev-resp-id : {A : Set} {M N : A} (α : Id M N) -> Eval (resp-id α)
    ev-subst-univ : {A B : Set} (w : AEq A B) -> Eval (subst-univ w)
    ev-! : {a : Set} {x y : a} -> {E : Id x y} -> Eval E -> Eval (! E)
    ev-resp : {A B : Set} {M N : A}{E : M ≃ N} (f : A -> B) -> Eval E -> Eval (resp f E)
    ev-snd≃ : {A : Set} {B : A -> Set} {p q : Σ B} -> {E : p ≃ q} -> Eval E -> Eval (snd≃ E)
    FIXMEEval : {A : Set} {M N : A} -> {α : M ≃ N} -> Eval α

{-
  eval-uip : {A : Set} {M : A} {E : M ≃ M} -> Eval E -> E ≃ Refl -- fixme and is an eval?
  eval-uip ev = {! ev!}
 
  eval-unique : {A : Set} {M N : A} {E1 E2 : M ≃ N} -> Eval E1 -> Eval E2 -> E1 ≃ E2 -- fixme and is an eval?
  eval-unique evRefl x' = {!x'!}
  eval-unique (ev-resp-o g f α) x' = {!x'!}
  eval-unique (ev-app≃ α) x' = {!!}
  eval-unique (ev-subst-o C f α) x' = {!!}
  eval-unique (ev-naturality1 β α) x' = {!!}
  eval-unique (ev-! y) x' = {!!}
  eval-unique (ev-resp-id f) x' = {!!}
  eval-unique (ev-resp f y) x' = {!!}
  eval-unique (ev-snd≃ y) x' = {!!}
  eval-unique (ev-subst-univ w) x' = {!!}
  eval-unique FIXMEEval x' = {!!}
{-
  eval-unique {E1 = Refl}  ev2 = {!!}
  eval-unique (ev-resp-o g f α) ev2 = {!jay1 (\ N α -> (E2 : _) -> Id (resp-o g f α) !}
  eval-unique (ev-app≃ Refl) ev2 = {!!}
  eval-unique (ev-subst-o C f Refl) ev2 = {!!}
  eval-unique (ev-naturality1 Refl Refl) ev2 = {!!}
  eval-unique (ev-resp-id Refl) ev2 = {!!}
  eval-unique (ev-! {E = Refl} ev) ev2 = {!!}
  eval-unique (ev-resp {E = Refl} f ev) ev2 = {!!}
  eval-unique (ev-snd≃ {E = Refl} y) ev2 = {!!}
  eval-unique (ev-subst-univ w) ev2 = {! ev2!}
  eval-unique FIXMEEval ev2 = FIXMETodo
-}  
-}

  -- semantic type value
  record CTy (A : U2) : Set1 where
    field
     Red  : A -> Set
     propr  : ∀ {M} -> Propo (Red M)
     Red≃ : {M N : A} -> (Red M) -> (Red N) -> M ≃ N -> Set
     propr≃  : ∀ {M N} {vM : Red M} {vN : Red N} -> ∀ {α} -> Propo (Red≃ vM vN α)
     head-expand : ∀ {M N} -> Red N -> (E : M ≃ N) -> Eval E -> Red M
     head-expand≃ : {M N : A} 
                    {vM : Red M} {vN : Red N} {α β : M ≃ N}
                  -> Red≃ vM vN α
                  -> (E : β ≃ α)
                  -> Eval E
                  -> Red≃ vM vN β
     rRefl  : {M : A} (rM : Red M) -> Red≃ rM rM (Refl{_}{M})
     r!     : {M N : A} {α : M ≃ N} {rM : Red M} {rN : Red N} 
               (rα : Red≃ rM rN α)
            -> Red≃ rN rM (! α)
     r∘     : {P M N : A} {β : N ≃ P} {α : M ≃ N} {rP : Red P} {rN : Red N} {rM : Red M} 
              (rβ : Red≃ rN rP β)(rα : Red≃ rM rN α)
            -> Red≃ rM rP (β ∘ α)
     eval-red≃ : {M N : A} {rM : Red M} {rN : Red N} 
                      (α : M ≃ N) -> Eval α -> Red≃ rM rN α

    retype≃1 : {M N : A} -> {rM1 : (Red M)} {rM2 : (Red M)} {rN : Red N} {α : M ≃ N}
            -> Red≃ rM1 rN α -> Red≃ rM2 rN α 
    retype≃1 {_}{_}{rM1}{rM2}{rN}{α} rα = subst (λ x → Red≃ x rN α) (propr rM1 rM2) rα
    -- NOTE: this means we wont' be able to run the algorithm in Agda,
    -- because this subst will be stuck.  
    -- but it would work in OTT

  open CTy public

  -- simply typed terms; call by ralue
  record Map {A B : Set} (rA : CTy A) (rB : CTy B) (F : A -> B) : Set where
    constructor smap
    field
      mred  : {M : A} -> (Red rA M) -> Red rB (F M)
      mresp : {M N : A} {α : M ≃ N} {rM : Red rA M} {rN : Red rA N}
              (rα : Red≃ rA rM rN α)
           -> Red≃ rB (mred rM) (mred rN) (resp F α)
  open Map public

  record Ty {Γ : Set} (rΓ : CTy Γ) (A : Γ -> Set) : Set1 where
    constructor ty 
    field
      tred   : {θ : Γ} -> (rθ : Red rΓ θ) -> CTy (A θ)
      ssubst : {θ1 θ2 : Γ} {α : θ1 ≃ θ2}
               {rθ1 : Red rΓ θ1} {rθ2 : Red rΓ θ2}
               (rα  : Red≃ rΓ rθ1 rθ2 α)
            -> Map (tred rθ1) (tred rθ2) (subst A α)
  open Ty public

  record Tm {Γ : Set} (rΓ : CTy Γ) {A : Γ -> Set} (As : Ty rΓ A) (M : (x : Γ) -> A x) : Set where
    constructor tm 
    field
      red   : {θ : Γ} -> (rθ : Red rΓ θ) -> Red (tred As rθ) (M θ)
      sresp : {θ1 θ2 : Γ} {α : θ1 ≃ θ2} {rθ1 : Red rΓ θ1} {rθ2 : Red rΓ θ2} 
              (rα : Red≃ rΓ rθ1 rθ2 α) 
             → Red≃ (tred As rθ2)
                    (mred (ssubst As rα) (red rθ1))
                    (red rθ2)
                    (respd M α)
  open Tm public

  mo : {A B C : Set} (As : CTy A) (Bs : CTy B) (Cs : CTy C) 
         (f : A -> B) (g : B -> C)
       -> Map Bs Cs g
       -> Map As Bs f
       -> Map As Cs (g o f)
  mo As Bs Cs f g sg sf = smap (λ x → mred sg (mred sf x)) 
                               (λ {_}{_}{α} rα → head-expand≃ Cs (mresp sg (mresp sf rα)) (resp-o g f α) (ev-resp-o g f α))

  head-expand-map : {A B : Set} {rA : CTy A} {rB : CTy B} {F G : A -> B}
                  -> (sf : Map rA rB F)
                  -> (β : G ≃ F) (E : Eval β)
                  -> Map rA rB G
  head-expand-map {rB = rB}{F}{G} sf β βcomp = 
    smap (λ x → head-expand rB (mred sf x) (app≃ β) (ev-app≃ β)) 
         (λ {M}{N}{α}{rM}{rN} rα → head-expand≃ rB 
                                                (r∘ rB (r! rB (eval-red≃ rB (app≃ β {N}) (ev-app≃ β)))
                                                      (r∘ rB (mresp sf rα) 
                                                             (eval-red≃ rB (app≃ β {M}) (ev-app≃ β)))) 
                                                (naturality1 β α) (ev-naturality1 β α)) -- naturality in syntax

  mto : {Γ Δ : Set} {sΓ : CTy Γ} {sΔ : CTy Δ}
         {θ : Γ -> Δ} {A : Δ -> Set}
       -> (sA : Ty sΔ A)
       -> (sθ : Map sΓ sΔ θ)
       -> Ty sΓ (A o θ)
  mto {θ = θ}{A = A} sA sθ = ty (λ rθ' → tred sA (mred sθ rθ')) 
                                (λ {_}{_}{α} rα → head-expand-map (ssubst sA (mresp sθ rα)) 
                                                                  (subst-o A θ α) (ev-subst-o A θ α))
  


