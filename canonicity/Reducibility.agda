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

  -- semantic type
  record SType (A : Set) : Set1 where
    field
     Value  : A -> Set
     Value≃ : {M N : A} -> Value M -> Value N -> M ≃ N -> Set
  open SType

  record Valuable {A : Set} (As : SType A) (M : A) : Set where
    constructor valuable 
    field
      val    : A
      isVal  : Value As val
      eval   : M ≃ val
      isEval : Eval eval
  open Valuable

  record Valuable≃ {A : Set} {As : SType A} {M N : A} (vM : Valuable As M) (vN : Valuable As N) (α : M ≃ N) : Set where
    constructor valuable≃
    field 
      val≃ : val vM ≃ val vN
      isVal≃ : Value≃ As (isVal vM) (isVal vN) val≃
      comm : eval vN ∘ α ∘ ! (eval vM) ≃ val≃
  open Valuable≃ 

  record STerm0 {A B : Set} (As : SType A) (Bs : SType B) (F : A -> B) : Set where
    constructor sterm0 
    field
      ob  : (M : A) -> Value As M -> Valuable Bs (F M)
      arr :  (M N : A) (α : M ≃ N) (vM : Value As M) (vN : Value As N)
          -> Value≃ As vM vN α 
          -> Valuable≃ (ob _ vM) (ob _ vN) (resp F α)

  
  -- examples

  Value× : {A B : Set} (As : SType A) (Bs : SType B)
                -> A × B -> Set 
  Value× As Bs (x , y) = Value As x × Value Bs y  -- really want them to be EQUAL to a pair

  Value×≃ : {A B : Set} (As : SType A) (Bs : SType B)
            {p1 : A × B} {p2 : A × B}
            (p1v : Value× As Bs p1) (p2v : Value× As Bs p2)
            (α : p1 ≃ p2) -> Set
  Value×≃ As Bs {p1 = x1 , y1} {p2 = x2 , y2} vp1 vp2 α = 
    Σ (λ (α1 : x1 ≃ x2) →
    Σ (λ (α2 : y1 ≃ y2) →
      (α ≃ resp2 _,_ α1 α2) ×   -- really want an equality
      Value≃ As (fst vp1) (fst vp2) α1 ×
      Value≃ Bs (snd vp1) (snd vp2) α2))
  


  id_ok : {A : Set} (As : SType A) -> STerm0 As As (\ x -> x)
  id_ok As = sterm0 (λ M vM → valuable M vM Refl evRefl) 
                    (λ _ _ α _ _ vα → valuable≃ α vα (resp-id α ∘ ∘-unit-l (resp (λ x → x) α)))

  o_ok : {A B C : Set} (As : SType A) (Bs : SType B) (Cs : SType C) 
         (f : A -> B) (g : B -> C)
       -> STerm0 Bs Cs g
       -> STerm0 As Bs f
       -> STerm0 As Cs (g o f)

  o_ok As Bs Cs f g (sterm0 go ga) (sterm0 fo fa) = 
    sterm0 (λ M vM → valuable (val (go (val (fo M vM)) (isVal (fo M vM)))) 
                              (isVal (go _ (isVal (fo _ vM)))) 
                              (eval (go _ (isVal (fo _ vM))) ∘ resp g (eval (fo M vM))) 
                              {!!}) 
           (λ M N α vM vN vα → valuable≃ (val≃ (ga _ _ (val≃ (fa M N α vM vN vα)) _ _ (isVal≃ (fa M N α vM vN vα))))
                                         (isVal≃
                                            (ga _ _ (val≃ (fa M N α vM vN vα)) _ _ (isVal≃ (fa M N α vM vN vα)))) 
                                         (comm
                                            (ga _ _ (val≃ (fa M N α vM vN vα)) _ _
                                             (isVal≃ (fa M N α vM vN vα)))
                                            ∘ {!!})) -- massage and use comm (fa M N α vM vN vα)

  _×s_ : {A B : Set} -> SType A -> SType B -> SType (A × B)
  As ×s Bs = record { Value = Value× As Bs;
                      Value≃ = Value×≃ As Bs}

  fst_ok : {A B : Set} (As : SType A) (Bs : SType B) -> STerm0 (As ×s Bs) As fst
  fst_ok As Bs = record { ob = λ {(M , N) (vM , vN) → valuable M vM Refl evRefl} ; 
                          arr = λ { (M1 , N1) (M2 , N2) α vM1 vM2 (α1 , α2 , αis , vα1 , vα2) -> 
                                valuable≃ α1 vα1 {!!} } -- resp fst (resp2 _,_ α1 α2) ≃ α1
                        }

  pair_ok : {Γ A B : Set} (Γs : SType Γ) (As : SType A) (Bs : SType B) 
            (M : Γ -> A) (N : Γ -> B)
          -> STerm0 Γs As M
          -> STerm0 Γs Bs N
          -> STerm0 Γs (As ×s Bs) (\ x -> M x , N x)
  pair_ok {Γ} {A} {B} Γs As Bs M N (sterm0 Mo Ma) (sterm0 No Na) = 
    sterm0 (λ g vg → valuable _ (isVal (Mo g vg) , isVal (No g vg)) 
                                (resp2 _,_ (eval (Mo g vg)) (eval (No g vg))) 
                                {!!}) 
           (λ g1 g2 α vg1 vg2 vα → valuable≃ (resp2 _,_ (val≃ (Ma g1 g2 α vg1 vg2 vα))
                                               (val≃ (Na g1 g2 α vg1 vg2 vα)))
                                             (val≃ (Ma _ _ _ _ _ vα) , 
                                                val≃ (Na _ _ _ _ _ vα) , 
                                                Refl , -- this MUST be Refl; this should be equality not equiv
                                                isVal≃ (Ma _ _ _ _ _ vα) , 
                                                isVal≃ (Na _ _ _ _ _ vα)) 
                                               {!!}) -- massage and use comm (Ma _ _ _ _ _ vα) and comm (Na _ _ _ _ _ vα)