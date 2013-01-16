open import homotopy.Paths
open PM
open import homotopy.Prods

module homotopy.misc.Quotient where

  -- FIXME: really want to do weak ω groupoid?

  record Gpd : Set1 where
   field
    Ob   : Set
    Arr  : Ob -> Ob -> Set
    id   : {x : Ob} -> Arr x x
    inv  : {x y : Ob} -> Arr x y -> Arr y x
    comp : {x y z : Ob} -> Arr x y -> Arr y z -> Arr x z
  open Gpd public

  ↑_ : (A : Set) -> Gpd 
  ↑_ A = record { Ob = A; Arr = Id; id = Refl; inv = sym; comp = trans }

  record Func (A B : Gpd) : Set where
    constructor func
    field
      _·_ : Ob A -> Ob B
      _⊙_ : ∀ {x y : Ob A} -> Arr A x y -> Arr B (_·_ x) (_·_ y)
  open Func

  idfunc : ∀ {A} -> Func A A
  idfunc = func (\ x -> x) (\ x -> x)

  _∘f_ : ∀ {A B C} -> Func B C -> Func A B -> Func A C
  F ∘f G = func (\ x -> F · (G · x)) (λ p → F ⊙ (G ⊙ p))

  module Q where
    private 
      record ↓i (G : Gpd) : Set where
        constructor [_]i 
        field
          rep : Ob G

      postulate 
        ↓eq : {G : Gpd} {x y : Ob G} -> Arr G x y -> Id{↓i G} ([ x ]i) ([ y ]i)

    ↓_ : Gpd -> Set
    ↓ G = ↓i G

    qintro : {G : Gpd} -> Func G (↑ ↓ G)
    qintro = func (λ x → [ x ]i) ↓eq 

    qrec   : {G : Gpd} {A : Set} -> Func G (↑ A) -> (↓ G -> A)
    qrec F x = F · (↓i.rep x)

    postulate
      qβa : {G : Gpd} {A : Set} -> (F : Func G (↑ A)) 
            -> ∀ {x1 x2} (p : Arr G x1 x2) -> (resp (qrec F) (qintro ⊙ p)) ≃ (F ⊙ p)

  open Q 

  [_]   : {G : Gpd} -> Ob G -> ↓ G
  [ a ] = qintro · a

  [[_]] : {G : Gpd} {x y : Ob G} -> Arr G x y -> Id{↓ G} [ x ] [ y ]
  [[ p ]] = qintro ⊙ p

  qelim : {G : Gpd} {P : ↓ G -> Set}
          (f : (x : Ob G) -> P [ x ])
          (fa : {x y : Ob G} -> (p : Arr G x y) -> subst P [[ p ]] (f x) ≃ (f y))
          -> (x : ↓ G) -> P x
  qelim {G}{P} f fa x = (snd (qrec {G} {Σ (λ x' → P x')} (func (λ x' → [ x' ] , f x') (λ {a} {b} p → pairPath [[ p ]] (fa p))) x))

  -- holds definitionally
  qβ1 : {G : Gpd} {A : Set} {F : Func G (↑ A)} 
     -> {x : Ob G} -> qrec F [ x ] ≃ (F · x)  
  qβ1 = Refl 

  qβ2 : {G : Gpd} {A : Set} -> (F : Func G (↑ A)) 
      -> ∀ {x1 x2} (p : Arr G x1 x2) -> (resp (qrec F) [[ p ]]) ≃ (F ⊙ p)
  qβ2 = qβa

  -- commuting conversion for qrec; holds definitionally
  qcomm : {G1 : Gpd} {A : Set} {F : Func G1 (↑ A)} 
     -> {x : ↓ G1} -> Id{↓ ↑ A} [ qrec F x ] (qrec (qintro ∘f F) x)
  qcomm = Refl

  module Weird where
    postulate 
      ext : {A B : Set} {h h' : A -> B} -> ((x : A) -> Id (h x) (h' x)) -> Id h h'
  
    -- FIXME: should NOT be provable!
    ignore : {G1 : Gpd} {A : Set} {f : Ob G1 -> A} 
           {a1 : ∀ {x y : Ob G1} -> Arr G1 x y -> (f x) ≃ (f y)}
           {a2 : ∀ {x y : Ob G1} -> Arr G1 x y -> (f x) ≃ (f y)}
           -> Id{↓ G1 -> A} (qrec (func f a1)) (qrec (func f a2))
    ignore {f = f} {a1 = a1} = ext (qelim (\ _ -> Refl) {!!})
  
    -- naturality square?
    respcong : ∀ {A B} -> {f g : A -> B} -> (p : f ≃ g) 
             -> ∀ {x y} -> (q : x ≃ y)
             ->  trans (sym (resp (\ f -> f x) p)) (trans (resp f q) (resp (\ f -> f y) p))  ≃ resp g q
    respcong Refl Refl = Refl
  
    UIP? : {G1 : Gpd} {A : Set} {f : Ob G1 -> A} 
           {a1 : ∀ {x y : Ob G1} -> Arr G1 x y -> (f x) ≃ (f y)}
           {a2 : ∀ {x y : Ob G1} -> Arr G1 x y -> (f x) ≃ (f y)}
           -> ∀ {x y} -> (p : Arr G1 x y) -> a1 p ≃ a2 p
    UIP? {G1}{A}{f = f}{a1 = a1} {a2 = a2} p = bad  where
      F1 : Func G1 (↑ A)
      F1 = (func f a1)
      F2 : Func G1 (↑ A)
      F2 = (func f a2)
      fact1 : Id{↓ G1 -> A} (qrec F1) (qrec F2)
      fact1 = (ignore{a1 = a1}{a2 = a2})
      fact2 : Id (resp (qrec F1) [[ p ]]) (resp (qrec F2) [[ p ]]) -- type checks because the action on objects is the same
      fact2 = {!resp (\ (f : ↓ G1 -> A) -> resp f [[ p ]]) fact1!} -- but can't prove this this way because the predicate you'd need is dependent
      fact2' : Id (resp (qrec F1) [[ p ]]) (resp (qrec F2) [[ p ]])
      fact2' = trans (trans (qβ2 F1 p) {!!}) (respcong fact1 [[ p ]]) -- FIXME: what's going on here?
      bad : a1 p ≃ a2 p
      bad  = trans (sym (qβ2 F1 p)) (trans fact2 ((qβ2 F2 p)))

  module Adjunction where
    
    -- ↓ and ↑ are an adjunction between Gpd and Set
    ↓a : ∀ {G1 G2} -> Func G1 G2 -> (↓ G1 -> ↓ G2)
    ↓a F = qrec (func (λ x → [ F · x ]) (λ p → [[ F ⊙ p ]]))

    ↑a : ∀ {A B} -> (A -> B) -> Func (↑ A) (↑ B) 
    ↑a f = func f (resp f)

    -- qrec is one direction of the action on homsets

    hom1 : {G : Gpd} {A : Set} -> Func G (↑ A) -> (↓ G -> A)
    hom1 = qrec

    hom2 : {G : Gpd} {A : Set} -> (↓ G -> A) -> Func G (↑ A)
    hom2 f = ↑a f ∘f qintro 

    -- FIXME: why is it enough to check the 1-cells?
    comp1 : {G : Gpd} {A : Set} -> (f : (↓ G -> A)) -> (x : _) -> (hom1 (hom2 f)) x ≃ f x
    comp1 f x = Refl

    comp1' : {G : Gpd} {A : Set} -> (f : (↓ G -> A)) -> (hom1 (hom2 f)) ≃ f
    comp1' f = {!!}

    comp2 : {G : Gpd} {A : Set} -> (f : Func G (↑ A)) -> (hom2 (hom1 f)) ≃ f
    comp2 f = {!!}

    -- FIXME: inherently natural in G and A?

  -- ↓ ↑ A ≃ A
  module Retraction where
    left : ∀ {A} -> A -> ↓ ↑ A
    left x = [ x ]

    right : ∀ {A} -> ↓ ↑ A -> A
    right x = qrec idfunc x

    ↓↑β : ∀ {A} {x : A}-> qrec idfunc [ x ] ≃ x
    ↓↑β = Refl

    comp1 : ∀ {A} {x : A} -> (right (left x)) ≃ x
    comp1 = Refl

    ↓↑η : ∀ {A} {x : ↓ ↑ A} -> x ≃ qrec qintro x
    ↓↑η = Refl

    comp2 : ∀ {A} {x : ↓ ↑ A} -> (left (right x)) ≃ x
    comp2 = Refl -- ≃ [ qrec idfunc x ] ≃ qrec (qintro ∘f idfunc) x ≃ qrec qintro x ≃ x 