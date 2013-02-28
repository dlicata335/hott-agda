-- some sketchy thoughts on quotients of groupoids 

{-# OPTIONS --without-K --type-in-type #-}

open import lib.Paths

open import lib.Prods
open import lib.Nat 
open NatM using (_+_)

module lib.Quotient where

  UIP : Set -> Set
  UIP A = (x : A) (p : Id x x) -> Id p Refl

  Ident : ∀ {A} -> (A -> A -> Set) -> Set
  Ident Arr = ∀ {x} -> Arr x x

  Inv : ∀ {A} -> (A -> A -> Set) -> Set
  Inv Arr = ∀ {x y} -> Arr x y -> Arr y x

  Comp : ∀ {A} -> (A -> A -> Set) -> Set
  Comp Arr = ∀ {x y z} -> Arr x y -> Arr y z -> Arr x z

  record Gpd : Set1 where
   field
    Ob   : Set
    Arr  : Ob -> Ob -> Set
    id   : ∀ {x} -> Arr x x
    inv  : ∀ {x y} -> Arr x y -> Arr y x
    comp : ∀ {x y z} -> Arr x y -> Arr y z -> Arr x z
    set  : ∀ {x y} -> UIP (Arr x y)

  open Gpd public

  ↑_ : (A : Set) -> Gpd 
  ↑_ A = record { Ob = A; Arr = Id; id = Refl; inv = sym; comp = trans }

  ActionOnArrows : (A B : Gpd) -> (f : Ob A -> Ob B) -> Set
  ActionOnArrows A B _·_ = ∀ {x y} -> Arr A x y -> Arr B (_·_ x) (_·_ y)

  record Func (A B : Gpd) : Set where
    constructor func
    field
      _·_ : Ob A -> Ob B
      _⊙_ : ActionOnArrows A B _·_
      -- FIXME: equations
  open Func

  idfunc : ∀ {A} -> Func A A
  idfunc = func (\ x -> x) (\ x -> x)

  _∘f_ : ∀ {A B C} -> Func B C -> Func A B -> Func A C
  F ∘f G = func (\ x -> F · (G · x)) (λ p → F ⊙ (G ⊙ p))

  module Q where
    private 
      data ↓i (G : Gpd) : Set where
        [_]i  : Ob G -> ↓i G

    ↓_ : Gpd -> Set
    ↓ G = ↓i G

    [_]   : {G : Gpd} -> Ob G -> ↓ G
    [ a ] = [ a ]i

    postulate
      -- FIXME: should be an iso!
      [[_]] : {G : Gpd} {x y : Ob G} -> Arr G x y -> Id{↓ G} [ x ] [ y ]

    qelim : {G : Gpd} {P : ↓ G -> Set}
            (f : (x : Ob G) -> P [ x ])
            (fa : {x y : Ob G} -> (p : Arr G x y) -> subst P [[ p ]] (f x) ≃ (f y))
            -- FIXME equations?
            -> (x : ↓ G) -> P x
    qelim {G}{P} f _ [ x ]i = f x

    -- could be defined 
    -- to be qelim {P = λ _ → A} (_·_ F) (\ {x}{y}p -> trans (resp (\ f -> f (F · x)) ((subst-constant [[ p ]]))) (F ⊙ p)) x
    -- but that gets hard to read
    qrec   : {G : Gpd} {A : Set} -> Func G (↑ A) -> (↓ G -> A)
    qrec {A = A} F [ x ]i = F · x

    postulate
      qβa : {G : Gpd} {A : Set} -> (F : Func G (↑ A)) 
           -> ∀ {x1 x2} (p : Arr G x1 x2) -> (resp (qrec F) ([[ p ]])) ≃ (F ⊙ p)
      -- FIXME: dependent version?

  open Q 

  qintro : {G : Gpd} -> Func G (↑ ↓ G)
  qintro = func (λ x → [ x ]) [[_]] 

  -- holds definitionally
  qβ1 : {G : Gpd} {A : Set} {F : Func G (↑ A)} 
     -> {x : Ob G} -> qrec F [ x ] ≃ (F · x)  
  qβ1 = Refl 

  qβ2 : {G : Gpd} {A : Set} -> (F : Func G (↑ A)) 
      -> ∀ {x1 x2} (p : Arr G x1 x2) -> (resp (qrec F) [[ p ]]) ≃ (F ⊙ p)
  qβ2 = qβa

  -- a commuting conversion for qrec; check that this holds
  qcomm : {G1 : Gpd} {A : Set} {F : Func G1 (↑ A)} 
     -> {x : ↓ G1} -> Id{↓ ↑ A} [ qrec F x ] (qrec (qintro ∘f F) x)
  qcomm = {!!}

  module Weird where
    postulate 
      ext : {A B : Set} {h h' : A -> B} -> ((x : A) -> Id (h x) (h' x)) -> Id h h'
  
  {-
    -- FIXME: should NOT be provable!
    ignore : {G1 : Gpd} {A : Set} {f : Ob G1 -> A} 
           {a1 : ∀ {x y : Ob G1} -> Arr G1 x y -> (f x) ≃ (f y)}
           {a2 : ∀ {x y : Ob G1} -> Arr G1 x y -> (f x) ≃ (f y)}
           -> Id{↓ G1 -> A} (qrec (func f a1)) (qrec (func f a2))
    ignore {f = f} {a1 = a1}{a2 = a2} = ext (qelim (\ _ -> Refl) 
      (λ {x} {y} p → trans (fire-subst (qrec F1) (qrec F2){_}{_}{[[ p ]]}{_}) {!!})) where -- need (a1 p) = (a2 p), good
      F1 = (func f a1)
      F2 = (func f a2)
  -}

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

  {-
    comp1 : {G : Gpd} {A : Set} -> (f : (↓ G -> A)) -> (x : _) -> (hom1 (hom2 f)) x ≃ f x
    comp1 f x = qelim {P = \ x ->  (hom1 (hom2 f)) x ≃ f x} (\ _ -> Refl) 
                      (\ {a}{b} p -> trans
                                       (fire-subst
                                        (qrec (func (λ x0 → f [ x0 ]) (λ p' → resp f [[ p' ]]))) f {_} {_}
                                        {[[ p ]]} {Refl})
                                       {!!}) x -- β2 and then collapse inverses
  -}

    comp2 : {G : Gpd} {A : Set} -> (f : Func G (↑ A)) -> (hom2 (hom1 f)) ≃ f
    comp2 f = {!Refl!}  -- works by β2

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

  {- FIXME fire-subst
    -- [ qrec idfunc x ] ≃ x 
    comp2 : ∀ {A} {x : ↓ ↑ A} -> (left (right x)) ≃ x
    comp2 {A}{x} = qelim {P = \ x -> (left (right x)) ≃ x} (\ _ -> Refl) (λ {a} {b} p →
                                                                               trans
                                                                               (fire-subst (λ x' → [ qrec idfunc x' ]) (λ x' → x') {_} {_}
                                                                                {[[ p ]]} {Refl})
                                                                               {!!}) x where -- β2, sts, cancel inverses
          sts : {a b : A}{p : a ≃ b} -> Id {Id {↓ ↑ A} [ a ] [ b ]} (resp (λ x' → [ qrec idfunc x' ]) [[ p ]]) [[ p ]]
          sts {p = Refl} = {!!}  -- [[ ]] preserves Refl; resp anything on Refl is Refl
  -}

  module Examples where

    module Interval where
      data Endpoint : Set where
        zero : Endpoint
        one : Endpoint
  
      data IntervalPath : Endpoint -> Endpoint -> Set where
        Refl : ∀ {x} -> IntervalPath x x
        Seg  : IntervalPath zero one
        SymSeg : IntervalPath one zero
        
      iinv : Inv IntervalPath 
      iinv Refl = Refl
      iinv Seg = SymSeg
      iinv SymSeg = Seg

      icomp : Comp IntervalPath 
      icomp Refl p = p
      icomp p Refl = p
      icomp Seg SymSeg = Refl
      icomp SymSeg Seg = Refl

      IntervalG : Gpd
      IntervalG = record { Ob = Endpoint; Arr = IntervalPath; id = Refl; inv = iinv; comp = icomp }

      I = ↓ IntervalG

      I-recF : {C : Set} 
           -> (a b : C)
           -> (p : a ≃ b)
           -> Func IntervalG (↑ C) 
      I-recF {C} a b p = (func I-recO I-recA) where
        I-recO : Endpoint -> C
        I-recO zero = a
        I-recO one = b

        I-recA : ActionOnArrows IntervalG (↑ C) I-recO
        I-recA Refl = Refl
        I-recA Seg = p
        I-recA SymSeg = sym p

      I-rec : {C : Set} 
           -> (a b : C)
           -> (p : a ≃ b)
           -> I -> C
      I-rec {C} a b p = qrec (I-recF a b p)

      β0 : ∀ {C} {a b : C} -> ∀ {p} -> I-rec a b p [ zero ] ≃ a
      β0 = Refl

      β1 : ∀ {C} {a b : C} -> ∀ {p} -> I-rec a b p [ one ] ≃ b
      β1 = Refl
        
      βseg : {C : Set} 
           -> (a b : C)
           -> (p : a ≃ b)
           -> resp (I-rec a b p) [[ Seg ]] ≃ p
      βseg a b p = qβ2 (I-recF a b p) Seg

    SquashG : Set -> Gpd 
    SquashG A = record { Ob = A; Arr = \ _ _ -> Unit; id = _; inv = _; comp = _ }

    Sq : Set -> Set
    Sq A = ↓ (SquashG A)

    module VeryFree(A : Set) (Graph : A -> A -> Set) where
      data Arrow : A -> A -> Set where
        Refl : Ident Arrow
        Sym : Inv Arrow
        Trans : Comp Arrow
        Gen : ∀ {x y} -> Graph x y -> Arrow x y

    module GroupoidLaws(A : Set) (Gen : A -> A -> Set) where
      module A = VeryFree A Gen 
      data Eq : ∀ {x y} -> A.Arrow x y -> A.Arrow x y -> Set where
         Cancel1 : ∀ {x y} {a : A.Arrow x y} -> Eq (A.Trans a (A.Sym a)) A.Refl
         Cancel2 : ∀ {x y} {a : A.Arrow x y} -> Eq (A.Trans (A.Sym a) a) A.Refl

    Free : (A : Set) (Graph : A -> A -> Set) -> Gpd
    Free A G = record { Ob = A; Arr = ArrMod; id = \ {_} -> [ VeryFree.Refl ]; inv = symf; comp = {!!} } where
      ArrMod : A -> A -> Set
      ArrMod x y = ↓ record { Ob = VeryFree.Arrow A G x y; 
                              Arr = \ p q -> Sq (VeryFree.Arrow (VeryFree.Arrow A G x y) (GroupoidLaws.Eq A G) p q); 
                              id = \ {x} -> [ VeryFree.Refl ]; 
                              inv = {!!}; 
                              comp = {!!} }  
      symf : Inv ArrMod
      symf a = qrec (func (\ p -> [ VeryFree.Sym p ] ) (λ {a'} {b} p → qrec (func ((λ q →  [[ [ {!!} ] ]] )) {!!}) p)) a
      

    module Circle where
      data CircPath : Unit -> Unit -> Set where
        Refl    : CircPath <> <>
        Clock   : Nat -> CircPath <> <>
        Counter : Nat -> CircPath <> <>
        
      isym : Inv CircPath
      isym Refl = Refl
      isym (Clock n) = Counter n
      isym (Counter n) = Clock n

      _-_ : Nat -> Nat -> CircPath <> <>
      n - Z = Clock n
      Z - m = Counter m
      (S n) - (S m) = n - m

      icomp : Comp CircPath
      icomp Refl p = p
      icomp p Refl = p
      icomp (Clock n) (Clock m) = Clock (n + m)
      icomp (Counter n) (Counter m) = Counter (n + m)
      icomp (Clock n) (Counter m) = n - m
      icomp (Counter n) (Clock m) = m - n

      CircleG : Gpd
      CircleG = record { Ob = Unit; Arr = CircPath; id = Refl; inv = isym; comp = icomp }

      Circle = ↓ CircleG

      -- Things to check:
      -- fundemental group is isomorphic to Z
      -- C -> X is isomorphic to pi_1(X) i.e. Id_X a a for some/any point a 
  
    module Sphere where
      open Circle

      SphereG : Gpd
      SphereG = record { Ob = Unit; Arr = \ _ _ -> Circle; id = \ {_} -> [ _ ]; inv = \ p -> [ _ ]; comp = \ _ _ -> [ _ ] }
    

    