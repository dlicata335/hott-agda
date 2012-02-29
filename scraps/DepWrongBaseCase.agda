

open import lib.Prelude hiding ([_])
open Vec

module homotopy.DepCovariant where

  mutual
  -- FIXME: sort out universe levels;
  -- U' has to live at Set1 because Π and Σ quantify over Set
    data U : Set where
      Πu   : (A : U) -> (El A -> U) -> U
      Σu   : (A : U) -> (El A -> U) -> U
      _∨_  : (A B : U) -> U
      ⊤    : U
      ⊥    : U
      nat  : U
      vec  : (A : U) -> Nat -> U -- FIXME: bug? what if you needed to interpret here?

    El : U -> Set
    El (Πu A B) = (x : El A) -> El (B x)
    El (Σu A B) = Σ \ (x : El A) -> El (B x)
    El (A ∨ B) = Either (El A) (El B)
    El ⊤ = Unit
    El ⊥ = Void
    El nat = Nat
    El (vec A n) = Vec (El A) n

  -- FIXME: define OTT equality and postulates about it (refl, subst, resp)
  
  _⊃_ : U -> U -> U
  A ⊃ B = Πu A (\ _ -> B)

  _×u_ : U -> U -> U
  A ×u B = Σu A (\ _ -> B)

  EqU : U -> U -> U
  EqU = {!!}

  EqEl : (A1 : U) -> (e1 : El A1)
      -> (A2 : U)  -> (e2 : El A2) 
      -> U
  EqEl (Πu A B) e1 (Πu A' B') e2 = Πu A \ x -> Πu A' \ x' -> Πu (EqEl A x A' x') \ xy -> EqEl (B x) (e1 x) (B' x') (e2 x')
  EqEl (Σu A B) (x , y) (Σu A' B') (x' , y') = (EqEl A x A' x') ×u (EqEl (B x) y (B' x') y')
  EqEl (A ∨ B) (Inl x) (A' ∨ B') (Inl x') = EqEl A x A' x'
  EqEl (A ∨ B) (Inr x) (A' ∨ B') (Inr x') = EqEl B x B' x'
  EqEl (A ∨ B) (Inl _) (A' ∨ B') (Inr _) = ⊥
  EqEl (A ∨ B) (Inr _) (A' ∨ B') (Inl _) = ⊥
  EqEl ⊤ _ ⊤ _ = ⊤
  EqEl _ _ _ _ = {!!}

  coerce : ∀ {A B} -> El (EqU A B) -> (El A -> El B)
  coerce = {!!}

  postulate 
    refl : (A : U) {x : El A} -> El (EqEl A x A x)

  Iso : U -> U -> U
  Iso A B = (A ⊃ B) 

  left : ∀ {A B} -> El (Iso A B) -> El (A ⊃ B)
  left i = i

  IsoEl : (A1 : U) -> (e1 : El A1)
       -> (A2 : U)  -> (e2 : El A2) 
       -> El (Iso A1 A2) -> U
  IsoEl A1 e1 A2 e2 i = EqEl A2 (left i e1) A2 e2

  Ctx : (U -> U) -> Set
  Ctx Δ = (α : U) -> El (Δ α) -> U

--   IsoArgs : (Δ Δ' : U -> U) -> U -> U -> Set
--   IsoArgs Δ Δ' α = -- or should it be for any two isomorphic codes?

  -- presupposes IsoArgs Δ Δ' ??
  data _~_ {Δ Δ'} : (A : Ctx Δ) -> (A' : Ctx Δ') -> Set where
    base :  {A : Ctx Δ} {A' : Ctx Δ'}
         -> (∀ {α α'} 
               -> El (Iso α α')
               -> (iΔ : El (Iso (Δ α) (Δ' α')))
               -> {σ : El (Δ α)} {σ' : El (Δ' α')}
               -> El (IsoEl _ σ _ σ' iΔ) 
               -> El (EqU (A α σ) (A' α' σ')))
         -> A ~ A'
    var : (\ α _ -> α) ~ (\ α _ -> α)
    _∨_ :  {A B : Ctx Δ} {A' B' : Ctx Δ'}
        -> A ~ A' -> B ~ B' 
        -> (\ α x -> A α x ∨ B α x) ~ (\ α x -> A' α x ∨ B' α x)
    Σu  : {A : Ctx Δ} {B : Ctx (\ α -> Σu (Δ α) \ x -> (A α x))} 
          {A' : Ctx Δ'} {B' : Ctx ((\ α -> Σu (Δ' α) \ x -> (A' α x)))}
        -> A ~ A' -> B ~ B'
        -> (\ α x -> Σu (A α x) \ y -> B α (x , y)) ~ (\ α x -> Σu (A' α x) \ y -> B' α (x , y))
{-
    ΣuBetter : {A : Ctx Δ} {B : Ctx (\ α -> Σu (Δ α) \ x -> (A α x))} 
          {A' : Ctx Δ'} {B' : Ctx ((\ α -> Σu (Δ' α) \ x -> (A' α x)))}
        -> A ~ A' -> B ~ B'
        -> (\ α x -> Σu (A α x) \ y -> B α (x , y)) ~ (\ α x -> Σu (A' α x) \ y -> B' α (x , y))
-}

  -- would follow from subst, but need it for context extension
  isoΣ : {A A' : U} {B : El A -> U} {B' : El A' -> U}
       -> (i : El (Iso A A'))
       -> ((x : El A) (x' : El A') -> El (IsoEl A x A' x' i) -> El (Iso (B x) (B' x')))
       -> El (Iso (Σu A B) (Σu A' B'))
  isoΣ {A}{A'} i1 i2 (x , y) = i1 x , i2 x (left i1 x) (refl A') y

  subst :  {A A' : U} -> El (Iso A A') 
        -> {Δ Δ' : _} -> (ia : El (Iso (Δ A) (Δ' A')))
        -> {σ : El (Δ A)} {σ' : El (Δ' A')} -> El (IsoEl (Δ A) σ (Δ' A') σ' ia)
        -> {C : Ctx Δ} {C' : Ctx Δ'} -> C ~ C'
        -> El (C A σ) -> El (C' A' σ')
  subst iA iΔ iσ (base eq) e = coerce (eq iA iΔ iσ) e 
  subst iA iΔ iσ var e = left iA e 
  subst iA iΔ iσ (γ1 ∨ γ2) (Inl e) = Inl (subst iA iΔ iσ γ1 e) 
  subst iA iΔ iσ (γ1 ∨ γ2) (Inr e) = Inr (subst iA iΔ iσ γ2 e) 
  subst iA iΔ iσ (Σu γ1 γ2) (e1 , e2) = 
    subst iA iΔ iσ γ1 e1 , 
    subst iA (isoΣ iΔ (\ x x' xx' -> subst iA iΔ xx' γ1)) (iσ , {!!}) γ2 e2 -- some equality stuff

  module Examples where

    IsSome : (α : U) -> El (α ∨ ⊤) -> U
    IsSome α (Inl _) = ⊤
    IsSome α (Inr _) = ⊥

    C : U -> U
    C α = Σu (α ∨ ⊤) (IsSome α)

    isoOption : ∀ {A B} -> El (Iso A B) -> El (Iso (A ∨ ⊤) (B ∨ ⊤))
    isoOption f (Inl x) = Inl (f x)
    isoOption f (Inr _) = Inr _

    substC : ∀ {α α'} -> El (Iso α α') -> El (Iso (C α) (C α'))
    substC {α} {α'} f = isoΣ{_}{(α' ∨ ⊤)}{_}{IsSome α'} (isoOption f) lemma where
      lemma : (x : Either (El α) Unit) (x' : Either (El α') Unit) →
                El (EqEl _ (isoOption f x) _ x') → (x0 : El (IsSome α x)) → El (IsSome α' x')
      lemma (Inl _) (Inl _) xx' is = _
      lemma (Inl _) (Inr _) ()  is
      lemma (Inr _) (Inl _) xx' is = _
      lemma (Inr _) (Inr _) xx' ()
      

{-
  mutual
  

    IsIso : (A B : U) -> (El A -> El B) -> Set
    IsIso A B f = Σ \ (g : El B -> El A) -> 
                    FunEq A A (\ x -> (g (f x))) (\ x -> x) ×
                    FunEq B B (\ x -> (f (g x))) (\ x -> x)

    Iso : U -> U -> Set
    Iso A B = Σ \ (f : El A -> El B) -> IsIso A B f

    FunEq : (A B : U) (f g : El A -> El B) -> Set
    FunEq A B f g = (x y : El A) -> Eq A x y -> Eq B (f x) (g y)

    Eq : (A : U) -> El A -> El A -> Set 
    Eq ⊤ _ _ = Unit
    Eq ⊥ () ()
    Eq (A ∧ B) (x1 , x2) (y1 , y2) = Eq A x1 y1 × Eq B x2 y2
    Eq (A ∨ B) (Inl x) (Inl y) = Eq A x y   
    Eq (A ∨ B) (Inr x) (Inr y) = Eq B x y
    Eq (A ∨ B) (Inl _) (Inr _) = Void
    Eq (A ∨ B) (Inr _) (Inl _) = Void
    Eq (A ⊃ B) f g = FunEq A B f g
    Eq (A ≅ B) (f , _) (f' , _) = FunEq A B f f' -- SUSP: because inverses and proofs are unique?

  _[_] : ∀ {Γ} -> U' True -> U' Γ -> U' Γ
  ⊤ [ _ ] = ⊤
  ⊥ [ _ ] = ⊥
  (A ∧ B) [ C ] = (A [ C ]) ∧ (B [ C ])
  (A ∨ B) [ C ] = (A [ C ]) ∨ (B [ C ])
  (A ⊃ B) [ C ] = (A [ C ]) ⊃ (B [ C ])
  (A ≅ B) [ C ] = (A [ C ]) ≅ (B [ C ])
  var     [ C ] = C

  module Equality where
    postulate 
      refl  : (A : U) {x : El A} -> Eq A x x
      -- subst : {A : U} (C : El A -> Set) {x y : El A} -> Eq A x y -> C x -> C y 
      resp : (A B : U) (f : El A -> El B) {x y : El A} -> Eq A x y -> Eq B (f x) (f y)
      -- uip   : (A : U) (x y : El A) -> (p q : Eq A x y) -> Id p q -- gross, but can't form an Eq of equalities

    sym : (A : U) {x y : El A} -> Eq A x y -> Eq A y x
    sym (A ⊃ A') p = \ x y xy -> sym A' (p y x (sym A xy))
    sym (A ∧ A') {_ , _} {_ , _} (p1 , p2) = sym A p1 , sym A' p2 
    sym (A ∨ A') {(Inl x)} {(Inl y)} e = sym A e
    sym (A ∨ A') {(Inr x)} {(Inr y)} e = sym A' e
    sym (A ∨ A') {(Inl _)} {(Inr _)} ()
    sym (A ∨ A') {(Inr _)} {(Inl _)} ()
    sym ⊤ _ = _
    sym ⊥ {()} {()} _
    sym (A ≅ A') {(f , _)} {(g , _)} p = \ x y xy -> sym A' (p y x (sym A xy))

    trans : (A : U) {y x z : El A} -> Eq A x y -> Eq A y z -> Eq A x z
    trans = {!!}

--    resp = {!!}

  module Iso where
    id : (A : U) -> El (A ≅ A)
    id A = (\ x -> x) , (\ x -> x) , (\ _ _ xy -> xy) , (\ _ _ xy -> xy)  

    comp : (A B C : U) -> El ((B ≅ C) ⊃ ((A ≅ B) ⊃ (A ≅ C)))
    comp A B C (bc , cb , cbc1 , cbc2) (ab , ba , cab1 , cab2) =
      (\ x -> bc (ab x)) , 
      (\ y -> ba (cb y) ) , 
      (\ x y xy -> Equality.trans A (Equality.trans A (Equality.resp B A ba ((cbc1 (ab x) (ab x) (Equality.refl B)))) (cab1 x x (Equality.refl A))) xy  ) ,
      {!  !} -- symmetric

    inv : (A B : U) -> El ((A ≅ B) ⊃ (B ≅ A))
    inv A B i = (fst (snd i)) , (fst i) , (snd (snd (snd i))) , (fst (snd (snd i)))

    inv-id-1 : (A B : U) -> (x : El (A ≅ B)) -> Eq (A ≅ A) (comp A B A (inv A B x) x) (id A)
    inv-id-1 A B (l , r , c1 , c2) = c1

    inv-id-2 : (A B : U) -> (x : El (A ≅ B)) -> Eq (B ≅ B) (comp B A B x (inv A B x)) (id B)
    inv-id-2 A B (l , r , c1 , c2) = c2

    inv-comp : (A B C : U) -> (g : El (B ≅ C)) (f : El (A ≅ B))
               -> Eq (C ≅ A) (inv A C (comp A B C g f)) (comp C B A (inv A B f) (inv B C g))
    inv-comp A B C (l , r , c1 , c2) (l' , r' , c1' , c2') = \ x y xy -> Equality.resp C A (\ z -> r' (r z)) xy

    inv-unique : (A B : U) (f : El A -> El B) -> (g1 g2 : IsIso A B f) -> FunEq B A (fst g1) (fst g2)
    inv-unique A B f g1 g2 x y xy = Equality.trans A {(fst g2) (f ((fst g1) x))} 
                                                     (Equality.sym A ((fst (snd g2)) _ _ (Equality.refl A))) 
                                                     (Equality.resp B A (\ z -> fst g2 z) ((snd (snd g1)) x y xy)) 

  mutual
    subst : ∀ (C : U' True) {A B : U} -> El ((A ≅ B) ⊃ (C [ A ] ⊃ C [ B ]))
    subst var (f , _) e = f e
    subst (C ⊃ C') i e = fsubst C C' i e
    subst (C ∧ C') i (e1 , e2) = subst C i e1 , subst C' i e2
    subst (C ∨ C') i (Inl e) = Inl (subst C i e)
    subst (C ∨ C') i (Inr e) = Inr (subst C' i e)
    subst ⊤ i _ = _
    subst ⊥ i ()
    subst (C ≅ C') {A}{B} i e = subst-into-iso C C' i e 
  
    fsubst : ∀ (C1 C2 : U' True) {A B : U} -> El ((A  ≅ B) ⊃ ((C1 ⊃ C2) [ A ] ⊃ (C1 ⊃ C2) [ B ]))
    fsubst C1 C2 {A} {B} i e = \ x -> subst C2 i (e (subst C1 (Iso.inv A B i) x ))

    subst-into-iso : ∀ (C1 C2 : U' True) {A B : U} -> El ((A ≅ B) ⊃ ((C1 [ A ] ≅ C2 [ A ]) ⊃ (C1 [ B ] ≅ C2 [ B ])))
    subst-into-iso C C' {A} {B} i (l , r , comp1 , comp2) = 
      fsubst C C' i l , 
      fsubst C' C i r , 
      (\ x y xy -> Equality.trans (C [ B ]) 
                   (Equality.trans (C [ B ]) 
                                   {(subst C i (r (l (subst C (Iso.inv A B i) x))))}
                                   (Equality.resp (C' [ A ]) (C [ B ]) (\ z -> subst C i (r z)) (subst-inverses1 C' i _ _ (Equality.refl (C' [ A ])))) 
                                   (Equality.trans (C [ B ]) {(subst C i (subst C (Iso.inv A B i) x))}
                                                   (Equality.resp (C [ A ]) (C [ B ]) (\ z -> subst C i z) (comp1 _ _ (Equality.refl (C [ A ])))) 
                                                   (subst-inverses2 C i x x (Equality.refl (C [ B ]))))) xy) ,
      {!!} -- symmetric

    identity : ∀ (C : U' True) {A : U} -> FunEq (C [ A ]) (C [ A ]) (subst C {A}{A} (Iso.id A)) (\ x -> x)
    identity (A ⊃ B) x y xy = \ x' y' x'y' -> identity B _ _ (xy _ _ (identity A _ _ x'y'))
    identity (A ∧ B) (x1 , x2) (y1 , y2) (p1 , p2) = identity A x1 y1 p1 , identity B x2 y2 p2
    identity (A ∨ B) (Inl y) (Inl y') xy = identity A y y' xy
    identity (A ∨ B) (Inl y) (Inr y') ()
    identity (A ∨ B) (Inr y) (Inl y') ()
    identity (A ∨ B) (Inr y) (Inr y') xy = identity B y y' xy
    identity ⊤ x y xy = _
    identity ⊥ () () _
    identity (A ≅ B) (l , r , c1 , c2) (l' , r' , c1' , c2') xy = \ x' y' x'y' -> identity B _ _ (xy _ _ (identity A _ _ x'y')) 
    identity var x y xy = xy

    subst-inverses1 : ∀ (D : U' True) {A B : U} -> (i : El (A ≅ B)) 
            -> FunEq (D [ A ]) (D [ A ]) (\ x -> subst D {B}{A} (Iso.inv A B i) (subst D i x)) (\ x -> x)
    subst-inverses1 D {A}{B} i = \ x y xy -> Equality.trans (D [ A ]) 
                                       (Equality.trans (D [ A ]) 
                                         (compose D {A} {B} {A} i (Iso.inv A B i) x x (Equality.refl (D [ A ])) ) 
                                         (Equality.resp (A ≅ A) (D [ A ]) (\ z -> subst D z x) (Iso.inv-id-1 A B i)) ) 
                                       (identity D {A} x y xy) 

    subst-inverses2 : ∀ (D : U' True) {A B : U} -> (i : El (A ≅ B)) 
            -> FunEq (D [ B ]) (D [ B ]) (\ x -> subst D {A}{B} i (subst D (Iso.inv A B i) x)) (\ x -> x)
    subst-inverses2 D {A}{B} i = {! \ x y xy -> Equality.trans (D [ A ]) 
                                       (Equality.trans (D [ A ]) 
                                         (compose D {A} {B} {A} i (Iso.inv A B i) x x (Equality.refl (D [ A ])) ) 
                                         (Equality.resp (A ≅ A) (D [ A ]) (\ z -> subst D z x) (Iso.inv-id-2 A B i)) ) 
                                       (identity D {A} x y xy) !}  -- symmetric

    compose : ∀ (D : U' True) {A B C : U} -> (i1 : El (A ≅ B)) -> (i2 : El (B ≅ C))
            -> FunEq (D [ A ]) (D [ C ]) (\ x -> subst D {B}{C} i2 (subst D {A}{B} i1 x)) (\ x -> (subst D {A} {C} (Iso.comp A B C i2 i1) x))
    compose (A ⊃ B) {A1} {A2} {A3} i1 i2 x y xy = 
            \ x' y' x'y' -> compose B i1 i2 _ _ 
                                (xy _ _ 
                                  (Equality.trans (A [ A1 ]) 
                                    (compose A (Iso.inv A2 A3 i2) (Iso.inv A1 A2 i1) _ _ x'y') 
                                    (Equality.resp (A3 ≅ A1) (A [ A1 ]) (\ x -> subst A x y') 
                                      \ x0 y0 x0y0 ->  Equality.sym A1 ((Iso.inv-comp A1 A2 A3 i2 i1) y0 x0 (Equality.sym A3 x0y0)))))
    compose (A ∧ B) i1 i2 (x , y) (x' , y') (x0 , y0) = compose A i1 i2 x x' x0 , compose B i1 i2 y y' y0
    compose (A ∨ B) i1 i2 (Inl y) (Inl y') xy = compose A i1 i2 y y' xy
    compose (A ∨ B) i1 i2 (Inl y) (Inr y') ()
    compose (A ∨ B) i1 i2 (Inr y) (Inl y') ()
    compose (A ∨ B) i1 i2 (Inr y) (Inr y') xy = compose B i1 i2 y y' xy
    compose ⊤ i1 i2 _ _ xy = _
    compose ⊥ i1 i2 () () xy
    compose (A ≅ B) i1 i2 (l1 , r1 , clr1 , crl1) (l2 , r2 , clr2 , crl2) xy = {!!} -- analogous to function case
    compose var {A}{B}{C} (l , r , c1 , c2) (l' , r' , c1' , c2') x y xy = Equality.resp A C (\ x -> (l' (l x))) xy

    subst-iso : ∀ (C : U' True) -> {A B : U} -> (i : El (A ≅ B)) -> IsIso (C [ A ]) (C [ B ]) (subst C i)
    subst-iso C {A} {B} i = subst C (Iso.inv A B i) , 
                             (\ x y xy ->  Equality.trans (C [ A ]) 
                                                          (compose C i (Iso.inv A B i) _ _ xy)
                                                          (Equality.trans (C [ A ]) 
                                                                          (Equality.resp (A ≅  A) (C [ A ]) (\ x -> (subst C x y)) (Iso.inv-id-1 A B i) ) 
                                                                          (identity C y y (Equality.refl (C [ A ])))) ) , 
                            {!!} -- FIXME-symmetric

{-
  substIso : ∀ {A B} -> (P : El A -> Set) -> (i : Iso A B) 
           -> (x : El A) -> (P x) -> (P ((fst (snd i)) x))
  substIso = ?
-}

-}