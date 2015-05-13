open import Agda.Primitive

module hithacks where

  record Unit : Set where
    constructor <>

  data _==_ {l : Level} {A : Set l} (a : A) : A → Set l where
    id : a == a

  ap :  {A B : Set} {M N : A}
       (f : A → B) → M == N → (f M) == (f N)
  ap f id = id

  ! : {A : Set} {M N : A} → M == N → N == M 
  ! id = id

  transport :  {B : Set} (E : B → Set) 
              {b1 b2 : B} → b1 == b2 → (E b1 → E b2)
  transport C id = λ x → x

  {-# BUILTIN EQUALITY _==_ #-}
  {-# BUILTIN REFL id #-}

  primitive 
    primTrustMe : {l : Level} {A : Set l} {x y : A} -> x == y

  funext-unit : {A : Set}{f g : Unit -> A} → f <> == g <> -> f == g
  funext-unit p = primTrustMe

  η-unit→ : {A : Set}{f g : Unit -> A} → (\ _ -> f <>) == f
  η-unit→ = id

  data Phantom {A : Set} (a : A) : Set where
    phantom : Phantom a

  {- 
    HIT I with
      zero : A -> I
      one : I
      seg : (a : A) -> zero a == one
  -}

  module Private {A : Set} where

    private
      data #I : Set where
        #zero : A → #I
        #one : #I
    
      data ##I : Set where
        #in : (Unit -> #I) -> ##I

      #out : ##I -> (Unit -> #I)
      #out (#in i) = i

    I : Set
    I = ##I
    
    zero : A → I
    zero a = #in (\ _ -> #zero a)
    
    one : I
    one = #in (\ _ -> #one)

    postulate 
      seg : (a : A) → zero a == one

    ext : (i : I) (x : #I) → #out i <> == x → #in (\ _ -> x) == i
    ext (#in i') x p = ap #in (! (funext-unit {f = i'} {g = λ _ → x} p)) 

    I-elim : (C : I -> Set) (zero' : (a : A) -> C (zero a)) (one' : C one) (seg' : (a : A) -> transport C (seg a) (zero' a) == one') -> (x : I) -> C x
    I-elim C zero' one' seg' x = I-elim-aux phantom (#out x <>) id where
      I-elim-aux : Phantom seg' → (i : #I) -> #out x <> == i →  C x
      I-elim-aux phantom (#zero a) p = transport C (ext x (#zero a) p) (zero' a) 
      I-elim-aux phantom #one p = transport C (ext x #one p) one'

  open Private 

  definitional0 : (A : Set) (a : A)
         (C : I -> Set)
         (zero' : (a : A) -> C (zero a))
         (one' : C one)
         (seg' : (a : A) -> transport C (seg a) (zero' a) == one')
         → I-elim C zero' one' seg' (zero a) == zero' a
  definitional0 _ _ _ _ _ _ = id
      
  definitional1 : (A : Set)
         (C : I -> Set)
         (zero' : (a : A) -> C (zero a))
         (one' : C one)
         (seg' : (a : A) -> transport C (seg a) (zero' a) == one')
         → I-elim C zero' one' seg' one == one'
  definitional1 _ _ _ _ _ = id

data Void : Set where

-- cannot replace p with ()
disjoint : {A : Set} (x : A) → zero x == one → Void
disjoint x p = {!p!}

-- cannot replace p with id
injective : {A : Set} {x y : A} → zero x == zero y → x == y
injective p = {!p!}

-- cannot compelte goal with id
irrel : (A : Set)
         (C : I -> Set)
         (zero' : (a : A) -> C (zero a))
         (one' : C one)
         (seg' seg'' : (a : A) -> transport C (seg a) (zero' a) == one')
         → I-elim C zero' one' seg' == I-elim C zero' one' seg''
irrel _ _ _ _ _ _ = {!id!}


