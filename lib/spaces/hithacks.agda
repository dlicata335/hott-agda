open import Agda.Primitive

module hithacks where

  record Unit : Set where
    constructor <>

  data _==_ {l : Level} {A : Set l} (a : A) : A → Set l where
    id : a == a

  {-# BUILTIN EQUALITY _==_ #-}
  {-# BUILTIN REFL id #-}
  primitive 
    primTrustMe : {l : Level} {A : Set l} {x y : A} -> x == y


  data Phantom {A : Set} (a : A) : Set where
    phantom : Phantom a

  transport :  {B : Set} (E : B → Set) 
              {b1 b2 : B} → b1 == b2 → (E b1 → E b2)
  transport C id = λ x → x

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
    
    I : Set
    I = Unit -> #I
    
    zero : A → I
    zero a = (\ _ -> #zero a)
    
    one : I
    one = (\ _ -> #one)

    postulate 
      seg : (a : A) → zero a == one
    
    I-elim : (C : I -> Set) (zero' : (a : A) -> C (zero a)) (one' : C one) (seg' : (a : A) -> transport C (seg a) (zero' a) == one') -> (x : I) -> C x
    I-elim C zero' one' seg' i = I-elim-aux phantom (i <>) where
      I-elim-aux : Phantom seg' → #I -> C i
      I-elim-aux phantom (#zero a) = transport C primTrustMe (zero' a) 
      I-elim-aux phantom #one = transport C primTrustMe one'

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
injective p = {!!}

-- cannot compelte goal with id
irrel : (A : Set)
         (C : I -> Set)
         (zero' : (a : A) -> C (zero a))
         (one' : C one)
         (seg' seg'' : (a : A) -> transport C (seg a) (zero' a) == one')
         → I-elim C zero' one' seg' == I-elim C zero' one' seg''
irrel _ _ _ _ _ _ = {!id!}

