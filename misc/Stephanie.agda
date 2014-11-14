
module misc.Stephanie (A : Set) where

  -- Prelude

  data _==_ {A : Set} (M : A) : A → Set where
   id :  M == M

  data List (a : Set) : Set where
    []  : List a
    _::_ : a -> List a -> List a 

  ap :  {A B : Set} {M N : A}
       (f : A → B) → M == N → (f M) == (f N)
  ap f id = id


  missing-side : {A : Set} {a b c d : A} 
               (left : a == b)
               (top : a == c)
               (right : c == d)
               → b == d
  missing-side id id id = id


  -- defs

  snoc : List A → A → List A
  snoc [] x = x :: []
  snoc (y :: xs) x = y :: snoc xs x

  remLast : List A → List A
  remLast [] = []
  remLast (x :: []) = []
  remLast (x :: xs) = x :: (remLast xs) 


  -- proof

  lemma : (x y : A) (xs : List A) → (remLast (y :: snoc xs x)) == (y :: remLast (snoc xs x))
  lemma x y [] = id
  lemma x y (x₁ :: xs) = id

  inv : {x : A} (xs : List A) → remLast (snoc xs x) == xs
  inv [] = id
  inv {x} (y :: xs) = missing-side id (lemma x y xs) (ap (_::_ y) (inv {x} xs))

  inj : {x y : A} {xs ys : List A} → (snoc xs x) == (snoc ys y) -> xs == ys
  inj {x}{y}{xs}{ys} p = missing-side (inv xs) (ap remLast p) (inv ys)
  
