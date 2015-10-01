
-- requires Agda 2.4.2.3 or later for the rewrite stuff

open import Agda.Primitive

module adjointlogic.Lib where

  -- REWRITE seems not to work with type-in-type
  data _==_ {A : Set} (M : A) : A → Set where
    id : M == M

  transport : ∀ {A : Set} (C : A →  Set) {M N : A} (P : M == N) → C M → C N
  transport C id x = x

  ap :  {A B : Set} {M N : A}
       (f : A → B) → M == N → (f M) == (f N)
  ap f id = id

  ap2 :  {A B C : Set} {M N : A} {M' N' : B} (f : A -> B -> C) -> M == N -> M' == N' -> (f M M') == (f N N')
  ap2 f id id = id

  ! :  {A : Set} {M N : A} → M == N → N == M
  ! id = id

  _∘_  : {A : Set} {M N P : A} → N == P → M == N → M == P
  β ∘ id = β

  _=〈_〉_ : {A : Set} (x : A) {y z : A} → x == y → y == z → x == z
  _ =〈 p1 〉 p2 = (p2 ∘ p1)
 
  _∎ : ∀ {A : Set} (x : A) → x == x
  _∎ _ = id

  infix  2 _∎
  infixr 2 _=〈_〉_ 

  infixr 10 _∘_ 

  data Either (A : Set) (B : Set) : Set where
    Inl : A → Either A B
    Inr : B → Either A B


