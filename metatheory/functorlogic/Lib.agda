
-- requires Agda 2.4.2.3 or later for the rewrite stuff

open import Agda.Primitive

module functorlogic.Lib where

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


  -- ----------------------------------------------------------------------
  -- products
  
  record Σe (A : Set) (B : A -> Set) : Set where
     constructor _,_
     field
       fst : A
       snd : B fst
  open Σe public
  
  infixr 0 _,_

  Σ : {A : Set} -> (B : A -> Set) -> Set
  Σ {A} B = Σe A B

  _×_ : Set → Set → Set
  A × B = Σe A (\ _ -> B)

  infixr 10 _×_

  record Unit : Set where
    constructor <>

  ----------------------------------------------------------------------

  data List (a : Set) : Set where
    []  : List a
    _::_ : a -> List a -> List a 

  _++_ : ∀ {A : Set} → List A → List A → List A
  [] ++ ys = ys
  (x :: xs) ++ ys = x :: (xs ++ ys)

  data _∈_ {A : Set} : A -> List A -> Set where
      i0 : {x : A}   {xs : List A} -> x ∈ (x :: xs)
      iS : {x y : A} {xs : List A} -> y ∈ xs -> y ∈ (x :: xs)
  infix 10 _∈_

  All : ∀ {A} → (A → Set) → List A → Set
  All {A} P [] = Unit
  All {A} P (x :: xs) = P x × All P xs 

  append-All : ∀ {A} {P : A → Set} {xs ys} → All P xs → All P ys → All P (xs ++ ys)
  append-All {xs = []} axs ays = ays
  append-All {xs = x :: xs} axs ays = fst axs , append-All (snd axs) ays

  all-from-in : ∀ {A} {P : A → Set} → (xs : List A) → ({x : A} → x ∈ xs → P x) → All P xs
  all-from-in [] f = <>
  all-from-in (x :: xs) f = f i0 , all-from-in xs (λ x₁ → f (iS x₁))

  lookup : ∀ {A : Set} {l : List A} {P : A → Set} {x : A}
         → All P l → x ∈ l
         → P x
  lookup a i0 = fst a
  lookup a (iS i) = lookup (snd a) i


  replace : ∀ {A} {xs} (ys : List A) {a : A} (i : a ∈ xs) → List A
  replace {xs = _ :: xs} ys i0 = ys ++ xs
  replace {xs = x :: _} ys (iS i) = x :: replace ys i

  addright : ∀ {A} {x} {xs ys : List A} → x ∈ xs → x ∈ xs ++ ys
  addright i0 = i0
  addright (iS i) = iS (addright i)

  addleft : ∀ {A} {x} {xs : List A} (ys : List A) → x ∈ xs → x ∈ ys ++ xs
  addleft [] i = i
  addleft (y :: ys) i = iS (addleft ys i)

  all-replace : ∀ {A} {P : A → Set} {xs} 
                  (axs : All P xs)
                  {ys : List A} (ays : All P ys)
                  {a : A} 
                  (i : a ∈ xs) → All P (replace ys i)
  all-replace axs ays i0 = append-All ays (snd axs)
  all-replace axs ays (iS i) = fst axs , all-replace (snd axs) ays i

  mapAll : ∀ {A} {P Q : A → Set} {xs : List A}
           → ({x : A} → P x → Q x) 
           → All P xs 
           → All Q xs 
  mapAll {xs = []} f ps = <>
  mapAll {xs = x :: xs} f (p , ps) = f p , mapAll f ps

  allList : ∀ {A} {P : A → Set} {l : List A} → All P l → List (Σ P)
  allList {l = []} x = []
  allList {l = x :: xs} (a , as) = (x , a) :: allList as

  allZip : ∀ {A} {P Q : A → Set} {l : List A} → All P l → All Q l → All (\x → P x × Q x) l
  allZip {l = []} a1 a2 = <>
  allZip {l = x :: xs} (a1 , as1) (a2 , as2) = (a1 , a2) , allZip as1 as2

  AllAll2 : ∀ {A} {P Q : A → Set} {xs : List A}
           → ({x : A} → P x → Q x → Set) 
           → All P xs 
           → All Q xs 
           → Set
  AllAll2 F ps qs = All (λ p → F (fst (snd p)) (snd (snd p))) (allList (allZip ps qs))

  makeAllAll2 : ∀ {A} {P Q R : A → Set} {xs : List A}
           → (f : {x : A} → P x → Q x) 
           → (g : {x : A} → P x → R x) 
           → (H : {x : A} → Q x → R x → Set)
           → ({x : A} (p : P x) → H (f p) (g p))
           → (a : All P xs)
           → AllAll2 H (mapAll f a) (mapAll g a)
  makeAllAll2 {xs = []} f g H mkH a = <>
  makeAllAll2 {xs = x :: xs} f g H mkH a = mkH (fst a) , makeAllAll2 f g H mkH (snd a)

{-
  allAll2map : ∀ {A} {P Q P' Q' : A → Set} {xs : List A}
               (F : {x : A} → P x → Q x → Set) 
               (F' : {x : A} → P' x → Q' x → Set) 
               → (f : {x : A} (p : P x) → P' x)
               → (g : {x : A} (p : Q x) → Q' x)
               → {a1 : All P xs} {a2 : All Q xs}
               → (∀ {x} {p : P x} {q : Q x} → F p q → F' (f p) (g q))
               → AllAll2 F a1 a2
               → AllAll2 F' (mapAll f a1) (mapAll g a2)
  allAll2map {xs = []} F F' f g FF'  a = <>
  allAll2map {xs = x :: xs} F F' f g FF' (a , as) = FF' a , allAll2map F F' f g  FF' as
-}

  allAll2refl : ∀ {A} {P : A → Set} {xs : List A}
               (F : {x : A} → P x → P x → Set) 
               → ({x : A} (p : P x) → F p p)
               → (a : All P xs)
               → AllAll2 F a a 
  allAll2refl {xs = []} F r a = <>
  allAll2refl {xs = x :: xs} F r (a , as) = r a , allAll2refl F r as

  allAll2Trans : ∀ {A} {P Q R : A → Set} {xs : List A}
               (F : {x : A} → P x → Q x → Set) 
               (G : {x : A} → Q x → R x → Set) 
               (H : {x : A} → P x → R x → Set) 
               {a1 : All P xs}
               {a2 : All Q xs}
               {a3 : All R xs}
               (fgh : ∀ {x} {p : P x} {q r} → F p q → G q r → H p r)
               → AllAll2 F a1 a2
               → AllAll2 G a2 a3
               → AllAll2 H a1 a3
  allAll2Trans {xs = []} F G H fgh aa1 aa2 = <>
  allAll2Trans {xs = x :: xs} F G H fgh aa1 aa2 = fgh (fst aa1) (fst aa2) , allAll2Trans F G H fgh (snd aa1) (snd aa2)
  
