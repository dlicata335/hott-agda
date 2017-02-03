{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open import lib.Nat
open import lib.Maybe
open import lib.Sums
open import lib.Prods

module lib.List where

  data List (a : Type) : Type where
    []  : List a
    _::_ : a -> List a -> List a 

  {-# COMPILED_DATA List [] [] (:) #-}
  {-# BUILTIN LIST List #-}
  {-# BUILTIN NIL [] #-}
  {-# BUILTIN CONS _::_ #-}

  infixr 99 _::_

  module ListM where
    -- we expand this out, rather than using (Somewhere (\x -> Id x a) l)
    -- so that we don't have to write the silly identity proof in the deBruijn index 
    data _∈_ {A : Type} : A -> List A -> Type where
      i0 : {x : A}   {xs : List A} -> x ∈ (x :: xs )
      iS : {x y : A} {xs : List A} -> y ∈ xs -> y ∈ (x :: xs)
    infix 10 _∈_
  
    data Everywhere {A : Type} (P : A -> Type) : List A -> Type where
      E[] : Everywhere P []
      _E::_ : forall {x xs} -> P x -> Everywhere P xs -> Everywhere P (x :: xs) 
  
    infixr 98 _E::_
  
    [_] : {A : Type} -> A -> List A
    [_] x  = x :: []
  
    append : {A : Type} -> List A -> List A -> List A
    append [] l2 = l2
    append (x :: xs) l2 = x :: (append xs l2)
  
    _++_ : {A : Type} -> List A -> List A -> List A
    _++_ = append
    infixr 20 _++_

    rev : {A : Type} -> List A -> List A
    rev [] = []
    rev (x :: xs) = rev xs ++ [ x ]

    length : {a : Type} -> List a -> Nat
    length [] = 0
    length (x :: xs) = S (length xs)
  
    fold : {a b : Type} -> b -> (a -> b -> b) -> List a -> b
    fold n c [] = n
    fold n c (x :: xs) = c x (fold n c xs)
  
    map : {a b : Type} -> (a -> b) -> List a -> List b
    map f [] = []
    map f (x :: xs) = f x :: (map f xs)

    nth : {A : Type} -> List A -> Nat -> Maybe A
    nth [] _ = None
    nth (x :: xs) 0 = Some x
    nth (x :: xs) (S n) = nth xs n

    tabulate' : {A : Type} -> (Nat -> A) -> Nat -> Nat -> List A
    tabulate' f 0 cur = []
    tabulate' f (S n) cur = f cur :: tabulate' f n (S cur)

    tabulate : {A : Type} -> (Nat -> A) -> Nat -> List A
    tabulate f n = tabulate' f n 0

    fuse-map : {A B C : Type} {f : A -> B} {g : B -> C} (l : List A) -> 
                map g (map f l)
              ≃ map (\ x -> g (f x)) l
    fuse-map [] = id
    fuse-map {f = f} {g = g} (x :: xs) = ap (\ xs -> (g (f x)) :: xs) (fuse-map xs)

    map-idfunc : ∀ {A} (l : List A)
               → map (\ x -> x) l ≃ l
    map-idfunc [] = id
    map-idfunc (x :: xs) = ap (_::_ x) (map-idfunc xs)

    append-rh-[] : ∀ {A} (xs : List A) → (append xs []) == xs
    append-rh-[] [] = id
    append-rh-[] (x :: xs) = ap2 _::_ id (append-rh-[] xs)
    
    append-assoc : ∀ {A} (xs ys zs : List A) → (append xs (append ys zs)) == (append (append xs ys) zs)
    append-assoc [] ys zs = id
    append-assoc (x :: xs) ys zs = ap2 _::_ id (append-assoc xs ys zs)
    
    rev-append : ∀ {A} (xs ys : List A) → rev (xs ++ ys) == rev ys ++ rev xs
    rev-append [] ys = ! (append-rh-[] (rev ys))
    rev-append (x :: xs) ys = ! (append-assoc (rev ys) (rev xs) [ x ]) ∘ ap (λ h → h ++ [ x ]) (rev-append xs ys)
    
    rev-rev : ∀ {A} (xs : List A) → rev (rev xs) == xs
    rev-rev [] = id
    rev-rev (x :: xs) = ap (_::_ x) (rev-rev xs) ∘ rev-append (rev xs) [ x ]

    module Index where
      Pos : ∀ {A} → List A → Set
      Pos xs = Σ \ x → x ∈ xs
    
      iSMany : ∀ {A} (xs : List A) {ys} {x} → x ∈ ys → x ∈ (xs ++ ys)
      iSMany [] i = i
      iSMany (x :: xs) i = iS (iSMany xs i)
    
      iSManyRight : ∀ {A} {xs} {ys : List A} {x} → x ∈ xs → x ∈ (xs ++ ys)
      iSManyRight i0 = i0
      iSManyRight (iS i) = iS (iSManyRight i)
    
      first : ∀ {A} {xs : List A} {x} → Pos (xs ++ [ x ])
      first {xs = []} = _ , i0
      first {xs = x :: xs} = _ , i0
    
      -- put an iS at the tail
      shiftright : ∀ {A} {xs : List A} {x0} → Pos xs → Pos (xs ++ [ x0 ])
      shiftright {xs = []} (_ , ())
      shiftright {xs = x :: []} {x0} (._ , i0) = x0 , iS i0
      shiftright {xs = x :: []} (_ , (iS ()))
      shiftright {xs = x :: x' :: xs} (._ , i0) = x' , iS i0
      shiftright {xs = x :: x' :: xs} (_ , iS i) with shiftright {xs = x' :: xs} (_ , i)
      ...                             | y' , i' = y' , iS i'
    
      same-index-in-rev : ∀ {A} { Ψ : List A } → Pos Ψ → Pos (rev Ψ)
      same-index-in-rev {Ψ = x :: Ψ} (.x , i0) = first {xs = rev Ψ}
      same-index-in-rev (_ , iS i) with same-index-in-rev (_ , i)
      ...          | y , i' = shiftright (_ , i')
    
      -- length(xs1)
      index : ∀ {A} {xs1 : List A} {x xs2} → x ∈ (xs1 ++ (x :: xs2)) 
      index {xs1 = xs1} = iSMany xs1 i0
    
      splitat : ∀ {A} {xs : List A} {x} → x ∈ xs → Σ \ xs1 → Σ \ xs2 → xs == xs1 ++ (x :: xs2)
      splitat i0 = [] , _ , id
      splitat (iS i) with splitat i 
      splitat (iS i) | xs1 , xs2 , id = _ :: xs1 , xs2 , id
    
      splitfirst : ∀ {A} {xs : List A} {x} → Σ \ ys → (xs ++ [ x ]) == (fst (first {xs = xs} {x})) :: ys
      splitfirst {xs = []} = _ , id
      splitfirst {xs = x :: xs} = _ , id
    
      split-∈++ : ∀ {A} {xs ys : List A} {x} → x ∈ (xs ++ ys) → Either (x ∈ xs) (x ∈ ys)
      split-∈++ {xs = []} i = Inr i
      split-∈++ {xs = x :: xs} i0 = Inl i0
      split-∈++ {xs = x₁ :: xs} (iS i) with split-∈++ {xs = xs} i 
      ... | Inl p = Inl (iS p)
      ... | Inr q = Inr q
      
      data _≤_ {A : Set} : {xs : List A} → (i : Pos xs) (i' : Pos xs) → Set where
        LtZ : ∀ {x xs} (i : Pos (x :: xs)) → (x , i0 {_}{x}{xs}) ≤ (fst i , (snd i))
        LtS : ∀ {x xs} {i i' : Pos xs} → i ≤ i' → (_ , iS {_}{x} (snd i)) ≤ (_ , (iS (snd i')))
    
      ≤-refl : {A : Set} {xs : List A} (i : Pos xs) → i ≤ i
      ≤-refl (x , i0) = LtZ _
      ≤-refl (x , iS i) = LtS (≤-refl (_ , i))
    
      iSMany≤ : ∀ {A} (xs : List A) {ys} {i j : Pos {A} ys} → i ≤ j → (_ , iSMany xs (snd i)) ≤ (_ , iSMany xs (snd j))
      iSMany≤ [] {i = fst , snd} {fst₁ , snd₁} lt = lt
      iSMany≤ (x :: xs) {i = fst , snd} {fst₁ , snd₁} lt = LtS (iSMany≤ xs lt)
    
      iSManyRight≤ : ∀ {A} {xs : List A} {ys} {i j : Pos {A} xs} → i ≤ j → (_ , iSManyRight {ys = ys} (snd i)) ≤ (_ , iSManyRight (snd j))
      iSManyRight≤ {i = fst , .i0} {fst₁ , snd} (LtZ .(fst₁ , snd)) = LtZ _
      iSManyRight≤ {i = ._ , ._} {._ , ._} (LtS lt) = LtS (iSManyRight≤ lt)
    
      noPos[] : ∀ {A C} → Pos {A} [] → C
      noPos[] (_ , ())

      -- see metatheory/SimplexOp for a lemma about splitting ++ and ≤ that I didn't want to rewrite without K  

      ≤-last : ∀ {A} {xs} {x : A} (i : Pos (xs ++ [ x ])) → i ≤ (_ , iSMany xs i0)
      ≤-last {xs = []} (x , i0) = LtZ _
      ≤-last {xs = []} (fst , iS ())
      ≤-last {xs = .x :: xs} (x , i0) = LtZ _
      ≤-last {xs = x₁ :: xs} (fst , iS i) = LtS (≤-last {xs = xs} (_ , i))

      shiftright≤ : ∀ {A} {Ψ : List A} {x0} {i j : Pos Ψ} → i ≤ j → shiftright  {x0 = x0} i ≤ shiftright j
      shiftright≤ {Ψ = x0 :: []} {i = .x0 , .i0} {._ , ._} (LtZ (._ , i0)) = LtS (LtZ _)
      shiftright≤ {Ψ = x0 :: []} {i = .x0 , .i0} {._ , ._} (LtZ (._ , iS ())) 
      shiftright≤ {Ψ = x0 :: x :: Ψ} {i = .x0 , .i0} (LtZ (._ , i0)) = LtS (LtZ _)
      shiftright≤ {Ψ = x0 :: x :: Ψ} {i = .x0 , .i0} (LtZ (fst , iS i)) = LtS (LtZ _)
      shiftright≤ {Ψ = x0 :: []} (LtS {i = _ , ()} lt) 
      shiftright≤ {Ψ = x0 :: x1 :: Ψ} (LtS lt) = LtS (shiftright≤ lt)
      
      first≤ : ∀ {A} {xs : List A} {x} {j : Pos (xs ++ [ x ])} → (first {xs = xs} {x}) ≤ j
      first≤ {xs = []} = LtZ _
      first≤ {xs = x :: xs} = LtZ _
      
      same-index-in-rev≤ : ∀ {A} {Ψ : List A} {i j : Pos Ψ} → i ≤ j → same-index-in-rev i ≤ same-index-in-rev j
      same-index-in-rev≤ {Ψ = x :: Ψ} (LtZ i) = first≤ {_}{rev Ψ}
      same-index-in-rev≤ (LtS lt) = shiftright≤ (same-index-in-rev≤ lt)
      
      transport≤ : ∀ {A} {Ψ Ψ' : List A} (α : Ψ == Ψ') {i i' : Pos Ψ} → i ≤ i' → transport Pos α i ≤ transport Pos α i'
      transport≤ id lt = lt

      ListBijection : ∀ {A} → List A → List A → Type
      ListBijection xs ys = Equiv (Pos xs) (Pos ys)

  transport-List : ∀ {A} {M N : A} (C : A -> Type) (α : M ≃  N)
                   → transport (\ x -> List (C x)) α
                   ≃ ListM.map (transport C α) 
  transport-List C id = ! (λ≃ ListM.map-idfunc)
  
