
{-# OPTIONS --type-in-type #-}

open import lib.Prelude

module programming.rbt.Delete where

  data Order : Type where
    Less Greater Equal : Order

  module RBT (Key : Set) (compare : Key -> Key -> Order) (Value : Set) where 

    data Color : Set where
      Red : Color
      Black : Color

    -- induction-induction version
    mutual
      data WellRedTree : Nat → Set where
        Empty : WellRedTree 1
        RedNode  : ∀ {n} (l : WellRedTree n)
                 → (kv : Key × Value)
                 → (r : WellRedTree n)
                 → (rl : RootColored l Black)
                 → (rr : RootColored r Black)
                 → WellRedTree n 
        BlackNode : ∀ {n} (l : WellRedTree n)
                 → (kv : Key × Value)
                 → (r : WellRedTree n)
                 → WellRedTree (S n)

      data RootColored : ∀ {n : Nat} → WellRedTree n -> Color -> Set where
        RC-Empty : RootColored Empty Black
        RC-Red   : {n : Nat} {l : WellRedTree n} {kv : Key × Value} {r : WellRedTree n} {cl : RootColored l Black} {cr : RootColored r Black} → RootColored (RedNode l kv r cl cr) Red
        RC-Black : {n : Nat} {l : WellRedTree n} {kv : Key × Value} {r : WellRedTree n} → RootColored (BlackNode l kv r) Black
  

    incr-if-black : Color -> Nat -> Nat
    incr-if-black Red x = x
    incr-if-black Black x = S x

    data AlmostWellRedTree : Nat → Set where
      AEmpty : AlmostWellRedTree 1
      ANode  :  ∀ {n} (l : WellRedTree n)
              → (c : Color)
              → (kv : Key × Value)
              → (r : WellRedTree n)
              → AlmostWellRedTree (incr-if-black c n)

    -- input color is implicitly black 
    balance-left : ∀ {n} → AlmostWellRedTree n
                 → Key × Value
                 → WellRedTree n
                 → WellRedTree (S n)
    -- these are the two rotation cases
    balance-left (ANode (RedNode a x b ra rb) Red y c) z d = RedNode (BlackNode a x b) y (BlackNode c z d) RC-Black RC-Black
    balance-left (ANode a Red x (RedNode b y c rb rc)) z d = RedNode (BlackNode a x b) y (BlackNode c z d) RC-Black RC-Black
    -- need to expand the catch-all, because the *proof* is different in each case.  
    balance-left AEmpty kv r = BlackNode Empty kv r
    balance-left (ANode a Black x b) kv r = BlackNode (BlackNode a x b) kv r 
    balance-left (ANode Empty Red x Empty) kv r = BlackNode (RedNode Empty x Empty RC-Empty RC-Empty) kv r
    balance-left (ANode Empty Red x (BlackNode l kv r)) kv' r' = BlackNode (RedNode Empty x (BlackNode l kv r) RC-Empty RC-Black) kv' r'
    balance-left (ANode (BlackNode a1 x1 a2) Red x Empty) y c = BlackNode (RedNode (BlackNode a1 x1 a2) x Empty RC-Black RC-Empty) y c
    balance-left (ANode (BlackNode a1 x1 a2) Red x (BlackNode b1 y1 b2)) y c = BlackNode (RedNode (BlackNode a1 x1 a2) x (BlackNode b1 y1 b2) RC-Black RC-Black) y c

    -- input color is implicitly black 
    balance-right : ∀ {n} → WellRedTree n → Key × Value → AlmostWellRedTree n → WellRedTree (S n)
    -- these are the two rotation cases
    balance-right a x (ANode (RedNode b y c _ _) Red z d) = RedNode (BlackNode a x b) y (BlackNode c z d) RC-Black RC-Black
    balance-right a x (ANode b Red y (RedNode c z d _ _)) = RedNode (BlackNode a x b) y (BlackNode c z d) RC-Black RC-Black
    -- catch-all 
    balance-right a x AEmpty = BlackNode a x Empty
    balance-right a x (ANode Empty Red kv Empty) = BlackNode a x (RedNode Empty kv Empty RC-Empty RC-Empty)
    balance-right a x (ANode Empty Red kv (BlackNode l kv' r)) = BlackNode a x (RedNode Empty kv (BlackNode l kv' r) RC-Empty RC-Black)
    balance-right a x (ANode (BlackNode l kv r) Red kv' Empty) = BlackNode a x (RedNode (BlackNode l kv r) kv' Empty RC-Black RC-Empty)
    balance-right a x (ANode (BlackNode l kv r) Red kv' (BlackNode l' kv0 r')) = BlackNode a x (RedNode (BlackNode l kv r) kv' (BlackNode l' kv0 r') RC-Black RC-Black)
    balance-right a x (ANode l Black kv r) = BlackNode a x (BlackNode l kv r)

    -- input color is implicitly red
    balance-break : ∀ {n} → WellRedTree n
                  → Key × Value
                  → WellRedTree n
                  → AlmostWellRedTree n
    balance-break l kv r = ANode l Red kv r

    decide-root : ∀ {n} (t : WellRedTree n) → Either (RootColored t Black) (RootColored t Red)
    decide-root Empty = Inl RC-Empty
    decide-root (RedNode _ _ _ _ _) = Inr RC-Red
    decide-root (BlackNode _ _ _) = Inl RC-Black

    promote : ∀ {n} → WellRedTree n -> AlmostWellRedTree n
    promote Empty = AEmpty 
    promote (RedNode l kv r _ _) = ANode l Red kv r
    promote (BlackNode l kv r)   = ANode l Black kv r

    mutual
      ins-red : ∀ {n} (t : WellRedTree n) (kv : Key × Value) → RootColored t Red → AlmostWellRedTree n
      ins-red Empty kv ()
      ins-red (RedNode l (k' , v') r rl rr) (k , v) rc with compare k k' 
      ... | Less = balance-break (ins-black l (k , v) rl) (k' , v') r
      ... | Greater = balance-break l (k' , v') (ins-black r (k , v) rr)
      ... | Equal = ANode l Red (k , v) r
      ins-red (BlackNode l kv r) kv' ()

      ins-black : ∀ {n} (t : WellRedTree n) (kv : Key × Value) → RootColored t Black → WellRedTree n
      ins-black Empty kv rt = RedNode Empty kv Empty RC-Empty RC-Empty
      ins-black (RedNode l kv r rl rr) kv' ()
      ins-black (BlackNode l (k' , v') r) (k , v) rt with compare k k'
      ... | Less = balance-left (ins-any l (k , v)) (k' , v') r
      ... | Greater = balance-right l (k , v) (ins-any r (k , v))
      ... | Equal = BlackNode l (k , v) r

      ins-any : ∀ {n} (t : WellRedTree n) (kv : Key × Value) -> AlmostWellRedTree n
      ins-any t kv with decide-root t 
      ... | Inl rt = promote (ins-black t kv rt)
      ... | Inr rt = ins-red t kv rt 

    blacken-root : ∀ {n} → AlmostWellRedTree n → Σ \ m → WellRedTree m
    blacken-root AEmpty = _ , Empty
    blacken-root (ANode l _ kv r) = _ , BlackNode l kv r

    insert : ∀ {n} → WellRedTree n → Key × Value → Σ \ m -> WellRedTree m
    insert t kv = blacken-root (ins-any t kv)

    
