{-# OPTIONS --type-in-type --without-K #-}

module misc.UniBug241 where

data Id {A : Set} (M : A) : A → Set where
  id : Id M M

_==_ : {A : Set} → A → A → Set
_==_ = Id

_∘_  : {A : Set} {M N P : A} 
      → N == P → M == N → M == P
β ∘ id = β

record Unit : Set where
    constructor <> 

data Unit⁺ : Set where
    <>⁺ : Unit⁺

ap :  {A B : Set} {M N : A}
       (f : A → B) → M == N → (f M) == (f N)
ap f id = id

-- gadget for defeating unused argument check in Agda 2.3.2.1 and later
-- a version of Unit⁺ that's indexed by an arbitrary thing.  
record Phantom {A : Set}(a : A) : Set where
    constructor phantom
    field 
      match : Unit⁺

module S¹ where
  private
    module S where
      private
        data S¹' : Set where
          Base : S¹'

        data S¹'' : Set where
          mkS¹'' : S¹' → (Unit -> Unit) → S¹'' -- unit->unit is defeat injectivity check
    
      S¹ : Set
      S¹ = S¹''
    
      base : S¹
      base = mkS¹'' Base _
    
      postulate {- HoTT Axiom -}
        loop : base == base
    
      S¹-rec' : {C : Set} 
             -> (c : C)
             -> (α : c == c) (_ : Phantom α) -- phantom is to defeat unused argument check
             -> S¹ -> C
      S¹-rec' a _ (Phantom.phantom <>⁺) (mkS¹'' Base _) = a

      S¹-rec : {C : Set} 
               -> (c : C)
               -> (α : c == c)
               -> S¹ -> C
      S¹-rec a α = S¹-rec' a α (Phantom.phantom <>⁺)
    
  open S public

-- 
notbad : S¹.S¹ == S¹.S¹
notbad = {!!}

bad : S¹.S¹ → S¹.S¹
bad = S¹.S¹-rec S¹.base {!!}

bad' : S¹.S¹ → S¹.S¹
bad' = S¹.S¹-rec S¹.base S¹.loop

notbad2 : (S¹.base == S¹.base) → S¹.S¹ → S¹.S¹
notbad2 t = S¹.S¹-rec S¹.base {!!}

notbad3 : ap bad' S¹.loop == id
notbad3 = {!id!}

l = S¹.loop

notbad4 : S¹.S¹ → S¹.S¹
notbad4 = S¹.S¹-rec S¹.base {!!}

