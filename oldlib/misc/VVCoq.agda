{- Some of Voevodsky's equivalence axiom Coq code
    (available from http://www.math.ias.edu/~vladimir/Site3/home_files/2010_3_3_foundations_post.v)
    transliterated to Agda 

   Dan Licata, March 2010 

CODE ROT: no longer compiles
-}
    
{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude hiding (HFiber ; WEq ; WEqBy)

module misc.VVCoq where

  {- Definition of "paths": identity type with refl (id) and J #-}
  module MyPaths where
    postulate 
      Path  : {A : Set} -> A -> A -> Set 
      id  : {A : Set} {x : A} -> Path x x
      J     : {A : Set} -> (C : (x y : A) -> Path x y -> Set) 
            -> ((x : A) -> C x x id) -> {M N : A} (P : Path M N) 
            -> C M N P
      Jcomp : {A : Set} -> (C : (x y : A) -> Path x y -> Set) 
            -> (b : (x : A) -> C x x id) -> {M : A} 
            -> Id (J C b id) (b M)
  
    subst : ∀ {A} (C : A -> Set) -> {x y : A} -> Path x y -> C x -> C y
    subst C path = J (\ x y _ -> C x -> C y) (\ _ y -> y) path 

    sym : ∀ {A} {x y : A} -> Path x y -> Path y x
    sym p = J (\ x y _ -> Path y x) (\ _ -> id) p
  
    trans : ∀ {A} {x y z : A} -> Path x y -> Path y z -> Path x z
    trans {A}{x} p1 p2 = subst (\ z -> Path x z) p2 p1 
  
    pairη : ∀ {A}{B : A -> Set} {p : Σ B} -> Path p (fst p , snd p)
    pairη {_}{_}{(x , y)} = id

    uipΣ2 : ∀ {A}{ x y : A} (p : Path x y) -> Path {Σ \x -> Path x y} (x , p) (y , id) 
    uipΣ2 {x}{y} p = J (\ x' y' p' -> Path{Σ \z -> Path z y'} (x' , p') ( y' , id) ) (\ x -> id) p

    irrelΣ2 : ∀ {A}{ y : A} (p q : Σ \x -> Path x y) 
            -> Path p q
    irrelΣ2 p q = trans (trans pairη (trans (uipΣ2 (snd p)) (sym (uipΣ2 (snd q))))) (sym pairη) 

    paircong : ∀ {A}{B : A -> Set} {x x' : A} {y : B x}{y' : B x'}
             -> (p : Path x x') -> Path (subst B p y) y'
             -> Path {Σ B} (x , y) (x' , y')
    paircong = {!!}

{-  
    lemma : ∀ {A B}{y : B}{f : A -> B} (p q : Σ \ x -> Path (f x) y)
          -> Path {Σ \z -> Path z y} (f (fst p) , snd p) (f (fst q) , snd q)
          -> Path (fst p) (fst q)
          -> Path {Σ \x -> Path (f x) y} (fst p , snd p) (fst q , snd q)
    lemma p q r l = paircong l {!!}

    irrelΣ2fiber : ∀ {A B}{f : A -> B}{y : B} (p q : Σ \x -> Path (f x) y)
            -> Path (fst p) (fst q)
            -> Path p q
    irrelΣ2fiber{A}{B}{f}{y} p q pth = trans (trans pairη ( (lemma p q ( (trans (uipΣ2 (snd p)) 
                                       (sym (uipΣ2 (snd q)))) )  pth) )) (sym pairη) 
-}

    resp : ∀ {A B} (f : A -> B) -> {x y : A} -> Path x y -> Path (f x) (f y)
    resp f path = J (\ x y _ -> Path (f x) (f y)) (\ x -> id) path

  open MyPaths

  {- Weak equivalence -}
  module WEq where
    -- contractible
    Contr : Set -> Set
    Contr A = Σ \ (t : A) -> (x : A) -> Path x t
  
    HFiber : {A B : Set} -> (A -> B) -> B -> Set
    HFiber f y = Σ \x -> Path (f x) y
  
    WEqBy : (A B : Set) -> (f : A -> B) -> Set
    WEqBy A B f = (y : _) -> Contr (HFiber f y)
  
    WEq : (A B : Set) -> Set
    WEq A B = Σ \f -> WEqBy A B f
  open WEq

  {- can get a weaken equivalence from an identity -}
  module PathsToWEq where
    idweq : ∀ {A} -> WEqBy A A (\ x -> x)
    idweq y = (y , id) ,  \ p -> trans pairη (uipΣ2 (snd p))  
  
    pathToWEq : ∀ {A B : Set} -> Path A B -> WEq A B
    pathToWEq p = J (\ x y _ -> WEq x y) (\ y -> (\ x -> x) , idweq) p
  open PathsToWEq

  {- equivalence axiom implies that you get identity from weak equivalence -}
  module WEqToPaths where
    postulate
      equivaxiom : ∀ {A B : Set} -> WEqBy (Path A B) (WEq A B) pathToWEq 
  
    eaΣ : ∀ {A B : Set} -> WEq (Path A B) (WEq A B) 
    eaΣ = pathToWEq , equivaxiom
  
    back : ∀ {A B : Set} -> WEq A B -> (B -> A)
    back (f , by) b = fst (fst (by b))
  
    wEqToPath : ∀ {A B : Set} -> WEq A B -> Path A B 
    wEqToPath w = back eaΣ w
  open WEqToPaths 


  {- However, because all identity types are interprovable, we can
     get a contradiction anyway, because normal Agda 'Id' has uip -}

  module Whoops where

    -- UIP holds for Path anyway, whoops

    pathToId : {A : Set} {x y : A} -> (p : Path x y) -> Id x y
    pathToId p = J (\ x y _ -> Id x y) (\ _ -> Refl) p

    idToPath : {A : Set} {x y : A} -> Id x y -> Path x y
    idToPath Refl = id

    comp1 : {A : Set} {x y : A} -> (p : Path x y) -> Id (idToPath (pathToId p)) p
    comp1 p =  J (\ x y p' -> Id (idToPath (J (\ x y _ -> Id x y) (\ _ -> Refl) p')) p') 
                 (\ x -> (resp idToPath (Jcomp (λ x' y' _ → Id x' y') (\ _ -> Refl)))) p 

    comp2 : {A : Set} {x y : A} -> (p : Id x y) -> Id (pathToId (idToPath p)) p
    comp2 Refl = Jcomp (\ x y _ -> Id x y) (\ _ -> Refl) 

    uipId : {A : Set} {x : A} -> (p : Id x x) -> Id p Refl
    uipId Refl = Refl

    uip : {A : Set} {x : A} -> (p : Path x x) -> Id p id
    uip p = trans (sym (comp1 p)) (resp idToPath (uipId (pathToId p)))

    Connected : Set -> Set
    Connected A = ( x y : A) -> Path x y 

    pathIsCon : {A : Set} {x y : A} -> Connected (Path x y)
    pathIsCon p = J (\ x' y' p -> (q : Path x' y') -> Path p q) (\ x q -> idToPath (sym (uip q))) p

    wEqIsCon : {x y : Set} -> Connected (WEq x y)
    wEqIsCon = subst Connected (wEqToPath eaΣ)  pathIsCon 

  {- copied from the standard library -}
  module PathReasoning where
    -- FIXME abstract

    data _IsRelatedTo_ {A : Set} (x y : A) : Set where
      relTo : (x∼y : Path x y) → x IsRelatedTo y
    
    begin_ : ∀ {A} {x y : A} → x IsRelatedTo y → Path x y
    begin (relTo p) = p
    
    _≡⟨_⟩_ : ∀ {A} (x : A) {y z} → Path x y → y IsRelatedTo z → x IsRelatedTo z
    _ ≡⟨ x∼y ⟩ relTo y∼z = relTo (trans x∼y y∼z)
    
    --     _≈⟨_⟩_ : ∀ x {y z} → x ≈ y → y IsRelatedTo z → x IsRelatedTo z
    --     _ ≈⟨ x≈y ⟩ relTo y∼z = relTo (trans (reflexive x≈y) y∼z)
    
    _∎ : ∀ {A} (x : A) → x IsRelatedTo x
    _∎ _ = relTo id

    infix  4 _IsRelatedTo_
    infix  2 _∎
    infixr 2 _≡⟨_⟩_
    infix  1 begin_

  module Examples where
   open PathReasoning

{-    
   module Normal where

    left : Bool -> Either Unit Unit
    left True = Inl <>
    left False = Inr <>

    right : Either Unit Unit -> Bool
    right (Inl _) = True
    right (Inr _) = False

    comp1 : (b : Bool) -> Path (right (left b)) b
    comp1 True = id
    comp1 False = id

    comp2 : (b : Either Unit Unit) -> Path (left (right b)) b
    comp2 (Inl _) = id
    comp2 (Inr _) = id

    pf : WEq Bool (Either Unit Unit)
    pf = left , 
         \ image -> (right image , comp2 image ) , 
         \ p ->  trans pairη ( (paircong (trans (sym (comp1 _)) (resp right (snd p))) {!!}) ) 
-}
{-
       pth : (image : Either Unit Unit) (p : Σ (\ (x : Bool) → Path (left x) image)) 
           -> Path
            (J (λ x y _ → Path (left x) image → Path (left y) image)
             (λ _ y → y)
             (J (λ x y _ → Path (fst p) x → Path (fst p) y) (λ _ y → y)
              (J (λ x y _ → Path (right x) (right y)) (λ x → id) (snd p))
              (J (λ x y _ → Path y x) (λ _ → id) (comp1 (fst p))))
             (snd p))
            (comp2 image)
       pth (Inl _) (True , p') = {!!}
         {!
         begin 
            (J (λ x y _ → Path (left x) (Inl _) → Path (left y) (Inl _))
             (λ _ y → y)
             (J (λ x y _ → Path True x → Path True y) (λ _ y → y)
              (J (λ x y _ → Path (right x) (right y)) (λ x → id) p')
              (J (λ x y _ → Path y x) (\ _ -> id) id))
             p')
           ≡⟨ {!!} ⟩ 
            (J 
             (λ x y _ → Path (left x) (Inl _) → Path (left y) (Inl _))
             (λ _ y → y)
             (J (λ x y _ → Path True x → Path True y) (λ _ y → y)
              (J (λ x y _ → Path (right x) (right y)) (λ x → id) p')
              id)
             p')
           ≡⟨ {!!} ⟩ 
            (J 
             (λ x y _ → Path (left x) (Inl _) → Path (left y) (Inl _))
             (λ _ y → y)
             (J (λ x y _ → Path True x → Path True y) (λ _ y → y)
              (J (λ x y _ → Path (right x) (right y)) (λ x → id) p')
              id)
             p')
           ≡⟨ {!!} ⟩ 
            id 
           ∎  
       !}
       pth (Inl _) (False , p') = {! begin ≡⟨   ⟩ (comp2 image) ∎!}
       pth (Inr _) f = {! begin ≡⟨   ⟩ (comp2 image) ∎!}
-}
{-
   module Flip where

    left : Bool -> Either Unit Unit
    left True = Inr <>
    left False = Inl <>

    right : Either Unit Unit -> Bool
    right (Inr _) = True
    right (Inl _) = False

    comp1 : (b : Bool) -> Path (right (left b)) b
    comp1 True = id
    comp1 False = id

    comp2 : (b : Either Unit Unit) -> Path (left (right b)) b
    comp2 (Inl _) = id
    comp2 (Inr _) = id

    pf : WEq Bool (Either Unit Unit)
    pf = left , 
         \ image -> (right image , comp2 image ) , 
         \ p ->  trans pairη {! (paircong (trans (sym (comp1 _)) (resp right (snd p))) {!!}) !}

   module XXX where
     open Whoops

     identify : Path Normal.pf Flip.pf
     identify = wEqIsCon Normal.pf Flip.pf 

     wrong : Path True False
     wrong = resp (\ x -> back x (Inl _)) identify

     contra : Void
     contra = subst Check wrong _
-}  
{-
  -- other true things about Paths

  uipΣ : ∀ {A}{ x y : A} (p : Path x y) -> Path {Σ \ x -> Σ \y -> Path x y} (x , y , p) (x , x , id)
  uipΣ = {!!}
-}