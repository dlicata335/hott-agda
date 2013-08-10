{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude

module programming.Database-talk where

  DB : Type

  DB = List (Nat × String × ((Nat × Nat) × Nat))

  euro : DB 
  euro = 
    (4  , "John"  , ((30 , 5) , 1956)) ::
    (8  , "Hugo"  , ((29 , 12) , 1978)) ::
    (15 , "James" , ((1 , 7) , 1968)) ::
    (16 , "Sayid" , ((2 , 10) , 1967)) ::
    (23 , "Jack"  , ((3 , 12) , 1969)) ::
    (42 , "Sun"   , ((20 , 3) , 1969)) ::
    []

  american : DB 
  american = 
    (4  , "John"  , ((5 , 30) , 1956)) ::
    (8  , "Hugo"  , ((12 , 29) , 1978)) ::
    (15 , "James" , ((7 , 1) , 1968)) ::
    (16 , "Sayid" , ((10 , 2) , 1967)) ::
    (23 , "Jack"  , ((12 , 3) , 1969)) ::
    (42 , "Sun"   , ((3 , 20) , 1969)) ::
    []

  Bijection : Type -> Type -> Type
  Bijection = Equiv 

  transport-is-bijection :  (E : Type → Type) {b1 b2 : Type} 
                 → (α : Bijection b1 b2) → IsEquiv {(E b1)} {(E b2)} (transport E (ua α))
  transport-is-bijection E α = transport-isequiv E (ua α)

  is-bijection : {A B : Type}
     {f : A → B}
     (g : B → A)
     (α : (x : A) → Path (g (f x)) x)
     (β : (y : B) → Path (f (g y)) y)
     → IsEquiv f
  is-bijection {f = f} g α β = snd (improve (hequiv f g α β))

  map : ∀ {A B} → (A → B) → List A -> List B
  map = ListM.map

  module ByHand where

    conv1 : (Nat × String × ((Nat × Nat) × Nat))
          → (Nat × String × ((Nat × Nat) × Nat))
    conv1 (key , name , ((x , y) , year)) = 
          (key , name , ((y , x) , year))       
  
    convert : DB -> DB
    convert = map conv1
  
    map-fusion : ∀ {A B C} (g : B → C)
                 (f : A → B) (l : List A) 
               → map (g o f) l ≃ map g (map f l)
    map-fusion g f [] = id
    map-fusion g f (x :: xs) =
      ap (_::_ (g (f x))) (map-fusion g f xs)

    map-idfunc : ∀ {A} (l : List A) → map (\ x -> x) l ≃ l
    map-idfunc [] = id
    map-idfunc (x :: xs) = ap (_::_ x) (map-idfunc xs)
  
    convert-inv : convert o convert ≃ (λ x -> x)
    convert-inv = map conv1 o map conv1 
                   ≃〈 ! (λ≃ (map-fusion conv1 conv1)) 〉 
                  map (conv1 o conv1)
                   ≃〈 id 〉 
                  map (\ x -> x)
                   ≃〈 λ≃ map-idfunc 〉 
                  (λ x → x) ∎

    convert-bijection : Bijection DB DB 
    convert-bijection =
      (convert , 
       is-bijection convert 
                    (λ x -> (ap≃ convert-inv))
                    (λ x -> (ap≃ convert-inv)))


  
  module HoTT where

    swapf : (Nat × Nat) → (Nat × Nat)
    swapf (x , y) = (y , x)

    swap : Bijection (Nat × Nat) (Nat × Nat)
    swap = (swapf ,
            is-bijection swapf (λ _ → id) (λ _ → id))

    There : Type -> Type
    There A = List (Nat × String × A × Nat)

    convert : DB → DB
    convert = transport There (ua swap)

    convert-bijection : Bijection DB DB
    convert-bijection =
      (convert , transport-is-bijection There swap)


{-
    test : convert euro ≃ american
    test = converts-same euro where
      converts-same : (db : _) → convert db ≃ ByHand.convert db
      converts-same db =

             convert db                                            ≃〈 {!!} 〉 
             
        |->  transport (λ A → List (Nat × String × A × Nat)) swap db  ≃〈 {!!} 〉 
             
        |->  map (transport (λ A → Nat × String × A × Nat) swap) db     ≃〈 {!!} 〉 
             
        |->  map (λ (key , name , (x , y) , year) → 
                    (key , name , 
                     transport (λ A → A) swap (x , y) ,
                     year)) db                                    ≃〈 {!!} 〉 
             
        |->  map (λ (key , name , (x , y) , year) → 
                    (key , name , (y , x) , year)) db             ≃〈 {!!} 〉 

        ByHand.convert db ∎
-}