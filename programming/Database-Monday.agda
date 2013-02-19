{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude

module programming.Database-starter where

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

  module ByHand where

    convert-record : Nat × String × (Nat × Nat) × Nat 
                   → Nat × String × (Nat × Nat) × Nat 
    convert-record (key , name , (day , month) , year) = 
                   (key , name , (month , day) , year)

    convert : DB -> DB
    convert d = ListM.map convert-record d
  
    -- id : {A : Type} {M : A} -> M ≃ M

    test : convert euro ≃ american
    test = id

    map-fusion : ∀ {A B C} (g : B -> C) (f : A -> B)
               -> ListM.map (g o f) ≃ ListM.map g o ListM.map f
    map-fusion {A} g f = λ≃ pointwise where
      pointwise : (l : List A) → 
                  ListM.map (g o f) l 
                ≃ ListM.map g (ListM.map f l)
      pointwise [] = id
      pointwise (x :: xs) =
        ap2 _::_ id (pointwise xs)

    map-idfunc : ∀ {A} -> ListM.map (\ (x : A) -> x) 
                        ≃ (\ x -> x)
    map-idfunc {A} = λ≃ pointwise where
      pointwise : (l : List A) → ListM.map (\ x -> x) l
                               ≃ l
      pointwise [] = id
      pointwise (y :: y') = ap2 _::_ id (pointwise y')
    
    inverse : convert o convert ≃ (λ x -> x)
    inverse = convert o convert           ≃〈 id 〉 

              ListM.map convert-record o
              ListM.map convert-record    ≃〈 ! (map-fusion convert-record convert-record) 〉 

              ListM.map (convert-record o 
                         convert-record)  ≃〈 id 〉

              ListM.map (λ x → x)  ≃〈 map-idfunc 〉
              
              (λ x → x) ∎