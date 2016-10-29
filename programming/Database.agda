{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude

module programming.Database where

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
    convert-record : (Nat × String × ((Nat × Nat) × Nat))
                   → (Nat × String × ((Nat × Nat) × Nat))
    convert-record = (λ {(key , name , ((day , month) , year)) → 
                             key , name , ((month , day) , year)})
  
    convert : DB -> DB
    convert = ListM.map convert-record
  
    test : convert euro ≃ american
    test = id

    map-fusion : ∀ {A B C} (g : B → C) (f : A → B) (l : List A) 
               → ListM.map (g o f) l ≃ ListM.map g (ListM.map f l)
    map-fusion g f [] = id
    map-fusion g f (x :: xs) = ap (_::_ (g (f x))) (map-fusion g f xs)

    map-idfunc : ∀ {A} (l : List A)
               → ListM.map (\ x -> x) l ≃ l
    map-idfunc [] = id
    map-idfunc (x :: xs) = ap (_::_ x) (map-idfunc xs)
  
    convert-inv : convert o convert ≃ (\ x -> x)
    convert-inv = 

                  convert o convert 
                    ≃〈 id 〉 

                  ListM.map convert-record o ListM.map convert-record
                    ≃〈 ! (λ≃ (map-fusion convert-record convert-record)) 〉 

                  ListM.map (convert-record o convert-record) 
                    ≃〈 id 〉 

                  ListM.map (\ x -> x) 
                    ≃〈 λ≃ ListM.map-idfunc 〉 

                  (λ x → x) ∎


  
  module HoTT where
    swapfn : ∀ {A B} → (A × B) → (B × A)
    swapfn (x , y) = (y , x)
    
    swap : ∀ {A B} → Equiv (A × B) (B × A)
    swap = equiv swapfn swapfn (λ _ → id) (λ _ → id) (λ _ → id)

    swap≃ : ∀ {A B} → (A × B) ≃ (B × A)
    swap≃ = ua swap

    convert : DB → DB
    convert = transport (\ A -> List (Nat × String × (A × Nat))) swap≃


    convert-inv : convert o convert ≃ (\ x -> x)
    convert-inv = let C = (\ A -> List (Nat × String × (A × Nat))) in 
                  
                  convert o convert 
                    ≃〈 id 〉 

                  transport C swap≃ o transport C swap≃  
                    ≃〈 ! (transport-∘ C swap≃ swap≃) 〉 

                  transport C (swap≃ ∘ swap≃)
                    ≃〈 ap (transport C) (type≃-ext (swap≃ ∘ swap≃) id (λ p → (ap≃ (type≃β swap) ∘ ap (λ f → coe swap≃ (f p)) (type≃β swap)) ∘ ap≃ (transport-∘ (λ x → x) swap≃ swap≃))) 〉 

                  transport C id
                    ≃〈 id 〉 

                  (λ x → x) ∎


    test : convert euro ≃ american
    test = ap≃ converts-same where
      converts-same : convert ≃ ByHand.convert
      converts-same =
        convert                                                          ≃〈 id 〉 

        transport (\ A -> List (Nat × String × (A × Nat))) swap≃         ≃〈 transport-List (λ A → Nat × String × A × Nat) swap≃ 〉 

        ListM.map (transport (\ A -> Nat × String × (A × Nat)) swap≃)    ≃〈 ap ListM.map (transport-×2 (λ A → String × A × Nat) swap≃) 〉 

        ListM.map (λ {(key , name , (month , day) , year)
                     → (key , transport (λ A → String × A × Nat) swap≃
                                        (name , (month , day) , year))})  ≃〈 ap ListM.map (λ≃ λ {(key , name , (month , day) , year) → ap (_,_ key) (ap≃ (transport-×2 (λ A → A × Nat) swap≃))}) 〉 

        ListM.map (λ {(key , name , (month , day) , year) → 
                      (key , name , 
                       (transport (λ A → A × Nat) swap≃ 
                                  ((month , day) , year)))})              ≃〈 ap ListM.map (λ≃ λ {(key , name , (month , day) , year) → ap (λ x → key , name , x) (ap≃ (transport-×1 (λ A → A) swap≃))}) 〉 

        ListM.map (λ {(key , name , (month , day) , year) → 
                      (key , name , 
                       (transport (λ A → A) swap≃ (month , day)) ,
                       year)})                                            ≃〈 ap ListM.map (λ≃ λ {(key , name , (month , day) , year) → ap (λ x → key , name , x , year) (ap≃ (type≃β swap))}) 〉 

        ListM.map (λ {(key , name , (month , day) , year) → 
                     (key , name , (swapfn (month , day) , year))})       ≃〈 id 〉 

        ListM.map (λ {(key , name , ((month , day) , year)) → 
                      (key , name , (day , month) , year)})               ≃〈 id 〉 

        ByHand.convert ∎


    data _≤_ : Nat → Nat → Set where

    thm : (p : Nat × Nat) → Either (fst p ≤ snd p) (snd p ≤ fst p)
    thm = {!!}

    thm' : (p : Nat × Nat) → Either (fst p ≤ snd p) (snd p ≤ fst p)
    thm' = {!apd thm swap≃!}
