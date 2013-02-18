{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude

module programming.Database where

  -- Bijection : Type -> Type -> Type
  -- Bijection = Equiv 

  -- bij : {A B : Type}
  --       (f : A → B)
  --       (g : B → A)
  --       (α : (x : A) → Path (g (f x)) x)
  --       (β : (y : B) → Path (f (g y)) y)
  --       → Equiv A B
  -- bij f g α β = improve (hequiv f g α β)

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
  
    convert-inv : convert o convert ≃ (\ x -> x)
    convert-inv = convert o convert ≃〈 id 〉 
                  ListM.map convert-record o ListM.map convert-record ≃〈 {!!} 〉 
                  ListM.map convert-record o ListM.map convert-record ≃〈 {!!} 〉 
                  (λ x → x) ∎
  
  module HoTT where
    swap : ∀ {A B} → Equiv (A × B) (B × A)
    swap = equiv (λ {(x , y) → y , x})
                 (λ {(x , y) → y , x})
                 (λ _ → id)
                 (λ _ → id)
                 (λ _ → id)

    swap≃ : ∀ {A B} → (A × B) ≃ (B × A)
    swap≃ = ua swap

    !swap≃ : ∀ {A B} → swap≃ ≃ ! (swap≃{A}{B})
    !swap≃ = ! (!-ua swap)

    convert : DB → DB
    convert = transport (\ A -> List (Nat × String × (A × Nat)))  swap≃

    convert-inv : convert o convert ≃ (\ x -> x)
    convert-inv = let C = (\ A -> List (Nat × String × (A × Nat))) in 
                  
                  convert o convert
                    ≃〈 id 〉 

                  transport C swap≃
                  o transport C swap≃
                    ≃〈 ap (λ x → transport C swap≃ o transport C x) !swap≃ 〉 

                  transport C swap≃
                  o transport C (! swap≃) 
                    ≃〈 transport-inv-2 C swap≃ 〉 

                  (λ x → x) ∎

    test : convert euro ≃ american
    test = ap≃ converts-same where
      converts-same : convert ≃ ByHand.convert
      converts-same =
        convert
          ≃〈 {!!} 〉 
        transport (\ A -> List (Nat × String × (A × Nat))) swap≃ 
          ≃〈 {!!} 〉 
        ListM.map (transport (\ A -> Nat × String × (A × Nat)) swap≃)
          ≃〈 {!!} 〉 
        ByHand.convert ∎
