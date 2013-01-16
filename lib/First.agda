
module lib.First where

 -- Agda uses the word "Set" in a way that I want to suppress
 Type = Set

 _o_ : {A B C : Type} → (B → C) → (A → B) → A → C
 g o f = \ x → g (f x)
 infixr 10 _o_
   
