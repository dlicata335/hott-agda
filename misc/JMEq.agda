{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude

module misc.JMEq where

  postulate 
    UIP : (A : Type) → HSet A

  module McBride where

    JMEq : (A B : Type) (a : A) (b : B) → Type
    JMEq A B a b = (α : A == B) → coe α a == b
  
    intro : (A : Type) (a : A) → JMEq A A a a 
    intro A a p = transport (λ p₁ → coe p₁ a == a) (HSet-UIP (UIP Type) _ _ id p) id
  
    scontr : {A : Type} {a a' : A} (p : JMEq A A a a') → Path{Σ \ a' → JMEq A A a a'} (a , intro A a) (a' , p)
    scontr {A} p = pair≃ (p id) (λ≃ (λ _ → HSet-UIP (UIP A) _ _ _ _)) -- uses funext
  
    elim : {A : Type} {M : A}
           (C : (x : A) → JMEq A A M x → Type)
        → (C M (intro A M))
        → {N : A} → (P : JMEq A A M N)
        → C N P
    elim C b p = transport (λ x → C (fst x) (snd x)) (scontr p) b
  
    lemma : {A : Type} {a : A} → (scontr (intro A a)) == id
    lemma = HSet-UIP (UIP _) _ _ _ _

    β : {A : Type} {M : A}
           (C : (x : A) → JMEq A A M x → Type)
        → (b : C M (intro A M))
        → (elim C b (intro A M)) == b
    β {A} {a} C b = transport (λ x → C (fst x) (snd x)) (scontr (intro A a)) b ≃〈 ap (λ X → transport (λ x → C (fst x) (snd x)) X b) lemma 〉 b ∎
    
