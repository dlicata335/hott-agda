
{-# OPTIONS --type-in-type --without-K #-}

open import NoFunextPrelude

module Coprod where

  data Void : Set where

  data Either (A : Type) (B : Type) : Type where
      Inl : A -> Either A B
      Inr : B -> Either A B

  coe-Either-l : ∀ {A A' B B' : Type} {x} → (α : A == A') (β : B == B') → coe (ap2 Either α β) (Inl x) == Inl (coe α x)
  coe-Either-l id id = id

  coe-Either-r : ∀ {A A' B B' : Type} {x} → (α : A == A') (β : B == B') → coe (ap2 Either α β) (Inr x) == Inr (coe β x)
  coe-Either-r id id = id

  module Coprod (A : Type) (B : Type) where

    C : (x y : Either A B) → Type
    C (Inl a) (Inl a') = a == a'
    C (Inr b) (Inr b') = b == b'
    C _ _ = Void

    ΣC : Type
    ΣC = (Σ \ p -> C (fst p) (snd p))

    rearrange : (Either (Paths A) (Paths B)) ≃ ΣC
    rearrange = improve (hequiv f g gf fg) where
      f : (Either (Paths A) (Paths B))  → (Σ \ p -> C (fst p) (snd p))
      f (Inl ((x , y) , p)) = (Inl x , Inl y) , p
      f (Inr ((x , y) , p)) = (Inr x , Inr y) , p

      g : (Σ \ p -> C (fst p) (snd p)) → (Either (Paths A) (Paths B)) 
      g ((Inl x , Inl y) , p) = Inl ((x , y) , p)
      g ((Inr x , Inr y) , p) = Inr ((x , y) , p)
      g ((Inl x , Inr y) , ())
      g ((Inr x , Inl y) , ())

      fg : (x : _) → f (g x) == x
      fg ((Inl x , Inl x₁) , y) = id
      fg ((Inl x , Inr x₁) , ())
      fg ((Inr x , Inl x₁) , ())
      fg ((Inr x , Inr x₁) , y) = id

      gf : (y : _) → g (f y) == y
      gf (Inl x) = id
      gf (Inr x) = id

    coprodt : Paths (Either A B) ≃ ΣC
    coprodt = Paths (Either A B)         ≃〈 contract-Paths≃ 〉 
              Either A B                 ≃〈 coe-equiv (ap2 Either (ua (!equiv contract-Paths≃)) (ua (!equiv contract-Paths≃)))  〉 
              Either (Paths A) (Paths B) ≃〈 rearrange 〉 
              ΣC ∎∎

    pres-id-l : (x : A) → (fst coprodt ((Inl x , Inl x) , id)) == ((Inl x , Inl x) , id)
    pres-id-l x = fst coprodt ((Inl x , Inl x) , id)                                                                         =〈 id 〉
                  fst rearrange (coe (ap2 Either (ua (!equiv contract-Paths≃)) (ua (!equiv contract-Paths≃))) (Inl x)) =〈 ap (fst rearrange) (coe-Either-l (ua (!equiv contract-Paths≃)) (ua (!equiv contract-Paths≃))) 〉
                  fst rearrange (Inl (coe (ua (!equiv contract-Paths≃)) x))                                               =〈 ap (λ u → fst rearrange (Inl (u x))) (type=β (!equiv contract-Paths≃)) 〉
                  fst rearrange (Inl (fst (!equiv contract-Paths≃) x))                                                    =〈 id 〉
                  ((Inl x , Inl x) , id) ∎

    pres-id-r : (x : B) → (fst coprodt ((Inr x , Inr x) , id)) == ((Inr x , Inr x) , id)
    pres-id-r x = fst coprodt ((Inr x , Inr x) , id) =〈 id 〉
                  fst rearrange (coe (ap2 Either (ua (!equiv contract-Paths≃)) (ua (!equiv contract-Paths≃))) (Inr x)) =〈 ap (fst rearrange) (coe-Either-r (ua (!equiv contract-Paths≃)) (ua (!equiv contract-Paths≃))) 〉
                  fst rearrange (Inr (coe (ua (!equiv contract-Paths≃)) x))                                               =〈 ap (λ u → fst rearrange (Inr (u x))) (type=β (!equiv contract-Paths≃)) 〉
                  fst rearrange (Inr (fst (!equiv contract-Paths≃) x))                                                    =〈 id 〉
                  ((Inr x , Inr x) , id) ∎

    pres-fst : (x : _) → fst (fst coprodt x) == fst x
    pres-fst ((Inl x , .(Inl x)) , id) = ap fst (pres-id-l x)
    pres-fst ((Inr x , .(Inr x)) , id) = ap fst (pres-id-r x)

    coprod : (x y : Either A B) → (x == y) ≃ C x y
    coprod x y = fiberwise-equiv-from-total≃ coprodt pres-fst (x , y)
