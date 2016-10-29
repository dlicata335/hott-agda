
{-# OPTIONS --without-K #-}

open import Agda.Primitive

module Heterogeneous where

  data Id {l : Level} {A : Set l} (M : A) : A → Set where
   Refl : Id M M

  ap : {l1 l2 : Level} {A : Set l1} {B : Set l2} {M N : A} (f : A → B) → Id M N → Id (f M) (f N)
  ap f Refl = Refl

  data HId {A : Set} (M : A) : {B : Set} → B → Set where
   HRefl : HId M M

  coe : {A B : Set} → Id A B → A → B
  coe Refl a = a

  het-to-hom1 : {A B : Set} {a : A} {b : B} → HId a b → Id A B
  het-to-hom1 HRefl = Refl

  het-to-hom2 : {A B : Set} {a : A} {b : B} → (p : HId a b) → Id (coe (het-to-hom1 p) a) b
  het-to-hom2 HRefl = Refl

  hom-to-het : {A B : Set} {a : A} {b : B} → (p : Id A B) → Id (coe p a) b → HId a b
  hom-to-het Refl Refl = HRefl

  hom-to-het-to-hom1 : {A B : Set} {a : A} {b : B} → (p : Id A B) (q : Id (coe p a) b) → Id (het-to-hom1 (hom-to-het p q)) p 
  hom-to-het-to-hom1 Refl Refl = Refl

  hom-to-het-to-hom2 : {A B : Set} {a : A} {b : B} → (p : Id A B) (q : Id (coe p a) b) 
                     → Id (coe (ap (\ x → Id (coe x a) b) (hom-to-het-to-hom1 p q)) (het-to-hom2 (hom-to-het p q))) q 
  hom-to-het-to-hom2 Refl Refl = Refl

  het-to-hom-to-het : {A B : Set} {a : A} {b : B} → (p : HId a b) → Id (hom-to-het (het-to-hom1 p) (het-to-hom2 p)) p
  het-to-hom-to-het HRefl = Refl
