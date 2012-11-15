{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open Paths

module applications.Pi1Either where

  module CaseForInl (A : Set) (B : Set) (a : A) where

    C : Either A B -> Set
    C (Inl a') = a ≃ a'
    C (Inr _) = Void

    encode : ∀ {e : Either A B} -> Inl a ≃ e -> C e
    encode α = subst C α Refl 

    decode : ∀ {e : Either A B} -> C e -> Inl a ≃ e
    decode {Inl a'} α = resp Inl α
    decode {Inr _} ()

    encode-decode : ∀ {e : Either A B} (p : C e) -> encode{e} (decode{e} p) ≃ p
    encode-decode {Inl a'} α = subst C (resp Inl α) Refl ≃〈 app≃ (subst-resp' C Inl α) 〉
                               subst (λ a' → Id a a') α Refl ≃〈 subst-Id-post α Refl 〉 
                               α ∘ Refl ≃〈 Refl 〉 
                               α ∎
    encode-decode {Inr _} ()

    decode-encode : ∀ {e : Either A B} (α : Inl a ≃ e) -> decode{e} (encode{e} α) ≃ α
    decode-encode Refl = Refl

    inlinl : ∀ {a'} -> (Inl{A}{B} a ≃ Inl a') ≃ (a ≃ a')
    inlinl {a'} = ua (isoToAdj(encode , isiso decode (encode-decode {Inl a'}) decode-encode))

    inlinr : {b : B} -> (Inl{A}{B} a ≃ Inr b) ≃ Void
    inlinr {b} = ua (isoToAdj(encode , isiso decode (encode-decode {Inr b}) decode-encode))
    
  -- copy and paste: is there a better way?  
  module CaseForInr (A : Set) (B : Set) (b : B) where

    C : Either A B -> Set
    C (Inr b') = b ≃ b'
    C (Inl _) = Void

    encode : ∀ {e : Either A B} -> Inr b ≃ e -> C e
    encode α = subst C α Refl 

    decode : ∀ {e : Either A B} -> C e -> Inr b ≃ e
    decode {Inr b'} α = resp Inr α
    decode {Inl _} ()

    encode-decode : ∀ {e : Either A B} (p : C e) -> encode{e} (decode{e} p) ≃ p
    encode-decode {Inr b'} α = subst C (resp Inr α) Refl ≃〈 app≃ (subst-resp' C Inr α) 〉
                               subst (λ b' → Id b b') α Refl ≃〈 subst-Id-post α Refl 〉 
                               α ∘ Refl ≃〈 Refl 〉 
                               α ∎
    encode-decode {Inl _} ()

    decode-encode : ∀ {e : Either A B} (α : Inr b ≃ e) -> decode{e} (encode{e} α) ≃ α
    decode-encode Refl = Refl

    inlinl : ∀ {b'} -> (Inr{A}{B} b ≃ Inr b') ≃ (b ≃ b')
    inlinl {b'} = ua (isoToAdj(encode , isiso decode (encode-decode {Inr b'}) decode-encode))

    inlinr : {a : A} -> (Inr{A}{B} b ≃ Inl a) ≃ Void
    inlinr {a} = ua (isoToAdj(encode , isiso decode (encode-decode {Inl a}) decode-encode))
    