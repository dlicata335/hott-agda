
{-#  OPTIONS --type-in-type --without-K  #-}

open import lib.Prelude 
open Paths

module homotopy.Pi1Either where

module CaseForInl (A : Type) (B : Type) (a : A) where

 Cover : Either A B -> Type
 Cover (Inl a') = Path a a'
 Cover (Inr _) = Void

 encode : {e : Either A B} -> Path (Inl a) e -> Cover e
 encode α = transport Cover α id 

 inj : {a' : A} → Path (Inl a) (Inl a') → Path a a'
 inj {a'} = encode {Inl a'}

 dis : {b : B} → Path (Inl a) (Inr b) → Void
 dis {b} = encode {Inr b}

 decode : {e : Either A B} → Cover e → Path (Inl a) e
 decode {Inl a'} α = ap Inl α
 decode {Inr _} ()

 encode-decode : {e : Either A B} (c : Cover e)
               → encode{e} (decode{e} c) ≃ c
 encode-decode {Inl a'} α = 
  encode{Inl a'} (decode{Inl a'} α)               --  (1) 
    ≃〈 id 〉  
  transport Cover (ap Inl α) id                   --  (2) 
    ≃〈 ap≃ (! (transport-ap-assoc' Cover Inl α)) 〉 
  transport (Cover o Inl) α id                    --  (3) 
    ≃〈 id 〉 
  transport (λ a' → Id a a') α id               --  (4) 
    ≃〈 transport-Path-right α id 〉 
  α ∘ id                                          --  (5)                                        
    ≃〈 id 〉  
  α ∎                                             --  (6) 
 encode-decode {Inr _} ()

 decode-encode  : {e : Either A B} (α : Path (Inl a) e) 
                → Path (decode{e} (encode{e} α)) α
 decode-encode {e} α = 
   path-induction 
   (λ e' α' -> Path (decode{e'} (encode{e'} α')) α')
   id α

 eq : {e : Either A B} -> Path (Path (Inl a) e) (Cover e)
 eq{e} = ua (improve
    (hequiv  encode decode
             decode-encode (encode-decode{e})))

 injEquiv : {a' : A} →  
   Path (Path{Either A B} (Inl a) (Inl a')) (Path a a')
 injEquiv = eq

 disEquiv : {b : B} →
   Path (Path{Either A B} (Inl a) (Inr b)) Void
 disEquiv = eq  
