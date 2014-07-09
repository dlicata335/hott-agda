{-# OPTIONS --type-in-type --new-without-K #-}

open import lib.Prelude

open Truncation

module homotopy.EncodeDecode where

  module ForLoopSpace (A : Type) (a0 : A)
                      (Codes : A → Type) (c0 : Codes a0)
                      (decode : {x : A} -> Codes x -> Path a0 x)
                      (encode-decode' : (c : Codes a0) -> transport Codes (decode{a0} c) c0 ≃ c)
                      (decode-encode-id : decode c0 ≃ id)
                      where

    encode : {x : A} → Path a0 x -> Codes x
    encode α = transport Codes α c0

    decode-encode : {x : A} -> (α : Path a0 x) → decode (encode α) ≃ α
    decode-encode id = decode-encode-id

    lemma : Equiv (Path a0 a0) (Codes a0) 
    lemma = improve (hequiv encode decode decode-encode encode-decode')

  module ForTruncatedLoopSpace (A : Type) (a0 : A) (k : _)
                               (Codes : A → Type) (nCodes : (x : A) → NType k (Codes x)) (c0 : Codes a0)
                               (decode : {x : A} -> Codes x -> Trunc k (Path a0 x))
                               (encode-decode' : (c : Codes a0) -> Trunc-rec (nCodes _) (\ α -> transport Codes α c0) (decode{a0} c) ≃ c)
                               (decode-encode-id : decode c0 ≃ [ id ])
                               where

    encode : {x : A} → Trunc k (Path a0 x) -> Codes x
    encode tα = Trunc-rec (nCodes _) (\ α -> transport Codes α c0) tα

    decode-encode : {x : A} -> (tα : Trunc k (Path a0 x)) → decode (encode tα) ≃ tα
    decode-encode = Trunc-elim _ (λ _ → path-preserves-level Trunc-level) 
                                 (path-induction (λ x α → decode (encode [ α ]) ≃ [ α ])
                                                 decode-encode-id) 

    lemma : Equiv (Trunc k (Path a0 a0)) (Codes a0) 
    lemma = improve (hequiv encode decode decode-encode encode-decode')

