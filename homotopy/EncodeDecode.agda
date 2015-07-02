{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open import lib.cubical.Cubical

open Truncation

module homotopy.EncodeDecode where

  module ForLoopSpace (A : Type) (a0 : A)
                      (Codes : A → Type) 
                      (c0 : Codes a0)
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


  -- strengthened assumptions due to Egbert: if decode c0 is not id, we can fix it
  module ForLoopSpace2 (A : Type) (a0 : A)
                       (Codes : A → Type) 
                       (c0 : Codes a0)
                       (decode' : {x : A} -> Codes x -> Path a0 x)
                       (encode-decode' : (c : Codes a0) -> transport Codes (decode'{a0} c) c0 ≃ c)
                       where

    encode : {x : A} → Path a0 x -> Codes x
    encode α = transport Codes α c0

    decode : {x : A} -> Codes x -> Path a0 x
    decode c = decode' c ∘ ! (decode' (encode id))

    decode-encode-id : decode c0 ≃ id
    decode-encode-id = !-inv-r (decode' c0)

    decode-encode : {x : A} -> (α : Path a0 x) → decode (encode α) ≃ α
    decode-encode id = decode-encode-id

    encode-decode : (c : Codes a0) -> encode {a0} (decode{a0} c) ≃ c
    encode-decode c = (encode-decode' c ∘ ap (transport Codes (decode' c)) fact2) ∘ ap≃ (transport-∘ Codes (decode' c) (! (decode' c0))) where
      fact1 : transport Codes (decode' c0) c0 == c0
      fact1 = encode-decode' c0
  
      fact2 : transport Codes (! (decode' c0)) c0 == c0
      fact2 = ! (coe (move-transport-right≃ Codes (decode' c0)) fact1)

    lemma : Equiv (Path a0 a0) (Codes a0) 
    lemma = improve (hequiv encode decode decode-encode encode-decode)


  -- simplified premises of encode-decode are contractibility of codes
  --   IF you do encode-decode for all a
  module EncodeDecodeVsContr (A : Type) (Codes : A → Type) where

     Prem : Type 
     Prem = Σ \ (a0 : A) -> 
            Σ \ (c0 : Codes a0) ->
            Σ \ (decode : (x : A) -> Codes x -> Path a0 x) ->
                (a : A) (c : Codes a) -> transport Codes (decode a c) c0 ≃ c

     to : Prem -> Contractible (Σ Codes)
     to (a0 , c0 , decode , encode-decode) = (a0 , c0) , (λ y → pair≃ (decode (fst y) (snd y)) (encode-decode (fst y) (snd y)))

     from : Contractible (Σ Codes) -> Prem
     from c = fst (fst c) , snd (fst c) , (λ x cx → ap fst (snd c (x , cx))) , (λ x cx → snd≃ (snd c (x , cx))) where

     comp : (p : Prem) -> from (to p) == p
     comp (a0 , c0 , decode , encode-decode) = ap (λ h → a0 , c0 , h) (pair= (λ≃ (λ x → λ≃ (λ cx → Σ≃β1 (decode x cx) (encode-decode x cx))))
                                                                             (coe (! PathOverΠ-NDdomain) (λ x → coe (! PathOverΠ-NDdomain) (λ cx → 
                                                                                  PathOver=.in-PathOver-= 
                                                                                  (sq x cx))))) where
          sq : (x : A) (cx : Codes x) -> _
          sq x cx = whisker-square id (! red1) (! (ap-constant cx (λ≃ (λ x₁ → λ≃ (λ cx₁ → Σ≃β1 (decode x₁ cx₁) (encode-decode x₁ cx₁)))))) id 
                    (disc-to-square (Σ≃β2 (decode x cx) (encode-decode x cx) ∘ ∘-unit-l (snd≃ (snd (to (a0 , c0 , decode , encode-decode)) (x , cx))))) where
            red1 :  ap (λ z → transport Codes (z x cx) c0) (λ≃ (λ x₁ → λ≃ (λ cx₁ → Σ≃β1 (decode x₁ cx₁) (encode-decode x₁ cx₁)))) == 
                    (ap (λ h → transport Codes h c0) (Σ≃β1 (decode x cx) (encode-decode x cx))) 
            red1 = ((ap (ap (λ h → transport Codes h c0)) (Π≃β (λ cx₁ → Σ≃β1 (decode x cx₁) (encode-decode x cx₁))) ∘
                     ap-o (λ h → transport Codes h c0) (λ f → f cx) (λ≃ (λ cx₁ → Σ≃β1 (decode x cx₁) (encode-decode x cx₁)))) ∘ 
                     ap (ap (λ z → transport Codes (z cx) c0)) (Π≃β (λ x₁ → λ≃ (λ cx₁ → Σ≃β1 (decode x₁ cx₁) (encode-decode x₁ cx₁))))) ∘ 
                     ap-o (λ z → transport Codes (z cx) c0) (λ f → f x) (λ≃ (λ x₁ → λ≃ (λ cx₁ → Σ≃β1 (decode x₁ cx₁) (encode-decode x₁ cx₁))))
     

     eqv : Equiv Prem (Contractible (Σ Codes))
     eqv = improve (hequiv to from comp (λ _ → HProp-unique (Contractible-is-HProp _) _ _))

     -- also preserves the point of interest
     prespoint1 : (a0 : A) → (Σ \ (p : Prem) -> fst p == a0) == (Σ \ (c : Contractible (Σ Codes)) → fst (fst c) == a0)
     prespoint1 a0 = apΣ' eqv (λ _ → id)

     prespoint : (a0 : A) → 
                 (Σ \ (c0 : Codes a0) ->
                  Σ \ (decode : (x : A) -> Codes x -> Path a0 x) ->
                    (a : A) (c : Codes a) -> transport Codes (decode a c) c0 == c)
                 == (Σ \ (c : Contractible (Σ Codes)) → fst (fst c) == a0)
     prespoint a0 = prespoint1 a0 ∘ ua (hfiber-fst-eqv a0)
