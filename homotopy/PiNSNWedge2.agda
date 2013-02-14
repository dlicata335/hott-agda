{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open Suspension
open Truncation
open NSphereSusp
open Int

module homotopy.PiNSNWedge2 where

  -- S^n+1 is n-connected

  S-connected : (n : _) -> Connected (tlp n) (S^ (S n))
  S-connected One = {!!} -- τ1 (S^2) is contractible
  S-connected (S n) = {! !}

  connected-Trunc : ∀ n k A -> Connected n A -> Connected n (Trunc k A)
  connected-Trunc n k A cA = {!!}

  wedge-rec-βb' : ∀ n {A B C : Type} {a : A} {b : B}
                 (cA : Connected (S n) A)
                 (cB : Connected (S n) B)
                 (nC : NType (S (S n)) C)
            -> (fa : B -> C)
            -> (fb : A -> C)
            -> (agree : fa b ≃ fb a)
            -> (\ a -> LeftBiased.wedge-rec fa fb agree a b) ≃ fb
  wedge-rec-βb' n {C = C}{a}{b} cA cB nC fa fb agree = {!!}

  wedge-elim' : ∀ n {A B : Type} (cA : Connected (S n) A) (cB : Connected (S n) B) (C : A → B → NTypes (S n)) {a : A} {b : B}
              -> (fa : (b' : B) -> fst (C a b'))
              -> (fb : (a' : A) -> fst (C a' b))
              -> fa b ≃ fb a 
              -> (a' : A) -> (b' : B) -> fst (C a' b')
  wedge-elim' n cA cB C fa fb agree = {!!}

  module BabyFreudenthal (n : TLevel) (X : Type) (base : X) (nX : Connected (S n) X) where

    up : X → Path {Susp X} No No
    up x = ! (mer base) ∘ mer x

    decode' : Trunc (S (S n)) X → Trunc (S (S n)) (Path {(Susp X)} No No)
    decode' = Trunc-func up

    P : Susp X -> Type 
    P x = Trunc (S (S n)) (Path {(Susp X)} No x)

    Codes-mer : X → (Trunc (S (S n)) X) → (Trunc (S (S n)) X)
    Codes-mer = LeftBiased.wedge-rec {_}{_}{_}{base}{[ base ]}(λ x' → x') (\ x -> [ x ]) id -- could be the other way around

    Codes-mer-βb : (\ a -> Codes-mer a [ base ]) ≃ (\ x -> [ x ])
    Codes-mer-βb = wedge-rec-βb' n {a = base} {b = [_] {n} base} nX (connected-Trunc _ _ _ nX) Trunc-level (λ _ → [ base ]) (λ x → [ x ]) id
    -- need to borrow the S from B: you know that Trunc (S (S n)) X is (S n) connected

    Codes-mer-equiv : (x : X) -> Equiv (Trunc (S (S n)) X) (Trunc (S (S n)) X)
    Codes-mer-equiv x = equiv (Codes-mer x) (Codes-mer x) (λ x' → id) (λ _ → id) (λ _ → id)

    Codes : Susp X -> Type 
    Codes = Susp-rec (Trunc (S (S n)) X) 
                     (Trunc (S (S n)) X)
                     (λ x → ua (Codes-mer-equiv x))

    NType-Codes : (x : Susp X) -> NType (S (S n)) (Codes x)
    NType-Codes = Susp-elim _ Trunc-level Trunc-level (λ _ → HProp-unique (NType-is-HProp _) _ _)

    encode0 : ∀ {x : Susp X} → Path No x → Codes x
    encode0 α = transport Codes α [ base ]

    encode : ∀ {x : Susp X} → P x → Codes x
    encode{x} tα = Trunc-rec (NType-Codes x) encode0 tα

    encode-decode' : (c : Codes No) → encode (decode' c) ≃ c
    encode-decode' = Trunc-elim _ (λ _ → path-preserves-level Trunc-level)
                                  (λ x → encode (decode' [ x ]) ≃〈 id 〉 
                                         transport Codes (! (mer base) ∘ mer x) [ base ] ≃〈 {!!} 〉 
                                         coe (ap Codes (! (mer base))) 
                                             (coe (ap Codes (mer x)) [ base ]) ≃〈 {!!} 〉 
                                         coe (! (ap Codes (mer base)))
                                             (Codes-mer x [ base ]) ≃〈 ap (λ x' → coe (! (ap Codes (mer base))) x') (ap≃ Codes-mer-βb) 〉 
                                         coe (! (ap Codes (mer base)))
                                             [ x ] ≃〈 {!!} 〉 
                                         Codes-mer base [ x ] ≃〈 id 〉 
                                         [ x ] ∎)

    decode : ∀ {x} -> Codes x → P x
    decode {x} = Susp-elim (\ x -> Codes x → P x)
                           decode'
                           (Trunc-func (λ x' → mer x')) 
                           (λ x' → transport (λ x0 → Codes x0 → P x0) (mer x') decode' ≃〈 {!!} 〉
                                   transport P (mer x') o decode' o transport Codes (! (mer x'))  ≃〈 {!!} 〉
                                   transport P (mer x') o decode' o transport Codes (! (mer x'))  ≃〈 {!!} 〉
                                   (Trunc-func (λ x0 → mer x0) ∎))
                           x
           where STS : ∀ x' c -> transport P (mer x') (decode' c)       ≃ 
                                 Trunc-func mer (transport Codes (mer x') c)
                 STS x' = Trunc-elim _ (λ _ → path-preserves-level Trunc-level)
                                       (λ x0 → wedge-elim' n nX nX 
                                                 (λ x1 x2 →
                                                    (transport P (mer x1) (decode' [ x2 ]) ≃
                                                      Trunc-func mer (transport Codes (mer x1) [ x2 ]))
                                                    , use-level (Trunc-level{S(S n)}) (transport P (mer x1) (decode' [ x2 ]) ) (Trunc-func mer (transport Codes (mer x1) [ x2 ])))
                                                 {base}{base}
                                                 (λ b' → transport P (mer base) (decode' [ b' ]) ≃〈 id 〉
                                                         transport P (mer base) [ (up b') ] ≃〈 {!!} 〉
                                                         [ (mer base) ∘ ! (mer base) ∘ mer b' ] ≃〈 {!!} 〉
                                                         [ mer b' ] ≃〈 id 〉
                                                         (Trunc-func mer (Codes-mer base [ b' ])) ≃〈 {!!} 〉 
                                                         (Trunc-func mer (transport Codes (mer base) [ b' ]) ∎))
                                                 (λ a' → transport P (mer a') (decode' [ base ]) ≃〈 {!!} 〉
                                                         transport P (mer a') [ up base ] ≃〈 {!!} 〉
                                                         [ (mer a') ∘ ! (mer base) ∘ mer base ] ≃〈 {!!} 〉
                                                         [ (mer a') ] ≃〈 id 〉
                                                         Trunc-func mer [ a' ] ≃〈 ap (Trunc-func mer) (! (ap≃ Codes-mer-βb)) 〉 
                                                         Trunc-func mer (Codes-mer a' [ base ]) ≃〈 {!!} 〉 
                                                         Trunc-func mer (transport Codes (mer a') [ base ]) ∎)
                                                 {!!} -- not sure about this one
                                                 x' x0) 


    -- S^n+2 is (S n)-connected; X is (S n) connected; therefore we want the theorem
    -- statement where X is like S^n+2; which is tau(n+2)(S^ n+2) = tau(n+2)(Omega(S^ n+3))
    theorem : Trunc (S (S n)) X ≃ Trunc (S (S n)) (Path {(Susp X)} No No)
    theorem = {!!}

    -- τ n (S^ n) = τ n (Path{S^ (n + 1)} No No)
    -- τ n (S^ n) = τ n (Path{Susp (S^ n)} No No)