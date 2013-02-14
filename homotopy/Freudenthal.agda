-- Peter Lumsdaine and Dan Licata

{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open Suspension
open Truncation

module homotopy.Freudenthal where

  postulate
    connected-Trunc : ∀ n k A -> Connected n A -> Connected n (Trunc k A)


  -- FIXME: move to NConnected once we discover what it is
  postulate
    AppropriateR : TLevel -> TLevel -> TLevel -> Type

    wedge-rec : ∀ {m} {n} {p} {A B C : Type} 
              -> Connected m A 
              -> Connected n B
              -> NType p C 
              -> AppropriateR m n p
              -> {a : A} {b : B}
              -> (fa : B -> C)
              -> (fb : A -> C)
              -> fa b ≃ fb a 
              -> A -> B -> C

    wedge-rec-βa : ∀ {m}{n}{p} {A B C : Type} 
              -> (cA : Connected m A)
              -> (cB : Connected n B)
              -> (nC : NType p C)
              -> (ap : AppropriateR m n p)
                 {a : A} {b : B}
              -> (fa : B -> C)
              -> (fb : A -> C)
              -> (agree : fa b ≃ fb a)
              -> (wedge-rec cA cB nC ap fa fb agree a ≃ fa)

    wedge-rec-βb : ∀ {m}{n}{p} {A B C : Type}
              -> (cA : Connected m A)
              -> (cB : Connected n B)
              -> (nC : NType p C)
              -> (ap : AppropriateR m n p)
                 {a : A} {b : B}
              -> (fa : B -> C)
              -> (fb : A -> C)
              -> (agree : fa b ≃ fb a)
              -> (\ a' -> wedge-rec cA cB nC ap fa fb agree a' b) ≃ fb

  postulate
    AppropriateE : TLevel -> TLevel -> TLevel -> Type

    wedge-elim : ∀ {m n p} {A B : Type} 
                 (cA : Connected m A) (cB : Connected n B) (C : A → B → NTypes p) 
              -> (app : AppropriateE m n p)
                 {a : A} {b : B}
              -> (fa : (b' : B) -> fst (C a b'))
              -> (fb : (a' : A) -> fst (C a' b))
              -> fa b ≃ fb a 
              -> (a' : A) -> (b' : B) -> fst (C a' b')

{-
    wedge-elim-βa : ∀{m}{n}{p} {A B : Type}
                 (cA : Connected m A) (cB : Connected n B) (C : A → B → NTypes p) {a : A} {b : B}
              -> (app : AppropriateE m n p)
              -> (fa : (b' : B) -> fst (C a b'))
              -> (fb : (a' : A) -> fst (C a' b))
              -> (agree : fa b ≃ fb a)
              -> (wedge-elim cA cB C app fa fb agree a ≃ fa)

    wedge-elim-βb : ∀{m}{n}{p} {A B : Type}
                 (cA : Connected m A) (cB : Connected n B) (C : A → B → NTypes p) {a : A} {b : B}
              -> (app : AppropriateE m n p)
              -> (fa : (b' : B) -> fst (C a b'))
              -> (fb : (a' : A) -> fst (C a' b))
              -> (agree : fa b ≃ fb a)
              -> (\ a' -> wedge-elim cA cB C app fa fb agree a' b) ≃ fb
-}

  module Freudenthal (n : TLevel)(k' : TLevel) (X : Type) (base : X) (nX : Connected n X) where

    k : TLevel
    k = S k'

    postulate
      app-nnk : AppropriateR n n k 
      appe-nnk' : AppropriateE n n k'

    P : Susp X -> Type 
    P x = Trunc k (Path {(Susp X)} No x)

    up : X → Path {Susp X} No No
    up x = ! (mer base) ∘ mer x

    decode' : Trunc k X → Trunc k (Path {(Susp X)} No No)
    decode' = Trunc-func up

    Codes-mer : X → (Trunc k X) → (Trunc k X)
    Codes-mer = wedge-rec nX (connected-Trunc _ _ _ nX) Trunc-level app-nnk {base}{[ base ]}(λ x' → x') (\ x -> [ x ]) id

    Codes-mer-βa : (\ b -> Codes-mer base b) ≃ (\ x -> x)
    Codes-mer-βa = wedge-rec-βa nX (connected-Trunc _ _ _ nX) Trunc-level app-nnk (λ x → x) (λ x → [ x ]) id

    Codes-mer-βb : (\ a -> Codes-mer a [ base ]) ≃ (\ x -> [ x ])
    Codes-mer-βb = wedge-rec-βb nX (connected-Trunc _ _ _ nX) Trunc-level app-nnk (λ x → x) (λ x → [ x ]) id

    Codes-mer-equiv : (x : X) -> Equiv (Trunc k X) (Trunc k X)
    Codes-mer-equiv x = improve (hequiv (Codes-mer x) (Codes-mer x) collapse collapse) where
      collapse : (x' : Trunc k X) → Path (Codes-mer x (Codes-mer x x')) x'
      collapse x' = wedge-elim nX (connected-Trunc _ _ _ nX) (λ x0 x1 → Codes-mer x0 (Codes-mer x0 x1) ≃ x1 , use-level (Trunc-level {k}) _ _)
                               appe-nnk' {base} {[ base ]} {!!} {!!} {!!} x x'

    Codes : Susp X -> Type 
    Codes = Susp-rec (Trunc k X) 
                     (Trunc k X)
                     (λ x → ua (Codes-mer-equiv x))

    NType-Codes : (x : Susp X) -> NType k (Codes x)
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
                                         Codes-mer base [ x ] ≃〈 ap≃ Codes-mer-βa 〉 
                                         [ x ] ∎)

    decode : ∀ {x} -> Codes x → P x
    decode {x} = Susp-elim (\ x -> Codes x → P x)
                           decode'
                           (Trunc-func (λ x' → mer x')) 
                           (λ x' →
                                transport (λ x0 → Codes x0 → P x0) (mer x') decode' ≃〈 {!!} 〉
                                transport P (mer x') o decode' o transport Codes (! (mer x')) ≃〈 {!!} 〉 
                                transport P (mer x') o decode' o transport Codes (! (mer x')) ≃〈 {!!}〉
                                (Trunc-func (λ x0 → mer x0) ∎))
                           x
           where STS : ∀ x' c -> transport P (mer x') (decode' c)       ≃ 
                                 Trunc-func mer (transport Codes (mer x') c)
                 STS x' = Trunc-elim _ (λ _ → path-preserves-level Trunc-level)
                                       (λ x0 → wedge-elim {n}{n}{k'} nX nX 
                                                 (λ x1 x2 →
                                                    (transport P (mer x1) (decode' [ x2 ]) ≃
                                                      Trunc-func mer (transport Codes (mer x1) [ x2 ]))
                                                    , use-level (Trunc-level {k}) _ _)
                                                 appe-nnk'
                                                 {base}{base}
                                                 (λ b' → transport P (mer base) (decode' [ b' ]) ≃〈 id 〉
                                                         transport P (mer base) [ (up b') ] ≃〈 {!!} 〉
                                                         [ (mer base) ∘ ! (mer base) ∘ mer b' ] ≃〈 {!!} 〉
                                                         [ mer b' ] ≃〈 {!id!} 〉
                                                         Trunc-func mer [ b' ] ≃〈 {!!} 〉
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

    decode-encode : ∀ {x : Susp X} (α : P x) -> decode (encode α) ≃ α
    decode-encode tα = Trunc-elim (\ α -> decode (encode α) ≃ α) (λ x → path-preserves-level Trunc-level) 
                                  (path-induction (λ _ p → decode (encode [ p ]) ≃ [ p ]) (ap [_] (!-inv-l (mer base))))
                                  tα

    theorem : Trunc k X ≃ Trunc k (Path {(Susp X)} No No)
    theorem = ua (improve (hequiv decode' encode encode-decode' decode-encode))
