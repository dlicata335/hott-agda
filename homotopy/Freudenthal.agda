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
    -- Appropriate: p <= m + n
    -- inclusion of wedge into product is m+n connected


  postulate
    AppropriateE : TLevel -> TLevel -> TLevel -> Type
  -- AppropriateE m n p iff p < m + n

  -- n + m + 2
  -- (not total otherwise, and the theorem works for -1/-2)
  plus2 : TLevel -> TLevel -> TLevel
  plus2 -2 n = n
  plus2 (S n) m = S (plus2 n m)

  Extensions : (A : Type) (a0 : A) (C : A -> Type) (c0 : C a0) -> Type
  Extensions A a0 C c0 = Σ (λ (f : (a : A) → (C a)) → f a0 ≃ c0)
  
  Extensions-Path : {A : Type} {a0 : A} (C : A -> Type) (c0 : C a0) 
                  (e1 e2 : Extensions A a0 C c0)
                  -> Path{(Extensions A a0 C c0)} e1 e2
                   ≃ Extensions A a0 (\ a -> Path{(C a)} (fst e1 a) (fst e2 a)) 
                                     (! (snd e2) ∘ snd e1)
  Extensions-Path {A}{a0}C c0 (f1 , α1) (f2 , α2) = 
    Path (f1 , α1) (f2 , α2)  ≃〈 ! ΣPath.path 〉 
    Σ (λ α → Path (transport (λ f → f a0 ≃ c0) α α1) α2) ≃〈 apΣ' (!equiv ΠPath.eqv) (λ _ → id) 〉 
    Σ (λ (h : (x : A) → Path (f1 x) (f2 x)) →
         Path (transport (λ f → f a0 ≃ c0) (λ≃ h) α1) α2) ≃〈 ap (λ B → Σ B) (λ≃ (λ h → ap (BackPath _) (ap (λ x → α1 ∘ ! x) (Π≃β h) ∘ transport-Path-pre' (λ f → f a0) (λ≃ h) α1))) 〉 
    Σ (λ (h : (x : A) → Path (f1 x) (f2 x)) →
         Path (α1 ∘ ! (h a0)) α2) ≃〈 ap (λ B → Σ B) (λ≃ (λ h → flip≃ ∘ flip-triangle≃ α1 α2 (h a0))) 〉 
    Σ (\ h -> h a0 ≃ ! α2 ∘ α1) ≃〈 id 〉 
    Extensions A a0 (λ a → Path (f1 a) (f2 a)) (! α2 ∘ α1) ∎
    
{-
  Extensions-level-nd : ∀ {m n} {A : Type} (cA : Connected m A)
                       (a0 : A) (C : NTypes (plus2 n m)) (c0 : fst C)
                   -> NType n (Extensions A a0 (\ _ -> C) c0)
  Extensions-level-nd {m}{ -2} cA a0 C c0 = ?
  Extensions-level-nd {m}{S n} cA a0 C c0 = ?
-}
{-
    ntype (λ e1 e2 → transport (NType n) 
           (! (Extensions-Path (fst o C) c0 e1 e2))
           (Extensions-level-nd {_} {n} cA a0 (\ a -> (Path (fst e1 a) (fst e2 a), use-level (snd (C a)) _ _)) 
                                           (! (snd e2) ∘ snd e1)))
-}

  Extensions-level : ∀ {m n} {A : Type} (cA : Connected (S m) A)
                       (a0 : A) (C : A -> NTypes (plus2 n m)) (c0 : fst (C a0))
                   -> NType n (Extensions A a0 (fst o C) c0)
  Extensions-level {m}{ -2} cA a0 C c0 = 
   ntype ((ConnectedFib.everywhere m cA C c0 , ConnectedFib.everywhereβ m cA C c0) ,
         (λ {(f , α) → pair≃ (λ≃ 
           (ConnectedFib.everywhere 
              m {_} {a0} cA 
              (λ a → Path (ConnectedFib.everywhere m cA C c0 a) (f a) , path-preserves-level (snd (C a)))
              (! α ∘ ConnectedFib.everywhereβ m cA C c0)))
           {! works!}}))
  Extensions-level {m}{S n} cA a0 C c0 =
    ntype (λ e1 e2 → transport (NType n) 
           (! (Extensions-Path (fst o C) c0 e1 e2))
           (Extensions-level {_} {n} cA a0 (\ a -> (Path (fst e1 a) (fst e2 a), use-level (snd (C a)) _ _)) 
                                           (! (snd e2) ∘ snd e1)))

  wedge-elim' : ∀ {m n} {A B : Type} 
                 (cA : Connected (S m) A) 
                 (cB : Connected (S n) B)
                 (C : A → B → NTypes (plus2 m n)) 
                 {a0 : A} {b0 : B}
              -> (fa0 : (b' : B) -> fst (C a0 b'))
              -> (fb0 : (a' : A) -> fst (C a' b0))
              -> fa0 b0 ≃ fb0 a0 
              -> (a' : A) -> (b' : B) -> fst (C a' b')
  wedge-elim'{m}{n}{A}{B} cA cB C {a0}{b0} fa0 fb0 agree a = 
    fst
      (ConnectedFib.everywhere m {_} {a0} cA
       (λ a' → Extensions _ _ (fst o (C a')) (fb0 a') , 
               Extensions-level {n} {m} cB b0 (C a') (fb0 a')) 
          (fa0 , agree)
       a)

  wedge-elim : ∀ {m n p} {A B : Type} 
                 (cA : Connected (S m) A) 
                 (cB : Connected (S n) B)
                 (C : A → B → NTypes p) 
                 (app : p <=tl plus2 m n)
                 {a0 : A} {b0 : B}
              -> (fa0 : (b' : B) -> fst (C a0 b'))
              -> (fb0 : (a' : A) -> fst (C a' b0))
              -> fa0 b0 ≃ fb0 a0 
              -> (a' : A) -> (b' : B) -> fst (C a' b')
  wedge-elim{m}{n}{p}{A}{B} cA cB C ap  = 
    wedge-elim' cA cB (λ a b → fst (C a b) , raise-level ap (snd (C a b))) 


{-
  wedge-elim-βa : ∀{m}{n}{p} {A B : Type}
                 (cA : Connected m A) (cB : Connected n B) (C : A → B → NTypes p) {a : A} {b : B}
              -> (fa : (b' : B) -> fst (C a b'))
              -> (fb : (a' : A) -> fst (C a' b))
              -> (agree : fa b ≃ fb a)
              -> (wedge-elim cA cB C app fa fb agree a ≃ fa)

  wedge-elim-βb : ∀{m}{n}{p} {A B : Type}
                 (cA : Connected m A) (cB : Connected n B) (C : A → B → NTypes p) {a : A} {b : B}
              -> (fa : (b' : B) -> fst (C a b'))
              -> (fb : (a' : A) -> fst (C a' b))
              -> (agree : fa b ≃ fb a)
              -> (\ a' -> wedge-elim cA cB C app fa fb agree a' b) ≃ fb
-}

  wedge-rec : ∀ {m n p} {A B C : Type} 
            -> Connected (S m) A 
            -> Connected (S n) B
            -> NType p C 
            -> p <=tl (plus2 m n)
            -> {a : A} {b : B}
            -> (fa : B -> C)
            -> (fb : A -> C)
            -> fa b ≃ fb a 
            -> A -> B -> C
  wedge-rec cA cB nC = wedge-elim cA cB (\ _ _ -> _ , nC) 

  postulate
    wedge-rec-βa : ∀ {m}{n}{p} {A B C : Type} 
              -> (cA : Connected (S m) A)
              -> (cB : Connected (S n) B)
              -> (nC : NType p C)
              -> (ap : p <=tl (plus2 m n))
                 {a : A} {b : B}
              -> (fa : B -> C)
              -> (fb : A -> C)
              -> (agree : fa b ≃ fb a)
              -> (wedge-rec cA cB nC ap fa fb agree a ≃ fa)
  
    wedge-rec-βb : ∀ {m}{n}{p} {A B C : Type}
              -> (cA : Connected (S m) A)
              -> (cB : Connected (S n) B)
              -> (nC : NType p C)
              -> (ap : p <=tl (plus2 m n))
                 {a : A} {b : B}
              -> (fa : B -> C)
              -> (fb : A -> C)
              -> (agree : fa b ≃ fb a)
              -> (\ a' -> wedge-rec cA cB nC ap fa fb agree a' b) ≃ fb


  -- case where n or k is -2: theorem is easy
  module Freudenthal (n' : TLevel)(k : TLevel) (k< : k <=tl (plus2 n' n'))  (X : Type) (base : X) (nX : Connected (S n') X) where

    n : TLevel
    n = S n'

    P : Susp X -> Type 
    P x = Trunc k (Path {(Susp X)} No x)

    up : X → Path {Susp X} No No
    up x = ! (mer base) ∘ mer x

    decode' : Trunc k X → Trunc k (Path {(Susp X)} No No)
    decode' = Trunc-func up

    Codes-mer : X → (Trunc k X) → (Trunc k X)
    Codes-mer = wedge-rec nX (connected-Trunc _ _ _ nX) Trunc-level k< {base} {[ base ]} (λ x' → x') (λ x → [ x ]) id

    Codes-mer-βa : (\ b -> Codes-mer base b) ≃ (\ x -> x)
    Codes-mer-βa = wedge-rec-βa nX (connected-Trunc _ _ _ nX) Trunc-level app-nnk (λ x → x) (λ x → [ x ]) id

    Codes-mer-βb : (\ a -> Codes-mer a [ base ]) ≃ (\ x -> [ x ])
    Codes-mer-βb = wedge-rec-βb nX (connected-Trunc _ _ _ nX) Trunc-level app-nnk (λ x → x) (λ x → [ x ]) id

{-
    Codes-mer-equiv : (x : X) -> Equiv (Trunc k X) (Trunc k X)
    Codes-mer-equiv x = improve (hequiv (Codes-mer x) (Codes-mer x) {!!} collapse) where
      collapse : (x' : Trunc k X) → Path (Codes-mer x (Codes-mer x x')) x'
      collapse x' = wedge-elim nX (connected-Trunc _ _ _ nX) 
                               (λ x0 x1 → Codes-mer x0 (Codes-mer x0 x1) ≃ x1 , use-level (Trunc-level {k}) _ _)
                               appe-nnk' {base} {[ base ]}
                               (λ tx → {! ap (λ f → f (f tx)) Codes-mer-βa !})
                               (λ x0 → {!!})
                               {!!}
                               x x' where
               diag : (x0 : X) → Codes-mer x0 [ x0 ] ≃ [ base ]
               diag = ConnectedFib.everywhere n' {a = base} nX (λ x0 → Codes-mer x0 [ x0 ] ≃ [ base ] , {!!}) (ap≃ Codes-mer-βb)

      collapse : (x' : Trunc k X) → Path (Codes-mer x (Codes-mer x x')) x'
      collapse x' = wedge-elim nX (connected-Trunc _ _ _ nX) 
                               (λ x0 x1 → Codes-mer x0 (Codes-mer x0 x1) ≃ x1 , use-level (Trunc-level {k}) _ _)
                               appe-nnk' {base} {[ base ]}
                               (λ tx → ap (λ f → f (f tx)) Codes-mer-βa)
                               (λ x0 → {!!} ∘ ap (Codes-mer x0) (ap≃ Codes-mer-βb))
                               {!!}
                               x x' where
               diag : (x0 : X) → Codes-mer x0 [ x0 ] ≃ [ base ]
               diag = ConnectedFib.everywhere n' {a = base} nX (λ x0 → Codes-mer x0 [ x0 ] ≃ [ base ] , {!!}) (ap≃ Codes-mer-βb)
-}
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
                                                         [ mer b' ] ≃〈 id 〉
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
