-- Peter Lumsdaine and Dan Licata

-- about 450 lines of new library code + this file

{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open Suspension
open Truncation
open Int
open ConnectedProduct

module homotopy.Freudenthal where


  -- index constraints:
  -- n is successor: needed first for the wedge-rec in Codes mer
  -- n is double-successor (n' is successor): needed first in Codes-mer-equiv (raise-HProp)
  module FreudenthalEquiv
    (n' : TLevel)
    (k : TLevel)
    (-2<n' : -2 <tl n')
    (k< : k <=tl (plus2 n' n'))
    (X : Type) (base : X) (nX : Connected (S n') X) where

    n : TLevel
    n = S n'

    P : Susp X -> Type 
    P x = Trunc k (Path {(Susp X)} No x)

    up : X → Path {Susp X} No No
    up x = ! (mer base) ∘ mer x

    decode' : Trunc k X → Trunc k (Path {(Susp X)} No No)
    decode' = Trunc-func up

    abstract
      Codes-mer : X → (Trunc k X) → (Trunc k X)
      Codes-mer = wedge-rec nX (connected-Trunc _ _ _ nX) Trunc-level k< {base} {[ base ]} (λ x' → x') (λ x → [ x ]) id
  
      Codes-mer-βa : (\ b -> Codes-mer base b) ≃ (\ x -> x)
      Codes-mer-βa = wedge-rec-βa nX (connected-Trunc _ _ _ nX) Trunc-level k< (λ x → x) (λ x → [ x ]) id
  
      Codes-mer-βb : (\ a -> Codes-mer a [ base ]) ≃ (\ x -> [ x ])
      Codes-mer-βb = wedge-rec-βb nX (connected-Trunc _ _ _ nX) Trunc-level k< (λ x → x) (λ x → [ x ]) id

      Codes-mer-coh : ap≃ Codes-mer-βb {base} ≃ ap≃ Codes-mer-βa {[ base ]} 
      Codes-mer-coh = ∘-unit-l (ap≃ Codes-mer-βa) ∘ wedge-rec-coh nX (connected-Trunc _ _ _ nX) Trunc-level k< (λ x → x) (λ x → [ x ]) id

      Codes-mer-isequiv : (x : X) -> IsEquiv (Codes-mer x)
      Codes-mer-isequiv = ConnectedFib.everywhere n' {a0 = base} 
                                                   nX
                                                   (λ x' → IsEquiv (Codes-mer x') ,
                                                    raise-level (-1<= -2<n') (IsEquiv-HProp (Codes-mer x'))) -- need n' is S - for this
                                                   (transport IsEquiv (! Codes-mer-βa) (snd id-equiv))
  
      Codes-mer-inv-base : IsEquiv.g (Codes-mer-isequiv base) ≃ (\ x -> x)
      Codes-mer-inv-base = transport-IsEquiv-g (! Codes-mer-βa) (snd id-equiv) ∘ ap IsEquiv.g
                             (ConnectedFib.β n' nX
                              (λ x' →
                                 IsEquiv (Codes-mer x') ,
                                 raise-level (-1<= -2<n') (IsEquiv-HProp (Codes-mer x')))
                              (transport IsEquiv (! Codes-mer-βa) (snd id-equiv)))

    Codes-mer-equiv : (x : X) -> Equiv (Trunc k X) (Trunc k X)
    Codes-mer-equiv x = (Codes-mer x) , Codes-mer-isequiv x 

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

    abstract
      encode-decode' : (c : Codes No) → encode (decode' c) ≃ c
      encode-decode' = Trunc-elim _ (λ _ → path-preserves-level Trunc-level)
                                    (λ x → encode (decode' [ x ]) ≃〈 id 〉 
                                           transport Codes (! (mer base) ∘ mer x) [ base ] ≃〈 ap≃ (transport-ap-assoc Codes (! (mer base) ∘ mer x)) 〉 
                                           coe (ap Codes (! (mer base) ∘ mer x)) [ base ] ≃〈 ap (λ x' → coe x' [ base ]) (ap-∘ Codes (! (mer base)) (mer x)) 〉 
                                           coe (ap Codes (! (mer base)) ∘ ap Codes (mer x)) [ base ] ≃〈 ap≃ (transport-∘ (λ x' → x') (ap Codes (! (mer base))) (ap Codes (mer x))) 〉 
                                           coe (ap Codes (! (mer base))) 
                                               (coe (ap Codes (mer x)) [ base ]) ≃〈 ap (\ x -> (coe (ap Codes (! (mer base))) (coe x [ base ]))) Susp-rec/βmer 〉 
                                           coe (ap Codes (! (mer base))) 
                                               (coe (ua (Codes-mer-equiv x)) [ base ]) ≃〈 ap (coe (ap Codes (! (mer base)))) (ap≃ (type≃β (Codes-mer-equiv x))) 〉 
                                           coe (ap Codes (! (mer base)))
                                               (Codes-mer x [ base ]) ≃〈 ap (λ x' → coe (ap Codes (! (mer base))) x') (ap≃ Codes-mer-βb) 〉 
                                           coe (ap Codes (! (mer base)))
                                               [ x ] ≃〈 ap (λ y → coe y [ x ]) (ap-! Codes (mer base)) 〉 
                                           coe (! (ap Codes (mer base)))
                                               [ x ] ≃〈 ap (λ y → coe (! y) [ x ]) Susp-rec/βmer 〉 
                                           coe (! (ua (Codes-mer-equiv base)))
                                               [ x ] ≃〈 ap≃ (type≃β! (Codes-mer-equiv base)) 〉 
                                           IsEquiv.g (snd (Codes-mer-equiv base))
                                               [ x ] ≃〈 ap≃ Codes-mer-inv-base {[ x ]} 〉 
                                           [ x ] ∎)

    decode : ∀ {x} -> Codes x → P x
    decode {x} = Susp-elim (\ x -> Codes x → P x)
                           decode'
                           (Trunc-func (λ x' → mer x')) 
                           (λ x' →
                                transport (λ x0 → Codes x0 → P x0) (mer x') decode' ≃〈 transport-→ Codes P (mer x') decode' 〉
                                transport P (mer x') o decode' o transport Codes (! (mer x')) ≃〈 move-posto-with-transport-left Codes (mer x') (transport P (mer x') o decode') (Trunc-func (λ x0 → mer x0)) (λ≃ (STS x'))〉
                                (Trunc-func (λ x0 → mer x0) ∎))
                           x where
     abstract
       STS : ∀ x' c -> transport P (mer x') (decode' c) ≃ 
                       Trunc-func mer (transport Codes (mer x') c)
       STS x' = Trunc-elim _ (λ _ → path-preserves-level Trunc-level)
         (λ x0 → wedge-elim nX nX 
                   (λ x1 x2 →
                      (transport P (mer x1) (decode' [ x2 ]) ≃
                        Trunc-func mer (transport Codes (mer x1) [ x2 ]))
                      , path-preserves-level (Trunc-level {k})) -- a little slack here, but would tightening it help?
                   k<
         {base}{base}
         (λ b' → transport P (mer base) (decode' [ b' ]) ≃〈 id 〉
                 transport P (mer base) [ (up b') ] ≃〈 ap≃ (transport-Trunc (Path No) (mer base)) 〉
                 [ transport (Path No) (mer base) (up b') ] ≃〈 ap [_] (transport-Path-right (mer base) (up b')) 〉
                 [ (mer base) ∘ ! (mer base) ∘ mer b' ] ≃〈 ap [_] (!-inv-r-front (mer base) (mer b')) 〉
                 [ mer b' ] ≃〈 id 〉
                 Trunc-func mer [ b' ] ≃〈 ap (Trunc-func mer) (! (ap≃ Codes-mer-βa)) 〉
                 (Trunc-func mer (Codes-mer base [ b' ])) ≃〈 ap (Trunc-func mer) (! (ap≃ (type≃β (Codes-mer-equiv base)))) 〉 
                 (Trunc-func mer (coe (ua (Codes-mer-equiv base)) [ b' ])) ≃〈 ap (Trunc-func mer) (ap (λ x1 → coe x1 [ b' ]) (! Susp-rec/βmer)) 〉  
                 (Trunc-func mer (coe (ap Codes (mer base)) [ b' ])) ≃〈 ap (Trunc-func mer) (! (ap≃ (transport-ap-assoc Codes (mer base)))) 〉 
                 (Trunc-func mer (transport Codes (mer base) [ b' ]) ∎))
         (λ a' → transport P (mer a') (decode' [ base ]) ≃〈 id 〉
                 transport P (mer a') [ up base ] ≃〈 ap≃ (transport-Trunc (Path No) (mer a')) 〉
                 [ transport (Path No) (mer a') (up base) ] ≃〈 ap [_] (transport-Path-right (mer a') (up base)) 〉
                 [ (mer a') ∘ ! (mer base) ∘ mer base ] ≃〈 ap [_] (!-inv-l-back (mer a') (mer base)) 〉 -- difference 1
                 [ (mer a') ] ≃〈 id 〉
                 Trunc-func mer [ a' ] ≃〈 ap (Trunc-func mer) (! (ap≃ Codes-mer-βb)) 〉 -- difference 2
                 (Trunc-func mer (Codes-mer a' [ base ])) ≃〈 ap (Trunc-func mer) (! (ap≃ (type≃β (Codes-mer-equiv a')))) 〉 
                 (Trunc-func mer (coe (ua (Codes-mer-equiv a')) [ base ])) ≃〈 ap (Trunc-func mer) (ap (λ x1 → coe x1 [ base ]) (! Susp-rec/βmer)) 〉  
                 (Trunc-func mer (coe (ap Codes (mer a')) [ base ])) ≃〈 ap (Trunc-func mer) (! (ap≃ (transport-ap-assoc Codes (mer a')))) 〉 
                 (Trunc-func mer (transport Codes (mer a') [ base ]) ∎))
         (ap2
            (λ x1 y →
               transport P (mer base) (decode' [ base ]) ≃〈 id 〉
               transport P (mer base) [ up base ] ≃〈 ap≃ (transport-Trunc (Path No) (mer base)) 〉
               [ transport (Path No) (mer base) (up base) ] ≃〈 ap [_] (transport-Path-right (mer base) (up base)) 〉
               [ mer base ∘ ! (mer base) ∘ mer base ] ≃〈 x1 〉
               [ mer base ] ≃〈 id 〉
               Trunc-func mer [ base ] ≃〈 y 〉
               Trunc-func mer (Codes-mer base [ base ]) ≃〈 ap (Trunc-func mer) (! (ap≃ (type≃β (Codes-mer-equiv base)))) 〉
               Trunc-func mer (coe (ua (Codes-mer-equiv base)) [ base ]) ≃〈 ap (Trunc-func mer) (ap (λ x2 → coe x2 [ base ]) (! Susp-rec/βmer))〉
               Trunc-func mer (coe (ap Codes (mer base)) [ base ]) ≃〈 ap (Trunc-func mer) (! (ap≃ (transport-ap-assoc Codes (mer base)))) 〉 (Trunc-func mer (transport Codes (mer base) [ base ]) ∎))
            (coh1 (mer base)) coh2) 
         x' x0) 
        where coh1 : ∀ {k A} {a a' : A} (p : a ≃ a') -> ap ([_]{k}) (!-inv-r-front p p) ≃ ap ([_]{k}) (!-inv-l-back p p)
              coh1 id = id
  
              coh2 : ap (Trunc-func mer) (! (ap≃ Codes-mer-βa {[ base ]})) ≃ ap (Trunc-func mer) (! (ap≃ Codes-mer-βb {base}))
              coh2 = ap (λ x0 → ap (Trunc-func mer) (! x0)) (! Codes-mer-coh)

    decode-encode : ∀ {x : Susp X} (α : P x) -> decode (encode α) ≃ α
    decode-encode tα = Trunc-elim (\ α -> decode (encode α) ≃ α) (λ x → path-preserves-level Trunc-level) 
                                  (path-induction (λ _ p → decode (encode [ p ]) ≃ [ p ]) (ap [_] (!-inv-l (mer base))))
                                  tα

    eqv : Equiv (Trunc k X) (Trunc k (Path {(Susp X)} No No))
    eqv = (improve (hequiv decode' encode encode-decode' decode-encode))

    path : Trunc k X ≃ Trunc k (Path {(Susp X)} No No)
    path = ua eqv -- ua (improve (hequiv decode' encode encode-decode' decode-encode))

  module StableSphere (n : Positive) (k : Positive) 
                      (c : (tlp k <=tl plus2 (-2ptl n) (-2ptl n)))
                      -- i.e. k <= 2n - 2 
         where

    open NSphereSusp

    nS^ : ∀ n → Connected (S (-2ptl n)) (S^ n)
    nS^ One = S^-Connected 0
    nS^ (S One) = S^-Connected 1
    nS^ (S (S n')) = transport (λ x → Connected (S (tl (pos2nat n'))) (Susp (S^ x))) 
                              (pos2nat-+1np n')
                              (S^-Connected (pos2nat (S n')))

    module F = FreudenthalEquiv (-2ptl n) (tlp k) (-2<pos-2 n) c (S^ n) (base^ n) (nS^ n) 

    stable : π k (S^ n) (base^ n) ≃ π (k +1) (S^ (n +1)) (base^ (n +1))
    stable = ! (π (S k) (S^ (S n)) (base^ (S n)) ≃〈 id 〉
                τ₀ (Loop (S k) (S^ (S n)) (base^ (S n))) ≃〈 ap τ₀ (LoopSpace.LoopPath.path k) 〉
                τ₀ (Loop k (Path {(S^ (S n))} (base^ (S n)) (base^ (S n))) id) ≃〈 ! (LoopSpace.Loop-Trunc0 k) 〉
                Loop k (Trunc (tlp k) (Path {(S^ (S n))} (base^ (S n)) (base^ (S n)))) [ id ] ≃〈 id 〉
                Loop k (Trunc (tlp k) (Path {Susp (S^ n)} No No)) [ id ] ≃〈 ap-Loop≃ k (! F.path) (ap≃ (type≃β! F.eqv)) 〉
                Loop k (Trunc (tlp k) (S^ n)) [ base^ n ] ≃〈 LoopSpace.Loop-Trunc0 k 〉 
                τ₀ (Loop k (S^ n) (base^ n)) ≃〈 id 〉 
                π k (S^ n) (base^ n) ∎)
    
    -- consequences of stablity for k <= 2n - 2 
    -- n = 1: k <= 0
    -- n = 2: k <= 2 : pi_1(S^2) = pi_2(S^3) and pi_2(S^2) = pi_3(S^3) 
    -- n = 3: k <= 4 : pi_1(S^3) = pi_2(S^4) and pi_2(S^3) = pi_3(S^4) and pi_3(S^3) = pi_4(s^4) and pi_4(S^3) = pi_5(S^4)
    -- n = 4: k <= 6 : pi_1(S^4) = pi_2(S^5) and pi_2(S^4) = pi_3(S^5) and pi_3(S^4) = pi_4(s^5) and pi_4(S^4) = pi_5(s^5) and pi_5(S^4) = pi_6(s^5) and pi_6(S^4) = pi_7(S^5)
    
    -- so: 
    -- k<n : pi_1(S^2) = pi_2(S^3) = pi_3(S^4) = pi_4(s^5) = ...
    --       pi_1(S^3) = pi_2(S^4) = pi_3(S^5) = ...
    --       pi_1(S^4) = pi_2(S^5) 
    -- k=n : pi_2(S^2) = pi_3(S^3) = pi_4(s^4) = pi_5(s^5) = ...
    -- k>n : pi_4(S^3) = pi_5(S^4) = pi_6(s^5) = ... 
    --       pi_6(S^4) = pi_7(S^5)

    -- to start the diagonals, can prove:
    -- pi_1(S^2)
    -- pi_1(S^3)
    -- pi_1(S^4)
    -- pi_2(S^2)
    -- pi_4(S^3)
    -- pi_6(S^4)
