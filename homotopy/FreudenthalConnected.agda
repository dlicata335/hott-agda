-- Peter Lumsdaine and Dan Licata

-- about 450 lines of new library code + this file

{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open Suspension
open Truncation
open Int
open ConnectedProduct

module homotopy.FreudenthalConnected where

    {-
    -- FIXME: move
    transport-Path-right-∘ : ∀ {A} {a b c : A} (β : b ≃ c) (α : a ≃ b)
                           → transport-Path-right (β ∘ α) id ≃ 
                             ap (λ x → β ∘ x) (transport-Path-right α id) ∘
                             (transport-Path-right β (transport (Path a) α id) ∘
                              ap≃ (transport-∘ (Path a) β α))
    transport-Path-right-∘ id id = id

    ∘-Σ : ∀ {A} {B : A → Type} {p q r : Σ B}
        → (α1 : fst p ≃ fst q) (α2 : fst q ≃ fst r)
        → (β1 : transport B α1 (snd p) ≃ (snd q)) (β2 : transport B α2 (snd q) ≃ (snd r))
        → (pair≃{B = B} α2 β2) ∘ (pair≃ α1 β1) ≃ pair≃ (α2 ∘ α1) (β2 ∘ ap (transport B α2) β1 ∘ ap≃ (transport-∘ B α2 α1))
    ∘-Σ {p = (p1 , p2)} {q = (.p1 , .p2)} {r = (.p1 , .p2)} id id id id = id
    -}


  module Freudenthal
    (n' : TLevel)
    (-2<n' : -2 <tl n')
    (X : Type) (x0 : X) (nX : Connected (S n') X) where

    n : TLevel
    n = S n'

    2n = plus2 n' n'

    loop : X → Path {Susp X} No No
    loop x = ! (mer x0) ∘ mer x

    Codes-mer' : (x1 x2 : X) -> Trunc 2n (HFiber mer ((mer x1) ∘ (! (mer x0)) ∘ (mer x2)))
    Codes-mer' = wedge-elim nX nX (λ x1 x2 → Trunc 2n (HFiber mer ((mer x1) ∘ (! (mer x0)) ∘ (mer x2))) , Trunc-level)
                               (Inr id) {x0}{x0}
                               (λ x2 → [ x2 , ! (!-inv-r-front (mer x0) (mer x2)) ])
                               (λ x1 → [ x1 , ! (!-inv-l-back (mer x1) (mer x0)) ])
                               (ap [_] (pair≃ id (ap ! (coh (mer x0))))) where
                  coh : ∀ {A} {a b : A} (α : a ≃ b) -> !-inv-r-front α α ≃ !-inv-l-back α α
                  coh id = id

    Codes-mer'' : (x1 : X) {p : Path No So}
               → (x2 : X) (q : Id (mer x1 ∘ ! (mer x0) ∘ mer x2) p)
               → Trunc 2n (HFiber mer p)
    Codes-mer'' x1 x2 q = transport (Trunc 2n o HFiber mer) q (Codes-mer' x1 x2)
    
    Codes-mer : (x1 : X) (p : Path No So)
               → Trunc 2n (HFiber loop (! (mer x1) ∘ p)) -> Trunc 2n (HFiber mer p)
    Codes-mer x1 p = Trunc-rec Trunc-level (λ {(x2 , q) → Codes-mer'' x1 x2 (move-left-! (loop x2) (mer x1) p q)})  

    Codes-mer-is-equiv : (x1 : X) (p : Path No So)
                        → IsEquiv (Codes-mer x1 p)
    Codes-mer-is-equiv = ConnectedFib.everywhere -1 {a0 = x0}
                                                    (lower-Connected (<=SCong (-1<= -2<n')) nX)
                                                    (λ x1 → ((p : Path No So) → IsEquiv (Codes-mer x1 p)) , Πlevel (λ _ → IsEquiv-HProp _))
                                                    {!!} 

    -- CodesFor x α is the Codes for paths to x which decode to α
    CodesFor : (x : Susp X) -> Path No x → Type
    CodesFor = Susp-elim _
                         (\ α → Trunc 2n (HFiber loop α))
                         (λ α → Trunc 2n (HFiber mer α))
                         (λ x1 → λ≃ (λ p → ua (Codes-mer x1 p , Codes-mer-is-equiv x1 p) ∘ 
                                           ap (λ p' → Trunc 2n (HFiber loop p')) (transport-Path-right (! (mer x1)) p) ∘
                                           ap≃ (transport-→-pre' (Path No) (mer x1) (λ α → Trunc 2n (HFiber loop α))))) 

    CodesForC : (Σ \ (x : Susp X) -> Path No x) → Type
    CodesForC p = CodesFor (fst p) (snd p)

    encode : {x : Susp X} → (α : Path No x) → CodesFor x α
    encode {x} α = -- this is really J written out with transport
                   coe
                   (ap CodesForC 
                       (pair≃ {B = Path No} α (transport-Path-right α id)))
                   [ x0 , !-inv-l (mer x0) ] -- includes bit from decode-encode

    -- if α = decode c then encode α = c
    encode-decode : {x : Susp X} → (α : Path No x) → (c : CodesFor x α) -> (encode α) ≃ c
    encode-decode id = Trunc-elim _ (λ _ → path-preserves-level Trunc-level) 
                                    (encode-decode' id) where
      -- WEIRD: by path induction, suffices to consider x = No, α = id
      -- but then need to re-generalize to arbitrary loop α?
      encode-decode' : (α : Path No No) → (c : HFiber loop α) → Id (encode α) [ c ]
      encode-decode' ._ (x , id) = STS where
        STS : (encode (! (mer x0) ∘ mer x)) ≃ [ x , id ]
        STS = (encode (! (mer x0) ∘ mer x)) ≃〈 id 〉 
              (coe (ap CodesForC (pair≃ (! (mer x0) ∘ mer x) (transport-Path-right (! (mer x0) ∘ mer x) id)))
                   [ x0 , !-inv-l (mer x0) ]) ≃〈 ap (λ x' → coe (ap CodesForC x') [ x0 , !-inv-l (mer x0) ]) 
                                                       (un∘ (! (mer x0)) (mer x)) 〉 
              (coe (ap CodesForC ((pair≃   (! (mer x0)) (transport-Path-right (! (mer x0)) (mer x))) 
                                  ∘ (pair≃ (mer x) (transport-Path-right (mer x) id))))
                   [ x0 , !-inv-l (mer x0) ]) ≃〈 {!!} 〉 
              (coe (ap CodesForC ((pair≃   (! (mer x0)) (transport-Path-right (! (mer x0)) (mer x))))
                    ∘ (ap CodesForC (pair≃ (mer x) (transport-Path-right (mer x) id))))
                                     [ x0 , !-inv-l (mer x0) ]) ≃〈 {!!} 〉 
              (coe (ap CodesForC ((pair≃   (! (mer x0)) (transport-Path-right (! (mer x0)) (mer x)))))
                   (coe (ap CodesForC (pair≃ (mer x) (transport-Path-right (mer x) id)))
                        [ x0 , !-inv-l (mer x0) ])) ≃〈 {!!} 〉 
              [ x , id ] ∎ where
         un∘ : ∀ {x y z} (α2 : Path{Susp X} y z) (α1 : Path{Susp X} x y)
               ->  (pair≃ {B = Path x} (α2 ∘ α1) (transport-Path-right (α2 ∘ α1) id))
                 ≃   pair≃ α2 (transport-Path-right α2 α1) 
                   ∘ pair≃ α1 (transport-Path-right α1 id)
         un∘ id id = id

    thm : ConnectedMap.ConnectedMap 2n {X}{(Path {(Susp X)} No No)} loop
    thm α = ntype (encode α , encode-decode α)

{-
    decode' : Trunc k X → Trunc k (Path {(Susp X)} No No)
    decode' = Trunc-func up

    abstract
      Codes-mer : X → (Trunc k X) → (Trunc k X)
      Codes-mer = wedge-rec nX (connected-Trunc _ _ _ nX) Trunc-level k< {x0} {[ base ]} (λ x' → x') (λ x → [ x ]) id
  
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
                                               (coe (ap Codes (mer x)) [ base ]) ≃〈 ap (\ x -> (coe (ap Codes (! (mer base))) (coe x [ base ]))) (Susp-rec/βmer {mer' = λ x₁ → ua (Codes-mer-equiv x₁)}) 〉 
                                           coe (ap Codes (! (mer base))) 
                                               (coe (ua (Codes-mer-equiv x)) [ base ]) ≃〈 ap (coe (ap Codes (! (mer base)))) (ap≃ (type≃β (Codes-mer-equiv x))) 〉 
                                           coe (ap Codes (! (mer base)))
                                               (Codes-mer x [ base ]) ≃〈 ap (λ x' → coe (ap Codes (! (mer base))) x') (ap≃ Codes-mer-βb) 〉 
                                           coe (ap Codes (! (mer base)))
                                               [ x ] ≃〈 ap (λ y → coe y [ x ]) (ap-! Codes (mer base)) 〉 
                                           coe (! (ap Codes (mer base)))
                                               [ x ] ≃〈 ap (λ y → coe (! y) [ x ]) (Susp-rec/βmer {mer' = (λ x → ua (Codes-mer-equiv x))} ) 〉 
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
                 (Trunc-func mer (coe (ua (Codes-mer-equiv base)) [ b' ])) ≃〈 ap (Trunc-func mer) (ap (λ x1 → coe x1 [ b' ]) (! (Susp-rec/βmer {mer' = (λ x → ua (Codes-mer-equiv x))}))) 〉  
                 (Trunc-func mer (coe (ap Codes (mer base)) [ b' ])) ≃〈 ap (Trunc-func mer) (! (ap≃ (transport-ap-assoc Codes (mer base)))) 〉 
                 (Trunc-func mer (transport Codes (mer base) [ b' ]) ∎))
         (λ a' → transport P (mer a') (decode' [ base ]) ≃〈 id 〉
                 transport P (mer a') [ up base ] ≃〈 ap≃ (transport-Trunc (Path No) (mer a')) 〉
                 [ transport (Path No) (mer a') (up base) ] ≃〈 ap [_] (transport-Path-right (mer a') (up base)) 〉
                 [ (mer a') ∘ ! (mer base) ∘ mer base ] ≃〈 ap [_] (!-inv-l-back (mer a') (mer base)) 〉 -- difference 1
                 [ (mer a') ] ≃〈 id 〉
                 Trunc-func mer [ a' ] ≃〈 ap (Trunc-func mer) (! (ap≃ Codes-mer-βb)) 〉 -- difference 2
                 (Trunc-func mer (Codes-mer a' [ base ])) ≃〈 ap (Trunc-func mer) (! (ap≃ (type≃β (Codes-mer-equiv a')))) 〉 
                 (Trunc-func mer (coe (ua (Codes-mer-equiv a')) [ base ])) ≃〈 ap (Trunc-func mer) (ap (λ x1 → coe x1 [ base ]) (! (Susp-rec/βmer {mer' = (λ x → ua (Codes-mer-equiv x))}))) 〉  
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
               Trunc-func mer (coe (ua (Codes-mer-equiv base)) [ base ]) ≃〈 ap (Trunc-func mer) (ap (λ x2 → coe x2 [ base ]) (! (Susp-rec/βmer {mer' = (λ x → ua (Codes-mer-equiv x))})))〉
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
-}
  

