-- Peter Lumsdaine, Eric Finster, and Dan Licata

{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open Truncation
open Int
open ConnectedProduct

module homotopy.BlakersMassey where

  module P = Pushout
  open P using (Pushout ; Pushout-rec ; Pushout-elim)

  module BMEquiv 
    (X Y : Type)
    (P : X → Y → Type)
    (x0 : X) (y0 : Y) (p0 : P x0 y0)
    (i' j' : TLevel)
    (cX : (x : X) → Connected (S i') (Σ[ y ∶ Y ] P x y))
    (cY : (y : Y) → Connected (S j') (Σ[ x ∶ X ] P x y))
    (-2<i' : -2 <tl i')
    (-2<j' : -2 <tl j')
    (k : TLevel)
    (k< : k <=tl (plus2 i' j'))
    where

    i : TLevel
    i = S i'

    j : TLevel
    j = S j'

    Pa : Pushout X Y P -> Type 
    Pa o = Trunc k (Path {Pushout X Y P} (P.inl x0) o)

    decode' : ∀ {x y} → Trunc k (P x y) → Trunc k (Path {Pushout X Y P} (P.inl x) (P.inr y))
    decode' = Trunc-func P.cross


    abstract
      -- Codes-cross' : (a : (Σ \ (x : X) -> P x y)) → (Σ \ (y : Y) → (Trunc k (P (fst a) y0))) → (Trunc k (P x0 y))
      -- Codes-cross' = ?

      Codes-cross : (x : X) (y : Y) → P x y → (Trunc k (P x y0)) → (Trunc k (P x0 y))
      Codes-cross x y px py = {!!}
  
{-
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
-}

    Codes : Pushout X Y P -> Type 
    Codes = Pushout-rec (λ x → Trunc k (P x y0))
                        (λ y → Trunc k (P x0 y))
                        {!!}

{-
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
-}

    eqv : (y : Y) → Equiv (Trunc k (P x0 y)) (Trunc k (Path {Pushout X Y P} (P.inl x0) (P.inr y)))
    eqv = {!!} -- (improve (hequiv decode' encode encode-decode' decode-encode))

{-
    path : Trunc k X ≃ Trunc k (Path {(Susp X)} No No)
    path = ua eqv -- ua (improve (hequiv decode' encode encode-decode' decode-encode))

-}