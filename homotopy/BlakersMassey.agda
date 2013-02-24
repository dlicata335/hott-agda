-- Peter Lumsdaine, Eric Finster, and Dan Licata

{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open Truncation
open Int
open ConnectedSigma

module homotopy.BlakersMassey where

  module P = Pushout
  open P using (Pushout ; Pushout-rec ; Pushout-elim)

  module BMEquiv 
    (X Y : Type)
    (P : X → Y → Type)
    (x0 : X) (y0 : Y) (p0 : P x0 y0)
    (i' j' : TLevel)
    (cY : (x : X) → Connected (S i') (Σ[ y ∶ Y ] P x y))
    (cX : (y : Y) → Connected (S j') (Σ[ x ∶ X ] P x y))
    (-2<i' : -2 <tl i')
    (-2<j' : -2 <tl j')
    (k : TLevel)
    -- (k> : -1 <=tl k) 
    (k< : k <=tl (plus2 j' i'))
    where

    i : TLevel
    i = S i'

    j : TLevel
    j = S j'

    Pa : Pushout X Y P -> Type 
    Pa o = Trunc k (Path {Pushout X Y P} (P.inl x0) o)

    decode' : ∀ {x y} → Trunc k (P x y) → Trunc k (Path {Pushout X Y P} (P.inl x) (P.inr y))
    decode' = Trunc-func P.cross


    a0 : (Σ \ (x : X) -> (P x y0))
    a0 = x0 , p0

    b0 : (a : (Σ \ (x : X) -> (P x y0))) → Σ \ (y : Y) → P (fst a) y
    b0 (x , px) = y0 , px

    abstract
      Codes-cross' : (a : (Σ \ (x : X) -> (P x y0)))
                   → (b : Σ \ (y : Y) → P (fst a) y) 
                   → Trunc k (P x0 (fst b))
      Codes-cross' = wedge-elim
                       {A = Σ (λ (x : X) → P x y0)}
                       {B = λ a → Σ (λ (y : Y) → P (fst a) y)}
                       (cX _) (λ xpx → cY (fst xpx))
                       (λ a b → Trunc k (P x0 (fst b)) , Trunc-level)
                       k< {a0} {b0} 
                       (λ ypy → [ snd ypy ])
                       (λ xpx → [ p0 ])
                       id

      Codes-cross : (x : X) (y : Y) → P x y → (Trunc k (P x y0)) → (Trunc k (P x0 y))
      Codes-cross x y py px = Trunc-rec Trunc-level (λ px' → Codes-cross' (x , px') (y , py)) px 
  
      Codes-cross-βa : (\ y py -> Codes-cross x0 y py [ p0 ]) ≃ (\ y py -> [ py ])
      Codes-cross-βa = λ≃ (\ y -> λ≃ \ py -> 
                       ap≃ (wedge-elim-βa
                       {A = Σ (λ (x : X) → P x y0)}
                       {B = λ a → Σ (λ (y : Y) → P (fst a) y)}
                       (cX _) (λ xpx → cY (fst xpx))
                       (λ a b → Trunc k (P x0 (fst b)) , Trunc-level)
                       k< {a0} {b0} 
                       (λ ypy → [ snd ypy ])
                       (λ xpx → [ p0 ])
                       id) {(y , py)})

      Codes-cross-βb : (\ x px -> Codes-cross x y0 px [ px ]) ≃ (λ _ _ → [ p0 ])
      Codes-cross-βb = λ≃ (\ y -> λ≃ \ py -> 
                       ap≃ (wedge-elim-βb
                       {A = Σ (λ (x : X) → P x y0)}
                       {B = λ a → Σ (λ (y : Y) → P (fst a) y)}
                       (cX _) (λ xpx → cY (fst xpx))
                       (λ a b → Trunc k (P x0 (fst b)) , Trunc-level)
                       k< {a0} {b0} 
                       (λ ypy → [ snd ypy ])
                       (λ xpx → [ p0 ])
                       id) {(y , py)})

      Codes-cross-coh : ap≃ (ap≃ Codes-cross-βb {x0}) {p0}
                      ≃ ap≃ (ap≃ Codes-cross-βa {y0}) {p0}
      Codes-cross-coh = 
                       {!!} ∘
                         wedge-elim-coh {A = Σ (λ (x : X) → P x y0)}
                         {B = λ a → Σ (λ (y : Y) → P (fst a) y)} (cX _)
                         (λ xpx → cY (fst xpx))
                         (λ a b → Trunc k (P x0 (fst b)) , Trunc-level) k< {a0} {b0}
                         (λ ypy → [ snd ypy ]) (λ xpx → [ p0 ]) id
                         ∘ {!!}
 
      Codes-cross-isequiv : (x : X) (y : Y) → (p : P x y) 
                           -> IsEquiv (Codes-cross x y p)
      Codes-cross-isequiv x y p = {!!}

      Codes-cross-isweq : (x : X) (y : Y) → (p : P x y) 
                           -> IsWEq (Codes-cross x y p)
      Codes-cross-isweq x y p = Trunc-elim _ (λ _ → raise-level {!!} (Contractible-is-HProp _)) 
        (λ px0y → 
         wedge-elim {A = Σ (\ y -> P x0 y)}
                    {B = \a -> Σ (\ x -> P x (fst a))}
                    (cY _) (λ a → cX (fst a))
                    (\ a b -> Contractible (HFiber (Codes-cross (fst b) (fst a) (snd b)) [ snd a ]) , Contractible-is-HProp _)
                    {!!} {y0 , p0} {\ a -> x0 , snd a}
                    (λ {(x , pxy0) → ([ pxy0 ] , ap≃ (ap≃ Codes-cross-βb)) , 
                                     (λ {(tpxy0 , α) → {!!}})})
                    {!!}
                    (HProp-unique (Contractible-is-HProp _) _ _) 
                    (y , px0y) (x , p))

{-  
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
-}

{-
    Codes-cross-equiv : (x : X) (y : Y) (p : P x y) -> Equiv (Trunc k (P x y0)) (Trunc k (P x0 y))
    Codes-cross-equiv x y p = ((Codes-cross x y p) , Codes-cross-isequiv x y p)

    Codes : Pushout X Y P -> Type 
    Codes = Pushout-rec (λ x → Trunc k (P x y0))
                        (λ y → Trunc k (P x0 y))
                        (λ x y p → ua (Codes-cross-equiv x y p))

    NType-Codes : (x : Pushout X Y P) -> NType k (Codes x)
    NType-Codes = Pushout-elim _ (\ _ -> Trunc-level) (\ _ -> Trunc-level) (λ _ _ _ → HProp-unique (NType-is-HProp _) _ _)

    encode0 : ∀ {y : _} → Path (P.inl x0) y → Codes y
    encode0 α = transport Codes α [ p0 ]

    encode : ∀ {x : _} → Pa x → Codes x
    encode{x} tα = Trunc-rec (NType-Codes x) encode0 tα

    abstract
      encode-decode' : (y : _) (p : Trunc k (P x0 y)) → encode (decode' p) ≃ p
      encode-decode' y = Trunc-elim _ (λ _ → path-preserves-level Trunc-level) 
        (λ py → encode (decode' [ py ]) ≃〈 id 〉 
               encode [ P.cross py ] ≃〈 id 〉 
               transport Codes (P.cross py) [ p0 ] ≃〈 ap≃ (transport-ap-assoc Codes (P.cross py)) 〉 
               coe (ap Codes (P.cross py)) [ p0 ] ≃〈 {!!} 〉 
               coe (ua (Codes-cross-equiv x0 y py)) [ p0 ] ≃〈 ap≃ (type≃β (Codes-cross-equiv _ _ py)) 〉 
               Codes-cross x0 y py [ p0 ] ≃〈 ap≃ (ap≃ Codes-cross-βa) 〉 
               [ py ] ∎)

    decode : ∀ {x} -> Codes x → Pa x
    decode {x} = Pushout-elim (\ x -> Codes x → Pa x)
                              (λ x → Trunc-func (λ px → ! (P.cross px) ∘ P.cross p0))
                              (λ _ → decode') 
                              (λ x y p →
                                  transport (λ x0 → Codes x0 → Pa x0) (P.cross p) (Trunc-func (λ px → ! (P.cross px) ∘ P.cross p0)) ≃〈 {!!} 〉
                                  transport Pa (P.cross p) o (Trunc-func (λ px → ! (P.cross px) ∘ P.cross p0)) o transport Codes (! (P.cross p)) ≃〈 {! move-posto-with-transport-left Codes (mer x') (transport P (mer x') o decode') (Trunc-func (λ x0 → mer x0)) (λ≃ (STS x')) !}〉
                                  decode' ∎)
                              x where
     abstract
       STS : ∀ x y (p : P x y) p' 
             -> transport Pa (P.cross p) ((Trunc-func (λ px → ! (P.cross px) ∘ P.cross p0)) p')
              ≃ decode' (transport Codes (P.cross p) p')
       STS x y p = Trunc-elim _ (λ _ → path-preserves-level Trunc-level)
        (\ pxy0 -> wedge-elim {A = Σ (λ (x' : X) → P x' y0)}
          {B = λ a → Σ (λ (y' : Y) → P (fst a) y')} (cX _) (λ xpx → cY (fst xpx))
          (λ a b →
             transport Pa (P.cross (snd b))
             (Trunc-func (λ px → ! (P.cross px) ∘ P.cross p0) [ snd a ])
             ≃ decode' (transport Codes (P.cross (snd b)) [ snd a ])
             , path-preserves-level Trunc-level)
          k<
          {a0} {b0}
          (λ {(y , px0y) → 
               (transport Pa (P.cross px0y) (Trunc-func (λ px → ! (P.cross px) ∘ P.cross p0) [ p0 ]) ≃〈 id 〉
                transport Pa (P.cross px0y) [ ! (P.cross p0) ∘ P.cross p0 ] ≃〈 {!!} 〉
                [ (P.cross px0y) ∘ ! (P.cross p0) ∘ P.cross p0 ] ≃〈 {!!} 〉
                [ (P.cross px0y) ] ≃〈 id 〉
                decode' [ px0y ] ≃〈 {!!} 〉 
                decode' (Codes-cross x0 y px0y [ p0 ]) ≃〈 {!!} 〉 
                decode' (coe (ua (Codes-cross-equiv _ _ px0y)) [ p0 ]) ≃〈 {!!} 〉 
                decode' (coe (ap Codes (P.cross px0y)) [ p0 ]) ≃〈 {!!} 〉 
                decode' (transport Codes (P.cross px0y) [ p0 ]) ∎) })
          (λ {(x , pxy0) → 
                transport Pa (P.cross pxy0) (Trunc-func (λ px → ! (P.cross px) ∘ P.cross p0) [ pxy0 ]) ≃〈 {!!} 〉
                transport Pa (P.cross pxy0) [ ! (P.cross pxy0) ∘ P.cross p0 ] ≃〈 {!!} 〉
                [ (P.cross pxy0) ∘ ! (P.cross pxy0) ∘ P.cross p0 ] ≃〈 {!!} 〉
                [ P.cross p0 ] ≃〈 id 〉
                decode' [ p0 ] ≃〈 {!!} 〉 
                decode' (Codes-cross x y0 pxy0 [ pxy0 ]) ≃〈 {!!} 〉 
                decode' (coe (ua (Codes-cross-equiv _ _ pxy0)) [ pxy0 ]) ≃〈 {!!} 〉 
                decode' (coe (ap Codes (P.cross pxy0)) [ pxy0 ]) ≃〈 {!!} 〉 
                decode' (transport Codes (P.cross pxy0) [ pxy0 ]) ∎
             })
          {!!}
          (x , pxy0) (y , p))

    decode-encode : ∀ {x : _} (α : Pa x) -> decode (encode α) ≃ α
    decode-encode tα = Trunc-elim (\ α -> decode (encode α) ≃ α) (λ x → path-preserves-level Trunc-level) 
                                  (path-induction (λ _ p → decode (encode [ p ]) ≃ [ p ])
                                                  (ap [_] (!-inv-l (P.cross p0))))
                                  tα

    eqv : (y : Y) → Equiv (Trunc k (P x0 y)) (Trunc k (Path {Pushout X Y P} (P.inl x0) (P.inr y)))
    eqv y = (improve (hequiv decode' encode (encode-decode' y) decode-encode))

{-
    path : Trunc k X ≃ Trunc k (Path {(Susp X)} No No)
    path = ua eqv -- ua (improve (hequiv decode' encode encode-decode' decode-encode))

-}

-}