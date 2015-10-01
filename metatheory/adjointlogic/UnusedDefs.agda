
open import adjointlogic.Lib
open import adjointlogic.Rules
open import adjointlogic.Properties
open import adjointlogic.General


module adjointlogic.UnusedDefs where

  -- justification for the definition of adjunction isomorphism; not fully formalized

  record IsoAdjMor0 {p q : Mode} {L L' : Functor p q} {R R' : Functor q p} (a1 : Adjunction L R) (a2 : Adjunction L' R') : Set where
    constructor iso
    field
      f : AdjMor a1 a2
      g : AdjMor a2 a1
      α : (f ·AdjMor g) == 1AdjMor {a = a1}
      β : (g ·AdjMor f) == 1AdjMor

  record IsoAdjMor' {p q : Mode} {L L' : Functor p q} {R R' : Functor q p} (a1 : Adjunction L R) (a2 : Adjunction L' R') : Set where
    constructor iso
    field
      f : AdjMor a1 a2
      g : AdjMor a2 a1
      -- we think of ≈ as being squashed to an hprop, or really should be using a set quotient of derivations mod ≈ 
      -- so:
      --   two adjunction morphisms are equal just when their two natural transformations are equal
      --   two natural transformations are equal just when their morphisms are equal for all A
      -- therefore, the == in IsoAdjMor unpack to this
      α1 : ∀ {A} → (cut (NatTrans.mor (AdjMor.LL f) {A}) (NatTrans.mor (AdjMor.LL g) {A})) ≈ hyp
      α2 : ∀ {A} → (cut (NatTrans.mor (AdjMor.RR g) {A}) (NatTrans.mor (AdjMor.RR f) {A})) ≈ hyp
      β1 : ∀ {A} → (cut (NatTrans.mor (AdjMor.LL g) {A}) (NatTrans.mor (AdjMor.LL f) {A})) ≈ hyp
      β2 : ∀ {A} → (cut (NatTrans.mor (AdjMor.RR f) {A}) (NatTrans.mor (AdjMor.RR g) {A})) ≈ hyp


  check1 : {p q : Mode} {L L' : Functor p q} {R R' : Functor q p} {a1 : Adjunction L R} {a2 : Adjunction L' R'}
           → IsoAdjMor' a1 a2
           → AdjIso a1 a2
  check1(iso (adjmor LL RR conjugate) (adjmor LL2 RR2 conjugate2) α1 α2 β1 β2) = 
    iso (natiso (iso (NatTrans.mor LL) (NatTrans.mor LL2) α1 β1) (NatTrans.square LL))
        (natiso (iso (NatTrans.mor RR) (NatTrans.mor RR2) β2 α2) (NatTrans.square RR))
        conjugate 

  check2 : {p q : Mode} {L L' : Functor p q} {R R' : Functor q p} {a1 : Adjunction L R} {a2 : Adjunction L' R'}
           → AdjIso a1 a2
           → IsoAdjMor' a1 a2
  check2 {L = L}{L'}{R}{R'}{a1}{a2} (iso LL RR conjugate) = 
         iso (adjmor (nat (Iso.f (NatIso.mor LL)) (NatIso.square LL))
                     (nat (Iso.f (NatIso.mor RR)) (NatIso.square RR))
                     conjugate) 
             (adjmor (nat (Iso.g (NatIso.mor LL)) {!need to derive the other square!}) (nat (Iso.g (NatIso.mor RR)) otherSquareR) 
                     ({!otherSquareR, reassociate, collapse inverses!} ∘≈ cut≈1 (!≈ fact1) (Functor.ar R' (Iso.g (NatIso.mor LL)))))
             (Iso.α (NatIso.mor LL)) (Iso.β (NatIso.mor RR)) (Iso.β (NatIso.mor LL)) (Iso.α (NatIso.mor RR))  where
         fact1 : ∀ {A} → cut (cut (Adjunction.LtoR a1 hyp) (Functor.ar R (Iso.f (NatIso.mor LL)))) (Iso.g (NatIso.mor RR)) ≈
                 (Adjunction.LtoR a2 {A = A} hyp)
         fact1 = {!cut≈1 conjugate (Iso.g (NatIso.mor RR))!} -- then reassoc and collapse inverses

         otherSquareR : ∀ {A B} (D : A [ 1m ]⊢ B) →
                        cut (Iso.g (NatIso.mor RR)) (Functor.ar R' D) ≈
                        cut (Functor.ar R D) (Iso.g (NatIso.mor RR))
         otherSquareR = {!!}

  check12 : {p q : Mode} {L L' : Functor p q} {R R' : Functor q p} {a1 : Adjunction L R} {a2 : Adjunction L' R'}
            (mor : IsoAdjMor' a1 a2) → check2 (check1 mor) == mor
  check12 mor = {!!}

  check21 : {p q : Mode} {L L' : Functor p q} {R R' : Functor q p} {a1 : Adjunction L R} {a2 : Adjunction L' R'}
            (mor : AdjIso a1 a2) → check1 (check2 mor) == mor
  check21 mor = {!!}
