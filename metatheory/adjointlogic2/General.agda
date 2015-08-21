
open import adjointlogic2.Lib
open import adjointlogic2.Rules
open import adjointlogic2.Properties

module adjointlogic2.General where

  -- a bunch of category theory definitions specialized to the categories used here

  record Iso {p : Mode} (A B : Tp p) : Set where
    constructor iso
    field
      f : A [ 1m ]⊢ B
      g : B [ 1m ]⊢ A
      α : cut f g ≈ hyp
      β : cut g f ≈ hyp

  _·i_ : {p : Mode} {A B C : Tp p} → Iso A B → Iso B C → Iso A C
  iso f g α β ·i iso f' g' α' β' = 
      iso (cut f f') (cut g' g) 
             ((((α ∘≈ cut≈2 f (cut-ident-left g)) ∘≈ cut≈2 f (cut≈1  α' g)) ∘≈ cut≈2 f (cut-assoc f' g' g)) ∘≈ !≈ (cut-assoc f f' (cut g' g))) 
             ((((β' ∘≈ cut≈2 g' (cut-ident-left f')) ∘≈ cut≈2 g' (cut≈1 β f')) ∘≈ cut≈2 g' (cut-assoc g f f')) ∘≈ !≈ (cut-assoc g' g (cut f f'))) 

  !i : {p : Mode} {A B : Tp p} → Iso A B → Iso B A
  !i (iso f g α β) = iso g f β α

  ⊕i : ∀ {p : Mode} {A A' B B' : Tp p} → Iso A A' → Iso B B' → Iso (A ⊕ B) (A' ⊕ B')
  ⊕i (iso f g α β) (iso f₁ g₁ α₁ β₁) = 
    iso (Case (cut f (Inl hyp)) (cut f₁ (Inr hyp))) (Case (cut g (Inl hyp)) (cut g₁ (Inr hyp))) 
        (Case≈ ((((cut-ident-left _ ∘≈  cut≈1 α (Inl hyp)) ∘≈ cut-assoc f g (Inl hyp)) ∘≈ (cut≈2 f (cut-ident-left _))) ∘≈ !≈ (cut-assoc f (Inl hyp) (Case (cut g (Inl hyp)) (cut g₁ (Inr hyp))))) ((((cut-ident-left _ ∘≈ cut≈1 α₁ (Inr hyp)) ∘≈ cut-assoc f₁ g₁ (Inr hyp)) ∘≈ cut≈2 f₁ (cut-ident-left _)) ∘≈ !≈ (cut-assoc f₁ (Inr hyp) (Case (cut g (Inl hyp)) (cut g₁ (Inr hyp))))))
        (Case≈ ((((cut-ident-left _ ∘≈ cut≈1 β (Inl hyp)) ∘≈ cut-assoc g f (Inl hyp)) ∘≈ cut≈2 g (cut-ident-left _)) ∘≈ !≈ (cut-assoc g (Inl hyp) (Case (cut f (Inl hyp)) (cut f₁ (Inr hyp))))) ((((cut-ident-left _ ∘≈ cut≈1 β₁ (Inr hyp)) ∘≈ cut-assoc g₁ f₁ (Inr hyp)) ∘≈ cut≈2 g₁ (cut-ident-left _)) ∘≈ !≈ (cut-assoc g₁ (Inr hyp) (Case (cut f (Inl hyp)) (cut f₁ (Inr hyp))))))

  record Functor (p q : Mode) : Set where 
    constructor func
    field
     ob : Tp p -> Tp q  
     ar : ∀ {A B : Tp p} → A [ 1m ]⊢ B → ob A [ 1m ]⊢ ob B
     ar≈ : ∀ {A B : Tp p} {D1 D2 : A [ 1m ]⊢ B} → D1 ≈ D2 → ar D1 ≈ ar D2
     presid  : ∀ {A : Tp p} → ar (ident A) ≈ ident (ob A)
     prescut : ∀ {A B C : Tp p} (D1 : A [ 1m ]⊢ B) (D2 : B [ 1m ]⊢ C)
             → ar (cut D1 D2) ≈ cut (ar D1) (ar D2)

  1Func : ∀ {p} → Functor p p
  1Func = func (\ x -> x) (\ D -> D) (\ x -> x) id (\ _ _ -> id)

  _∘Func_ : ∀ {p q r} → Functor q r → Functor p q → Functor p r 
  _∘Func_ H G = func (λ X → Functor.ob H (Functor.ob G X)) (λ D → Functor.ar H (Functor.ar G D)) (λ q → Functor.ar≈ H (Functor.ar≈ G q)) (Functor.presid H ∘≈ Functor.ar≈ H (Functor.presid G)) (λ D1 D2 → Functor.prescut H _ _ ∘≈ Functor.ar≈ H (Functor.prescut G D1 D2))

  record NatTrans {p q : Mode} (G1 G2 : Functor p q) : Set where
    constructor nat
    field
      mor    : {A : Tp p} → Functor.ob G1 A [ 1m ]⊢ Functor.ob G2 A
      square : {A B : Tp p} (D : A [ 1m ]⊢ B)
             → cut (mor {A}) (Functor.ar G2 D) ≈ cut (Functor.ar G1 D) (mor {B})

  1NatTrans : ∀ {p q : Mode} {G : Functor p q} → NatTrans G G 
  1NatTrans {G = G} = nat hyp (λ D → !≈ (cut-ident-right (Functor.ar G D)) ∘≈ cut-ident-left (Functor.ar G D))

  _·NatTrans_ : ∀ {p q : Mode} {G1 G2 G3 : Functor p q} → NatTrans G1 G2 → NatTrans G2 G3 → NatTrans G1 G3
  _·NatTrans_ {G1 = G1}{G2}{G3} n1 n2 = nat (cut (NatTrans.mor n1) (NatTrans.mor n2)) (λ D → !≈ (cut-assoc (Functor.ar G1 D) (NatTrans.mor n1) (NatTrans.mor n2)) ∘≈ cut≈1 (NatTrans.square n1 D) (NatTrans.mor n2) ∘≈ cut-assoc (NatTrans.mor n1) (Functor.ar G2 D) (NatTrans.mor n2) ∘≈ cut≈2 (NatTrans.mor n1) (NatTrans.square n2 D) ∘≈ !≈ (cut-assoc (NatTrans.mor n1) (NatTrans.mor n2) (Functor.ar G3 D)))

  -- it's a theorem that a natural isomorphism is the same as an isomorphism of natural transformations
  record NatIso {p q : Mode} (G1 G2 : Functor p q) : Set where
    constructor natiso
    field
      mor    : {A : Tp p} → Iso (Functor.ob G1 A) (Functor.ob G2 A) 
      square : {A B : Tp p} (D : A [ 1m ]⊢ B)
             → cut (Iso.f (mor {A})) (Functor.ar G2 D) ≈ cut (Functor.ar G1 D) (Iso.f (mor {B}))

  !natiso : {p q : Mode} {G1 G2 : Functor p q} → NatIso G1 G2 → NatIso G2 G1
  !natiso i = natiso (!i (NatIso.mor i)) (λ D → {!NatIso.square i D!})

  square' : {p q : Mode} {G1 G2 : Functor p q} {A B : Tp p} 
          → (i : NatIso G1 G2) (D : A [ 1m ]⊢ B)
          → (Functor.ar G1 D) ≈ cut (Iso.f (NatIso.mor i {A})) (cut (Functor.ar G2 D) (Iso.g (NatIso.mor i {B})))
  square' = {!!}

  NatIso-forward : ∀ {p q : Mode} {G1 G2 : Functor p q} → NatIso G1 G2 → NatTrans G1 G2
  NatIso-forward i = nat (Iso.f (NatIso.mor i)) (NatIso.square i)

  -- natural bijection on hom sets
  record Adjunction (p q : Mode) : Set where
    constructor adj
    field 
      L : Functor p q
      R : Functor q p
      LtoR : ∀ {A B} → Functor.ob L A [ 1m ]⊢ B → A [ 1m ]⊢ Functor.ob R B
      RtoL : ∀ {A B} → A [ 1m ]⊢ Functor.ob R B → Functor.ob L A [ 1m ]⊢ B
      LtoR≈ : ∀ {A B} → {D1 D2 : Functor.ob L A [ 1m ]⊢ B} → D1 ≈ D2 → LtoR D1 ≈ LtoR D2
      RtoL≈ : ∀ {A B} → {D1 D2 : A [ 1m ]⊢ Functor.ob R B} → D1 ≈ D2 → RtoL D1 ≈ RtoL D2
      LtoRtoL : ∀ {A B} → (D : Functor.ob L A [ 1m ]⊢ B) 
                        → RtoL (LtoR D) ≈ D
      RtoLtoR : ∀ {A B} → (D : A [ 1m ]⊢ Functor.ob R B) 
                        → LtoR (RtoL D) ≈ D
      LtoRnat : ∀ {A A' B B'} 
                → (D1 : A' [ 1m ]⊢ A) (D : Functor.ob L A [ 1m ]⊢ B) (D2 : B [ 1m ]⊢ B')
                →   LtoR (cut (Functor.ar L D1) (cut D D2))
                  ≈ cut D1 (cut (LtoR D) (Functor.ar R D2))
      RtoLnat : ∀ {A A' B B'} 
                → (D1 : A' [ 1m ]⊢ A) (D : A [ 1m ]⊢ Functor.ob R B) (D2 : B [ 1m ]⊢ B')
                →   RtoL (cut D1 (cut D (Functor.ar R D2)))
                  ≈ cut (Functor.ar L D1) (cut (RtoL D) D2)

  1Adj : ∀ {p} → Adjunction p p
  1Adj = adj 1Func 1Func (λ D → D) (λ D → D) (\ q -> q) (\ q -> q) (λ _ → id) (λ _ → id) (λ _ _ _ → id) (λ _ _ _ → id)

  _·Adj_ : ∀ {p q r} → Adjunction p q → Adjunction q r → Adjunction p r 
  _·Adj_ a1 a2 = adj (Adjunction.L a2 ∘Func Adjunction.L a1) (Adjunction.R a1 ∘Func Adjunction.R a2)
                   (λ D → Adjunction.LtoR a1 (Adjunction.LtoR a2 D)) 
                   (λ D → Adjunction.RtoL a2 (Adjunction.RtoL a1 D))
                   (λ q → Adjunction.LtoR≈ a1 (Adjunction.LtoR≈ a2 q)) 
                   (λ q → Adjunction.RtoL≈ a2 (Adjunction.RtoL≈ a1 q))
                   (λ D → Adjunction.LtoRtoL a2 D ∘≈ Adjunction.RtoL≈ a2 (Adjunction.LtoRtoL a1 _))
                   (λ D → Adjunction.RtoLtoR a1 D ∘≈ Adjunction.LtoR≈ a1 (Adjunction.RtoLtoR a2 _))
                   (λ D1 D D2 → {!Adjunction.LtoRnat a2 D1 D D2!}) {!!}

  record AdjMor {p q : Mode} (a1 : Adjunction p q) (a2 : Adjunction p q) : Set where
    constructor adjmor
    field
      LL        : NatTrans (Adjunction.L a1) (Adjunction.L a2)
      RR        : NatTrans (Adjunction.R a2) (Adjunction.R a1)
      -- one of many ways to phrase this; see
      -- https://unapologetic.wordpress.com/2007/07/30/transformations-of-adjoints/
      conjugate : ∀ {A} → cut (Adjunction.LtoR a1 hyp) (Functor.ar (Adjunction.R a1) (NatTrans.mor LL {A})) ≈ cut (Adjunction.LtoR a2 hyp) (NatTrans.mor RR {Functor.ob (Adjunction.L a2) A})

  record _==AdjMor_ {p q : Mode} {a1 : Adjunction p q} {a2 : Adjunction p q} (mor1 : AdjMor a1 a2) (mor2 : AdjMor a1 a2) : Set where
    constructor eqadjmor
    field 
      eq1 : ∀ {A} → NatTrans.mor (AdjMor.LL mor1) {A = A} ≈ NatTrans.mor (AdjMor.LL mor2)
      eq2 : ∀ {A} → NatTrans.mor (AdjMor.RR mor1) {A = A} ≈ NatTrans.mor (AdjMor.RR mor2)

  1AdjMor : {p q : Mode} {a : Adjunction p q}
          → AdjMor a a 
  1AdjMor {a = a} = adjmor 1NatTrans 1NatTrans (cut≈2 (Adjunction.LtoR a hyp) (Functor.presid (Adjunction.R a)))

  _·AdjMor_ : {p q : Mode} {a1 : Adjunction p q} {a2 : Adjunction p q} {a3 : Adjunction p q}
          → AdjMor a1 a2
          → AdjMor a2 a3
          → AdjMor a1 a3
  _·AdjMor_ {a1 = a1}{a2}{a3} mor1 mor2 = 
    adjmor (AdjMor.LL mor1 ·NatTrans AdjMor.LL mor2)
           (AdjMor.RR mor2 ·NatTrans AdjMor.RR mor1) 
           {!AdjMor.conjugate mor1!}

  _·Adj-cong_ : ∀ {p q r} {a1 a1' : Adjunction p q} {a2 a2' :  Adjunction q r}
                → AdjMor a1 a1'
                → AdjMor a2 a2'
                → AdjMor (a1 ·Adj a2) (a1' ·Adj a2')
  _·Adj-cong_ {a1 = a1}{a1'}{a2}{a2'} mor1 mor2 = adjmor (nat (cut (Functor.ar (Adjunction.L a2) (NatTrans.mor (AdjMor.LL mor1))) (NatTrans.mor (AdjMor.LL mor2))) {!!}) (nat (cut (Functor.ar (Adjunction.R a1') (NatTrans.mor (AdjMor.RR mor2))) (NatTrans.mor (AdjMor.RR mor1))) {!!}) {!!}


  record AdjIso {p q : Mode} (a1 : Adjunction p q) (a2 : Adjunction p q) : Set where
    constructor adjiso
    field
      LL        : NatIso (Adjunction.L a1) (Adjunction.L a2)
      RR        : NatIso (Adjunction.R a2) (Adjunction.R a1)
      conjugate : ∀ {A} → cut (Adjunction.LtoR a1 hyp) (Functor.ar (Adjunction.R a1) (Iso.f (NatIso.mor LL {A}))) ≈ cut (Adjunction.LtoR a2 hyp) (Iso.f (NatIso.mor RR {Functor.ob (Adjunction.L a2) A}))

  AdjIso-forward : {p q : Mode} {a1 : Adjunction p q} {a2 : Adjunction p q}
                → AdjIso a1 a2 → AdjMor a1 a2
  AdjIso-forward i = adjmor (NatIso-forward (AdjIso.LL i)) (NatIso-forward (AdjIso.RR i)) (AdjIso.conjugate i)

            
  -- ----------------------------------------------------------------------
  -- F α and F β are different for two parallel but different α and β

  -- these should not be provable 
  {-
  diff1 : {p q : Mode} {α β : q ≥ p} {A : Tp q} → F α A [ 1m ]⊢ F β A
  diff1 = FL (FR 1m {!NO!} hyp)

  diff2 : {p q : Mode} {α β : q ≥ p} {A : Tp p} → U α A [ 1m ]⊢ U β A
  diff2 = UR (UL 1m {!NO!} hyp)
  -}

  -- ----------------------------------------------------------------------
  -- functoriality of F and U on terms

  Ffunc : ∀ {p q : Mode} {α : q ≥ p} {A B} → A [ 1m ]⊢ B → F α A [ 1m ]⊢ F α B
  Ffunc {α = α} D =  FL {α = α} {β = 1m} (FR 1m 1⇒ D)

  Ffunc-ident : ∀ {p q : Mode} {α : q ≥ p} {A} → Ffunc (ident A) ≈ (ident (F α A))
  Ffunc-ident = id

  Ffunc-cut : ∀ {p q : Mode} {α : q ≥ p} {A B C} (D : A [ 1m ]⊢ B) (E : B [ 1m ]⊢ C) → Ffunc {α = α} (cut D E) ≈ cut (Ffunc D) (Ffunc E)
  Ffunc-cut D E = eq (! (ap FL (transport⊢1 _)) ∘ ap FL (! (cutFR D)) )

  Ufunc : ∀ {p q : Mode} {α : q ≥ p} {A B} → A [ 1m ]⊢ B → U α A [ 1m ]⊢ U α B
  Ufunc {α = α} D =  UR {α = α} {β = 1m} (UL 1m 1⇒ D)

  Ufunc-ident : ∀ {p q : Mode} {α : q ≥ p} {A} → Ufunc (ident A) ≈ (ident (U α A))
  Ufunc-ident = id

  Ufunc-cut : ∀ {p q : Mode} {α : q ≥ p} {A B C} (D : A [ 1m ]⊢ B) (E : B [ 1m ]⊢ C) → Ufunc {α = α} (cut D E) ≈ cut (Ufunc D) (Ufunc E)
  Ufunc-cut D E = UR≈ (eq (! (transport⊢1 _)) ∘≈ (!≈ (cutUL E)))

  -- functoriality preserves equivalence
  
  Ffunc-i : ∀ {p q} {α : p ≥ q} {A B : Tp p} → Iso A B → Iso (F α A) (F α B)
  Ffunc-i (iso f g α β) = iso (Ffunc f) (Ffunc g) (FL≈ ((FR≈ α ∘≈ eq (cutFR f)) ∘≈ eq (transport⊢1 (cut f (FR 1m 1⇒ g))))) (FL≈ ((FR≈ β ∘≈ eq (cutFR g)) ∘≈ eq (transport⊢1 (cut g (FR 1m 1⇒ f)))))

  Ufunc-i : ∀ {p q} {α : p ≥ q} {A B : Tp q} → Iso A B → Iso (U α A) (U α B)
  Ufunc-i {α = α1} (iso f g α β) = iso (Ufunc f) (Ufunc g) (UR≈ {α = α1} {β = 1m ∘1 1m} ((UL≈ {e = 1⇒} α ∘≈ cutUL g) ∘≈ eq (transport⊢1 _))) (UR≈ {α = α1} {β = 1m ∘1 1m} ((UL≈ {e = 1⇒} β ∘≈ cutUL f) ∘≈ eq (transport⊢1 _)) )

  Ffunctor : ∀ {p q} (α : q ≥ p) → Functor q p 
  Ffunctor α = func (F α) Ffunc (λ D → FL≈ (FR≈ D)) Ffunc-ident Ffunc-cut

  Ufunctor : ∀ {p q} (α : q ≥ p) → Functor p q
  Ufunctor α = func (U α) Ufunc (λ D → UR≈ (UL≈ D)) Ufunc-ident Ufunc-cut

  -- ----------------------------------------------------------------------
  -- F -| U

  UFadjunction1 : ∀ {p q} {A B} {α : q ≥ p} → F α A [ 1m ]⊢ B → A [ 1m ]⊢ U α B
  UFadjunction1 {α = α} D = UR {α = α} {β = 1m} (cut (FR 1m 1⇒ hyp) D) 

  UFadjunction2 : ∀ {p q} {A B} {α : q ≥ p} → A [ 1m ]⊢ U α B → F α A [ 1m ]⊢ B 
  UFadjunction2 {α = α} D = FL {α = α} {β = 1m} (cut D (UL 1m 1⇒ hyp)) 

  UFadj-composite2 : ∀ {p q} {A B} {α : q ≥ p} (D : F α A [ 1m ]⊢ B ) -> UFadjunction2 (UFadjunction1 D) ≈ D
  UFadj-composite2 D = (!≈ (Fη D) ∘≈ FL≈ (cut-ident-right _ ∘≈ eq (transport⊢1 _)))

  UFadj-composite1 : ∀ {p q} {A B} {α : q ≥ p} (D : A [ 1m ]⊢ U α B) -> UFadjunction1 (UFadjunction2 D) ≈ D
  UFadj-composite1 D = !≈ (Uη D) ∘≈ UR≈ (cut-ident-left _ ∘≈ eq (transport⊢1 _))

  UFadjunction-nat1 : ∀ {p q} {A A' B B'} {α : q ≥ p} 
                      (D1 : A' [ 1m ]⊢ A) (D : F α A [ 1m ]⊢ B) (D2 : B [ 1m ]⊢ B')
                    → UFadjunction1 (cut (Ffunc D1) (cut D D2))
                    ≈ cut D1 (cut (UFadjunction1 D) (Ufunc D2))
  UFadjunction-nat1 D1 D D2 = !≈ (eq (cutUR D1)) ∘≈ UR≈ {β = 1m} ((((!≈ (cut≈2 D1 (eq (transport⊢1 (cut (cut (FR 1m 1⇒ hyp) D) D2)))) ∘≈ !≈ (cut-assoc D1 (cut (FR 1m 1⇒ hyp) D) D2) ∘≈ !≈ (cut≈1 (cut-assoc D1 (FR 1m 1⇒ hyp) D) D2) ∘≈ !≈ (cut≈1 (cut≈1 (eq (cutFR D1)) D) D2) ∘≈ !≈ (cut≈1 (cut≈1 (FR≈ (cut-ident-right D1)) D) D2) ∘≈ cut-assoc (FR 1m 1⇒ D1) D D2) ∘≈ cut≈1 (cut-ident-left (FR 1m 1⇒ D1)) (cut D D2)) ∘≈ cut≈1 (eq (transport⊢1 (cut hyp (FR 1m 1⇒ D1)))) (cut D D2)) ∘≈ cut-assoc (FR 1m 1⇒ hyp) (Ffunc D1) (cut D D2))

  UFadjunction-nat2 : ∀ {p q} {A A' B B'} {α : q ≥ p} 
                      (D1 : A' [ 1m ]⊢ A) (D : A [ 1m ]⊢ U α B) (D2 : B [ 1m ]⊢ B')
                    → UFadjunction2 (cut D1 (cut D (Ufunc D2)))
                    ≈ cut (Ffunc D1) (cut (UFadjunction2 D) D2)
  UFadjunction-nat2 {α = α} D1 D D2 = !≈ (cutFL {α = 1m} (cut (FL {α = α} {β = 1m} (cut D (UL 1m 1⇒ hyp))) D2)) ∘≈ FL≈ {α = α} {β = 1m} (!≈ (cut-assoc (FR 1m 1⇒ D1) (FL {α = α} {β = 1m} (cut D (UL 1m 1⇒ hyp))) D2) ∘≈ (((cut≈1 (eq (! (transport⊢1 (cut D1 (cut D (UL 1m 1⇒ hyp)))))) D2 ∘≈ cut-assoc D1 (cut D (UL 1m 1⇒ hyp)) D2 ∘≈ cut≈2 D1 (cut-assoc D (UL 1m 1⇒ hyp) D2) ∘≈ cut≈2 D1 (cut≈2 D (!≈ (cutUL D2))) ∘≈ cut≈2 D1 (cut≈2 D (UL≈ (!≈ (cut-ident-left D2))))) ∘≈ cut≈2 D1 (cut≈2 D (cut-ident-right (UL 1m 1⇒ D2) ∘≈ eq (transport⊢1 _)))) ∘≈ !≈ (cut≈2 D1 (cut-assoc D (UR {α = α} {β = 1m} (UL 1m 1⇒ D2)) (UL 1m 1⇒ hyp)))) ∘≈ !≈ (cut-assoc D1 (cut D (UR {α = α} {β = 1m} (UL 1m 1⇒ D2))) (UL 1m 1⇒ hyp)))


  -- ----------------------------------------------------------------------
  -- functoriality of F and U on 1-cells in the diagrams
  -- F is contravariant

  -- F/U on 1
  
  F11 : ∀ {p} {A : Tp p} → F 1m A [ 1m ]⊢ A
  F11 = FL {α = 1m} {β = 1m} hyp

  F12 : ∀ {p} {A : Tp p} → A [ 1m ]⊢ F 1m A
  F12 = FR 1m 1⇒ hyp

  F1-composite-1 : ∀ {p} {A : Tp p} → (cut (F11 {p = p} {A}) F12) ≈ hyp {_}{F 1m A}
  F1-composite-1 = FL≈ (FR≈ {e = 1⇒} (cut-ident-left _ ∘≈ eq (transport⊢1 _))) ∘≈ (Fη (FR 1m 1⇒ (FL {α = 1m} {β = 1m} hyp)) ∘≈ FR≈ (cut-ident-right _))

  F1-composite-2 : ∀ {p} {A : Tp p} → (cut F12 (F11 {p = p} {A})) ≈ hyp
  F1-composite-2 = cut-ident-left _ ∘≈ eq (transport⊢1 _)

  F11-nat : ∀ {p}{A A' : Tp p} (D : A [ 1m ]⊢ A') 
              → (cut F11 D) ≈ cut (Ffunc {α = 1m} D) (F11)
  F11-nat D = FL≈ {α = 1m} {β = 1m ∘1 1m} ((!≈ (eq (transport⊢1 _)) ∘≈ !≈ (cut-ident-right D)) ∘≈ cut-ident-left D)  ∘≈ cutFL D

  F1-iso : {p : Mode} {A : Tp p} → Iso (F 1m A) A
  F1-iso = iso F11 F12 F1-composite-1 F1-composite-2 

  F1-natiso : {p : Mode} → NatIso {p = p} (Ffunctor 1m) 1Func
  F1-natiso = natiso F1-iso F11-nat

  U11 : ∀ {p} {A : Tp p} → U 1m A [ 1m ]⊢ A
  U11 = UL 1m 1⇒ hyp

  U12 : ∀ {p} {A : Tp p} → A [ 1m ]⊢ U 1m A
  U12 = UR {α = 1m} {β = 1m} hyp

  U1-composite-1 : ∀ {p} {A : Tp p} → cut U11 U12 ≈ ident (U 1m A)
  U1-composite-1  = UR≈ {α = 1m}{β = 1m ∘1 1m} (UL≈ (cut-ident-left hyp) ∘≈ cutUL hyp)

  U1-composite-2 : ∀ {p} {A : Tp p} → cut U12 U11 ≈ ident A
  U1-composite-2 = cut-ident-left hyp ∘≈ eq (transport⊢1 _)

  U12-nat : ∀ {p}{A A' : Tp p} (D : A [ 1m ]⊢ A') 
              → (cut U12 (Ufunc D)) ≈ cut D (U12)
  U12-nat D = !≈ (eq (cutUR D)) ∘≈ UR≈ {α = 1m} {β = 1m} ((!≈ (cut-ident-right D) ∘≈ cut-ident-left D) ∘≈ (eq (transport⊢1 _)))

  U1-iso : {p : Mode} {A : Tp p} → Iso (U 1m A) A
  U1-iso = iso U11 U12 U1-composite-1 U1-composite-2 

  U1-natiso : {p : Mode} → NatIso {p = p} (Ufunctor 1m) 1Func
  U1-natiso = !natiso (natiso (!i U1-iso) U12-nat)

  FU1-conjugate : ∀ {p} {A : Tp p}
                    → cut (UFadjunction1 hyp) (Ufunc F11) ≈ cut (ident A) U12
  FU1-conjugate = !≈ (cut-ident-left U12) ∘≈ UR≈ {α = 1m} {β = 1m} (((cut-ident-right hyp ∘≈ eq (transport⊢1 _)) ∘≈ cut≈1 (cut-ident-left (FR 1m 1⇒ hyp) ∘≈ eq (transport⊢1 _)) F11) ∘≈ eq (transport⊢1 _))

  -- F/U on ∘

  F∘2 : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _}
          → F α (F β A) [ 1m ]⊢ F (β ∘1 α) A
  F∘2 = FL (FL (FR 1m 1⇒ hyp))

  F∘1 : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _}
          → F (β ∘1 α) A [ 1m ]⊢ F α (F β A)
  F∘1 {α = α} {β = β} = FL {α = β ∘1 α} {β = 1m} (FR β 1⇒ (FR 1m 1⇒ hyp)) 

  F∘-composite-2 : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _}
          → cut (F∘2 {α = α} {β = β} {A = A}) F∘1 ≈ hyp
  F∘-composite-2 {α = α} {β = β} = FL≈ (!≈ (Fη (FR 1m 1⇒ (FL (FR 1m 1⇒ hyp))))) ∘≈ eq (! (ap (λ x → FL (FL (FR β 1⇒ x))) (transport⊢1 _)) ) ∘≈ !≈ (FL≈ (FL≈ (FR≈ (cut-ident-left _)))) ∘≈ FL≈ (FL≈  (cut-ident-left _)) ∘≈ eq (ap FL (ap FL (transport⊢1 _))) 

  F∘-composite-1 : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _}
          → cut F∘1 (F∘2 {α = α} {β = β} {A = A}) ≈ hyp
  F∘-composite-1 = FL≈ ((cut-ident-left _ ∘≈ eq (transport⊢1 _)) ∘≈ eq (transport⊢1 _))

  F∘1-nat : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A A' : Tp _}
          → (D : A [ 1m ]⊢ A') 
          → cut F∘1 (Ffunc {α = α} (Ffunc {α = β} D)) ≈ cut (Ffunc D) F∘1
  F∘1-nat D = FL≈ (!≈ (eq (transport⊢1 _)) ∘≈ !≈ (eq (cutFR D)) ∘≈ FR≈ ((eq (! (cutFR D)) ∘≈ FR≈ (!≈ (cut-ident-right D))) ∘≈ cut-ident-left (FR 1m 1⇒ D) ∘≈ eq (transport⊢1 _)))

  F∘-iso : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _} → Iso (F (β ∘1 α) A) (F α (F β A))
  F∘-iso = iso F∘1 F∘2 F∘-composite-1 F∘-composite-2

  F∘-natiso : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} → NatIso (Ffunctor (β ∘1 α)) (Ffunctor α ∘Func Ffunctor β)
  F∘-natiso = natiso F∘-iso F∘1-nat

  U∘2 : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _}
          → U β (U α A) [ 1m ]⊢ U (β ∘1 α) A
  U∘2 {α = α} {β = β} = UR {α = β ∘1 α} {β = 1m} (UL α 1⇒ (UL 1m 1⇒ hyp))

  U∘1 : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _}
          → U (β ∘1 α) A [ 1m ]⊢ U β (U α A)
  U∘1 {α = α} {β = β} = UR {α = β} {β = 1m} (UR (UL 1m 1⇒ hyp)) 

  U∘-iso : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _} → Iso (U (β ∘1 α) A) (U β (U α A))
  U∘-iso {α = α} {β = β} = 
    iso U∘1 U∘2
        (UR≈ (cut-ident-right _ ∘≈ (eq (transport⊢1 _ ∘ transport⊢1 _))))
        (UR≈ {α = β} {β = 1m ∘1 1m} (!≈ (Uη _) ∘≈ UR≈ ((UL≈ {e = 1⇒} (!≈ (eq (transport⊢1 _)) ∘≈ !≈ (cut-ident-right _)) ∘≈ cut-ident-right (UL _ 1⇒ (UL 1m 1⇒ hyp))) ∘≈ eq (transport⊢1 _)) ) )

  U∘-natiso : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} → NatIso (Ufunctor (β ∘1 α)) (Ufunctor β ∘Func Ufunctor α)
  U∘-natiso {α = α}{β} = natiso U∘-iso (λ D → UR≈ (UR≈ (transport⊢≈ 1⇒ (((!≈ (cut-ident-right (UL 1m 1⇒ D)) ∘≈ UL≈ (cut-ident-left D)) ∘≈ cutUL D) ∘≈ eq (transport⊢1 _)))))

  FU∘-conjugate : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _} →
        cut (UFadjunction1 (ident (F (β ∘1 α) A))) (Ufunc F∘1) ≈ cut (UFadjunction1 (UFadjunction1 hyp)) U∘2
  FU∘-conjugate {α = α}{β = β} {A = A} = UR≈ {α = β ∘1 α} {β = 1m ∘1 1m} ((!≈ (eq (transport⊢1 _ ∘ transport⊢1 _ ∘ transport⊢1 _)) ∘≈ !≈ (cut≈1 (cut-ident-left (FR 1m 1⇒ hyp) ∘≈ eq (transport⊢1 _) ∘≈ cut-ident-left _ ∘≈ eq (transport⊢1 _)) (FR 1m 1⇒ (FL (FR 1m 1⇒ hyp)))) ∘≈ !≈ (FR≈ (cut-ident-left _ ∘≈ eq (transport⊢1 _))) ∘≈ (cut-ident-left _ ∘≈ eq (transport⊢1 _)) ∘≈ cut≈1 (cut-ident-left _ ∘≈ eq (transport⊢1 _)) (FL {α = β ∘1 α} {β = 1m} (FR β 1⇒ (FR 1m 1⇒ (ident A))))) ∘≈ eq (transport⊢1 _))

  -- action of F and U on terms is functorial in α
  -- corollaries of naturality

  F1-func : ∀ {p : Mode} {A B : Tp p} (D : A [ 1m ]⊢ B) 
              → Ffunc {α = 1m} {A} {B} D ≈ cut {α = 1m} {β = 1m} F11 (cut {α = 1m} {β = 1m} D F12)
  F1-func {p} {A = A} {B = B} D = square' {p = p} {q = p}{G1 = Ffunctor 1m} {G2 = 1Func} {A = A} {B = B} (F1-natiso) D

  F∘-func : ∀ {p q r : Mode} {α : p ≥ q} {β : q ≥ r} {A B : Tp p} (D : A [ 1m ]⊢ B) 
              →  (Ffunc {α = α ∘1 β} D) ≈ cut {α = 1m} {β = 1m} F∘1 (cut {α = 1m} {β = 1m} (Ffunc {α = β} (Ffunc {α = α} D)) F∘2)
  F∘-func D = square' F∘-natiso D 

  U1-func : ∀ {p : Mode} {A B : Tp p} (D : A [ 1m ]⊢ B) 
              → Ufunc {α = 1m} {A} {B} D ≈ cut {α = 1m} {β = 1m} U11 (cut {α = 1m} {β = 1m} D U12)
  U1-func {p} {A = A} {B = B} D = square' {p = p} {q = p}{G1 = Ufunctor 1m} {G2 = 1Func {p = p}} {A = A} {B = B} (U1-natiso {p = p}) D

  U∘-func : ∀ {p q r : Mode} {α : p ≥ q} {β : q ≥ r} {A B : Tp r} (D : A [ 1m ]⊢ B) 
                → (Ufunc {α = α ∘1 β} D) ≈ cut {α = 1m} {β = 1m} U∘1 (cut {α = 1m} {β = 1m} (Ufunc {α = α} (Ufunc {α = β} D)) U∘2)
  U∘-func {α = α} {β = β} D = square' (U∘-natiso) D


  ----------------------------------------------------------------------
  -- monads

  □ : ∀ {p q} (α : q ≥ p) → Tp p → Tp p 
  □ α A = F α (U α A)

  ◯ : ∀ {p q} (α : q ≥ p) → Tp q → Tp q 
  ◯ α A = U α (F α A)

  □func : ∀ {p q : Mode} {α : q ≥ p} {A B} → A [ 1m ]⊢ B → □ α A [ 1m ]⊢ □ α B
  □func D = Ffunc (Ufunc D)

  ◯func : ∀ {p q : Mode} {α : q ≥ p} {A B} → A [ 1m ]⊢ B → ◯ α A [ 1m ]⊢ ◯ α B
  ◯func D = Ufunc (Ffunc D)

  □counit : {p q : Mode} {A : Tp p} {α : q ≥ p} → □ α A [ 1m ]⊢ A
  □counit {α = α} = FL {α = α} {β = 1m} (UL 1m 1⇒ hyp)

  □comult : {p q : Mode} {A : Tp p} {α : q ≥ p} → □ α A [ 1m ]⊢ □ α (□ α A)
  □comult {α = α} = FL {α = α} {β = 1m} (FR 1m 1⇒ (UR (FR 1m 1⇒ hyp))) 

  ◯unit : {p q : Mode} {A : Tp q} {α : q ≥ p} → A [ 1m ]⊢ ◯ α A
  ◯unit {α = α} = UR (FR 1m 1⇒ hyp)

  ◯mult : {p q : Mode} {A : Tp q} {α : q ≥ p} → ◯ α (◯ α A) [ 1m ]⊢ ◯ α A
  ◯mult {α = α} = UR {α = α} {β = 1m} (UL 1m 1⇒ (FL (UL 1m 1⇒ hyp))) 

  ◯unit-nat : {p q : Mode} {A A' : Tp q} {α : q ≥ p} (D : A [ 1m ]⊢ A')
             → cut D (◯unit {α = α}) ≈ cut ◯unit (◯func D)
  ◯unit-nat D = UR≈ (((eq (! (transport⊢1 _)) ∘≈ eq (! (transport⊢1 _)) ∘≈ !≈ (cut-ident-left (FR 1m 1⇒ D))) ∘≈ FR≈ (cut-ident-right D)) ∘≈ eq (cutFR D)) ∘≈ eq (cutUR D)

  ◯mult-nat : {p q : Mode} {A A' : Tp q} {α : q ≥ p} (D : A [ 1m ]⊢ A') 
            → cut (◯mult {α = α}) (◯func D) ≈ cut (◯func (◯func D)) ◯mult 
  ◯mult-nat D = UR≈ (UL≈ (FL≈ (UL≈ (FL≈ (transport⊢≈ 1⇒ ((eq (! (cutFR D)) ∘≈ FR≈ (!≈ (cut-ident-right _))) ∘≈ cut-ident-left _))))))

  ◯assoc : ∀ {p q : Mode} {A : Tp q} {α : q ≥ p} 
          -> (cut {A = ◯ α (◯ α (◯ α A))} {C = ◯ α A} (◯func ◯mult) ◯mult) ≈ (cut ◯mult ◯mult)
  ◯assoc = id

  ◯unit1 : ∀ {p q : Mode} {A : Tp q} {α : q ≥ p} 
              -> (cut {A = ◯ α A} {C = ◯ α A}◯unit ◯mult) ≈ hyp
  ◯unit1 {α = α} = UR≈ {α = α} {β = 1m} (UL≈ {γ = 1m} {e = 1⇒} (FL≈ (cut-ident-left _ ∘≈ eq (transport⊢1 _))))

  ◯unit2 : ∀ {p q : Mode} {A : Tp q} {α : q ≥ p} 
              -> (cut {A = ◯ α A} {C = ◯ α A} (◯func ◯unit) ◯mult) ≈ hyp
  ◯unit2 {α = α} = UR≈ {α = α} {β = 1m} (UL≈ {γ = 1m} {e = 1⇒} (FL≈ (cut-ident-left _ ∘≈ eq (transport⊢1 _ ∘ (transport⊢1 _ ∘ transport⊢1 _)))))

  □counit-nat : {p q : Mode} {A A' : Tp p} {α : q ≥ p} (D : A [ 1m ]⊢ A') 
              → cut (□counit {α = α}) D ≈ cut (□func D) □counit
  □counit-nat D = (FL≈ (!≈ (eq (transport⊢1 _)) ∘≈ !≈ (eq (transport⊢1 _)) ∘≈ !≈ (cut-ident-right (UL 1m 1⇒ D)) ∘≈ UL≈ (cut-ident-left D)) ∘≈ FL≈ (cutUL D)) ∘≈ cutFL D

  □comult-nat : {p q : Mode} {A A' : Tp p} {α : q ≥ p} (D : A [ 1m ]⊢ A')
              → cut (□func D) (□comult {α = α}) ≈ cut □comult (□func (□func D))
  □comult-nat D = FL≈ (FR≈ (UR≈ (FR≈ (UR≈ (transport⊢≈ 1⇒ ((!≈ (cutUL D) ∘≈ UL≈ (!≈ (cut-ident-left _) ∘≈ cut-ident-right _)) ∘≈ cutUL hyp))))))
  
  □assoc : ∀ {p q : Mode} {A : Tp p} {α : q ≥ p} 
          -> (cut {A = □ α A} {C = □ α (□ α (□ α A)) } □comult (□func □comult)) ≈ (cut □comult □comult)
  □assoc = id

  □unit1 : ∀ {p q : Mode} {A : Tp p} {α : q ≥ p} 
          -> (cut {A = □ α A} {C = □ α A} □comult □counit) ≈ hyp
  □unit1 {α = α} = FL≈ (FR≈ {γ = 1m} {e = 1⇒} (UR≈ (cut-ident-right _ ∘≈ eq (transport⊢1 _))))

  □unit2 : ∀ {p q : Mode} {A : Tp p} {α : q ≥ p} 
          -> (cut {A = □ α A} {C = □ α A} □comult (□func □counit)) ≈ hyp
  □unit2 {α = α} = FL≈ (FR≈ {γ = 1m} {e = 1⇒} (UR≈ (((cut-ident-right _ ∘≈ eq (transport⊢1 _)) ∘≈ eq (transport⊢1 _)) ∘≈ eq (transport⊢1 _))))


  


  {- these should not be provable

  -- need β such that 1m ⇒ α ∘1 β 
  badcounit : {p q : Mode} {A : Tp q} {α : q ≥ p} → ◯ α A [ 1m ]⊢ A
  badcounit = UL {!!} {!NO!} (FL {!!}) 

  -- need β such that 
  badunit : {p q : Mode} {A : Tp p} {α : q ≥ p} → A [ 1m ]⊢ □ α A
  badunit = FR {!!} {!NO!} (UR {!!})

  -}

  -- ----------------------------------------------------------------------
  -- 2-cells induce morphisms of adjunctions (conjugate pairs of functors)
  -- F is contravariant; U is covariant

  F2 : ∀ {p q} {A : Tp q} {α β : q ≥ p} → β ⇒ α → F α A [ 1m ]⊢ F β A
  F2 {α = α} e = FL {α = α} {β = 1m} (FR 1m e hyp)

  F2-natural : ∀ {p q : Mode} {α β : p ≥ q} {A B : Tp p} (e : α ⇒ β) (D : A [ 1m ]⊢ B) →
                     cut {α = 1m} (F2 e) (Ffunc {α = α} D) ≈ (cut {β = 1m} (Ffunc {α = β} D) (F2 e))
  F2-natural {β = β} e D = FL≈ {α = β} {β = 1m ∘1 1m} (!≈ (eq (transport⊢1 _)) ∘≈ (!≈ (eq (cutFR D)) ∘≈ (!≈ (FR≈ {γ = 1m} {e = e} (cut-ident-right D)) ∘≈ transport⊢≈ e (cut-ident-left (FR 1m 1⇒ D)))))

  F21 : ∀ {p q} {A : Tp q} {α : q ≥ p} → F2 {A = A} (1⇒ {α = α}) ≈ hyp 
  F21 = id

  F2· : ∀ {p q} {A : Tp q} {α β γ : q ≥ p} {e1 : β ⇒ α} {e2 : γ ⇒ β} → F2 {A = A} (e2 ·2 e1) ≈ cut (F2 {A = A} e1) (F2 {A = A} e2)
  F2· = FL≈ (!≈ (transport⊢≈ _ (cut-ident-left _)))

  U2 : ∀ {p q} {A : Tp p} {α β : q ≥ p} → α ⇒ β → U α A [ 1m ]⊢ U β A
  U2 {α = α} {β = β} e = UR {α = β} {β = 1m} (UL 1m e hyp)

  U2-natural : ∀ {p q : Mode} {α β : p ≥ q} {A B : Tp q} (e : α ⇒ β) (D : A [ 1m ]⊢ B) →
                     cut {α = 1m} (U2 e) (Ufunc {α = β} D) ≈ (cut {β = 1m} (Ufunc {α = α} D) (U2 e))
  U2-natural {α = α} {β = β} e D = UR≈ {α = β} {β = 1m ∘1 1m} ((((!≈ (transport⊢≈ e (cut-ident-right (UL 1m 1⇒ D)))) ∘≈ UL≈ {γ = 1m}{e = e} (cut-ident-left D)) ∘≈ cutUL D) ∘≈ eq (transport⊢1 _))

  U21 : ∀ {p q} {A : Tp p} {α : q ≥ p} → U2 {A = A} (1⇒ {α = α}) ≈ hyp 
  U21 = id

  U2· : ∀ {p q} {A : Tp p} {α β γ : q ≥ p} {e1 : β ⇒ α} {e2 : γ ⇒ β} → U2 {A = A} (e2 ·2 e1) ≈ cut (U2 {A = A} e2) (U2 {A = A} e1)
  U2· {α = α} {e1 = e1} {e2} = UR≈ {α = α} {β = 1m} (!≈ (transport⊢≈ e1 (cut-ident-right (UL 1m e2 hyp))))

  F2U2conjugate : ∀ {p q} {A : Tp q} {α β : q ≥ p} {e : β ⇒ α}
            → cut (UFadjunction1 (ident (F _ A))) (Ufunc (F2 e))
            ≈ cut (UFadjunction1 hyp) (U2 e)
  F2U2conjugate {A = A} {α = α} {β = β} {e} = 
    UR≈ {α = α} {β = 1m} (((!≈ (transport⊢≈ e (cut≈1 (cut-ident-left _ ∘≈ eq (transport⊢1 _)) (FL {α = β} {β = 1m} (FR 1m 1⇒ (ident A)))))
                            ∘≈ !≈ (transport⊢≈ e (cut-ident-left (FR 1m 1⇒ (ident A)) ∘≈ eq (transport⊢1 (cut (ident A) (FR 1m 1⇒ (ident A)))))) )
                            ∘≈ cut-ident-left (FR 1m e (ident A)) ∘≈ eq (transport⊢1 (cut (ident A) (FR 1m e (ident A)))))
                            ∘≈ cut≈1 (cut-ident-left (FR 1m 1⇒ (ident A)) 
                            ∘≈ eq (transport⊢1 _)) (FL {α = α} {β = 1m} (FR 1m e (ident A))) ∘≈ eq (transport⊢1 _))

  -- ----------------------------------------------------------------------
  -- F preserves coproducts

  Fpres-coprod1 : ∀ {p q} {α : p ≥ q} {A B} → F α (A ⊕ B) [ 1m ]⊢ (F α A ⊕ F α B)
  Fpres-coprod1 {α = α} = FL {α = α} {β = 1m} (Case (Inl (FR 1m 1⇒ hyp)) (Inr (FR 1m 1⇒ hyp)))

  Fpres-coprod2 : ∀ {p q} {α : p ≥ q} {A B} → (F α A ⊕ F α B) [ 1m ]⊢ (F α (A ⊕ B))
  Fpres-coprod2 = Case (FL (FR 1m 1⇒ (Inl hyp))) (FL (FR 1m 1⇒ (Inr hyp)))

  Fpres-coprod-composite-1 : ∀ {p q} {α : p ≥ q} {A B} 
                           → cut (Fpres-coprod2 {α = α}{A}{B}) Fpres-coprod1 ≈ hyp
  Fpres-coprod-composite-1 = Case≈ (!≈ (Fη _) ∘≈ FL≈ (Inl≈ (!≈ (cut-ident-left _ ∘≈ eq (transport⊢1 _))) ∘≈ (cut-ident-left _ ∘≈ eq (transport⊢1 _)))) (!≈ (Fη _) ∘≈ FL≈ (Inr≈ (!≈ (cut-ident-left _ ∘≈ eq (transport⊢1 _))) ∘≈ (cut-ident-left _ ∘≈ eq (transport⊢1 _))))

  Fpres-coprod-composite-2 : ∀ {p q} {α : p ≥ q} {A B} 
                           → cut (Fpres-coprod1 {α = α}{A}{B}) Fpres-coprod2 ≈ hyp
  Fpres-coprod-composite-2 {α = α} = FL≈ {α = α} {β = 1m ∘1 1m} (!≈ (⊕η _) ∘≈ Case≈ (!≈ (FR≈ {γ = 1m} {e = 1⇒} (cut-ident-left _)) ∘≈ (cut-ident-left _ ∘≈ eq (transport⊢1 _))) (!≈ (FR≈ {γ = 1m} {e = 1⇒} (cut-ident-left _)) ∘≈ (cut-ident-left _ ∘≈ eq (transport⊢1 _))))

  Fpres-coprod : ∀ {p q} {α : p ≥ q} {A B} → Iso (F α (A ⊕ B)) (F α A ⊕ F α B)
  Fpres-coprod = iso Fpres-coprod1 Fpres-coprod2 Fpres-coprod-composite-2 Fpres-coprod-composite-1


  -- ----------------------------------------------------------------------
  -- pseudofunctor from M into Adj

  F2-nattrans : ∀ {p q} {α β : q ≥ p} (e : α ⇒ β) → NatTrans (Ffunctor β) (Ffunctor α)
  F2-nattrans e = nat (F2 e) (F2-natural e)

  U2-nattrans : ∀ {p q} {α β : q ≥ p} (e : α ⇒ β) → NatTrans (Ufunctor α) (Ufunctor β)
  U2-nattrans e = nat (U2 e) (U2-natural e)

  -- (0) each object of M determines a category:
  --     objects of p are A : Tp p
  --     morphisms are D : A [ 1m ]⊢ B mod ≈ 
  --               id and comp are ident and cut, which are associative and unital up to ≈

  -- (1) functor from each hom category q ≥ p to category of Adjunction q p and AdjMor's 
  
  P1-ob : ∀ {p q} → q ≥ p → Adjunction q p
  P1-ob α = adj (Ffunctor α) (Ufunctor α) UFadjunction1 UFadjunction2 (λ q → UR≈ {α = α} {β = 1m} (cut≈2 (FR 1m 1⇒ hyp) q)) (λ q → FL≈ {α = α} {β = 1m} (cut≈1 q (UL 1m 1⇒ hyp))) UFadj-composite2 UFadj-composite1 UFadjunction-nat1 UFadjunction-nat2
  
  P1-mor : ∀ {p q} {α β : q ≥ p} (e : α ⇒ β) → 
                      AdjMor (P1-ob β) (P1-ob α)
  P1-mor e = adjmor (F2-nattrans e) (U2-nattrans e) F2U2conjugate

  P1-mor-1 : ∀ {p q} {α : q ≥ p}
         → P1-mor (1⇒{_}{_}{α}) ==AdjMor 1AdjMor
  P1-mor-1 = eqadjmor F21 U21

  P1-mor-· : ∀ {p q} {α β γ : q ≥ p} (e1 : α ⇒ β) (e2 : β ⇒ γ)
       → (P1-mor (e1 ·2 e2)) ==AdjMor ((P1-mor e2) ·AdjMor (P1-mor e1))
  P1-mor-· e1 e2 = eqadjmor F2· U2·

  -- (2) for each p, a 2-cell isomorphism between P1-ob(1m:p≥p) and the identity 1-cell on P0(p)
  --     i.e. P1 preserves 1 up to isomorphism
  --     in this case, the identity 1-cell is the 1 -| 1 adjunction

  P1-ob-1 : ∀ {p} → AdjIso (P1-ob 1m) (1Adj {p}) 
  P1-ob-1 = adjiso F1-natiso (!natiso U1-natiso) FU1-conjugate

  -- (3) for composable α and β, a 2-cell isomorphism between P1-ob(α ∘1 β) and the composite of P1-ob(α) and P1-ob(β) 

  P1-ob-∘ : ∀ {p q r} {α : r ≥ q} {β : q ≥ p} → AdjIso (P1-ob (α ∘1 β)) (P1-ob α ·Adj P1-ob β)
  P1-ob-∘ = adjiso F∘-natiso (!natiso U∘-natiso) FU∘-conjugate

  P1-ob-∘-nat : ∀ {p q r} {α α' : r ≥ q} {β β' : q ≥ p} (e1 : α ⇒ α') (e2 : β ⇒ β')
              → (P1-mor (e1 ∘1cong e2) ·AdjMor AdjIso-forward (P1-ob-∘ {α = α} {β = β})) ==AdjMor (AdjIso-forward (P1-ob-∘ {α = α'} {β = β'}) ·AdjMor (P1-mor e1 ·Adj-cong P1-mor e2))
  P1-ob-∘-nat {α = α}{α'}{β}{β'} e1 e2 = 
    eqadjmor (FL≈ {α = α' ∘1 β'} {β = 1m} (!≈ (FR2 {α = β} {β = α' ∘1 β'} {γ = α'} {γ' = α} {e = _} {e' = e1 ∘1cong e2} {D = cut (FR 1m 1⇒ hyp) (cut (FL {α = α'} {β = 1m} (FR 1m e1 hyp)) hyp)} {D' = FR 1m 1⇒ hyp} e1 (! (interchange {e1 = e1} {e2 = 1⇒} {f1 = 1⇒} {f2 = e2})) ((( transport⊢≈ e1 (cut-ident-left (FR 1m 1⇒ hyp))) ∘≈ cut-ident-left _) ∘≈ eq (transport⊢1 _))) ∘≈ transport⊢≈ _ (cut-ident-left (FR α 1⇒ (FR 1m 1⇒ hyp)))))
             (UR≈ {α = α' ∘1 β'} {β = 1m} (!≈ (cut-ident-right (UL β' (e1 ∘1cong 1⇒) (transport⊢ 1⇒ (cut (UL 1m e2 hyp) hyp))) ∘≈ eq (transport⊢1 _) ∘≈ eq (transport⊢1 _)) ∘≈ !≈ (UL2 {e = e1 ∘1cong 1⇒} {e' = 1⇒ ·2 (e1 ∘1cong e2)} {D = transport⊢ 1⇒ (cut (UL 1m e2 hyp) hyp)} {D' = UL 1m 1⇒ hyp} e2 (! (interchange {e1 = 1⇒} {e2 = e1} {f1 = e2} {f2 = 1⇒})) (cut-ident-right (UL 1m e2 hyp) ∘≈ eq (transport⊢1 _))) ∘≈ transport⊢≈ (e1 ∘1cong e2) (cut-ident-right (UL β 1⇒ (UL 1m 1⇒ hyp))) ))
