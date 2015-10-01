
open import adjointlogic.Lib
open import adjointlogic.Rules
open import adjointlogic.Properties

module adjointlogic.General where

  -- a bunch of category theory definitions specialized to the categories used here

  record Iso {p : Mode} (A B : Tp p) : Set where
    constructor iso
    field
      f : A [ 1m ]⊢ B
      g : B [ 1m ]⊢ A
      α : cut f g ≈ hyp
      β : cut g f ≈ hyp

  1i : ∀ {p : Mode} {A : Tp p} → Iso A A
  1i = iso hyp hyp (cut-ident-left hyp) (cut-ident-left hyp) 

  _·i_ : {p : Mode} {A B C : Tp p} → Iso A B → Iso B C → Iso A C
  iso f g α β ·i iso f' g' α' β' = 
      iso (cut f f') (cut g' g) 
             ((((α ∘≈ cut≈2 f (cut-ident-left g)) ∘≈ cut≈2 f (cut≈1  α' g)) ∘≈ cut≈2 f (cut-assoc f' g' g)) ∘≈ !≈ (cut-assoc f f' (cut g' g))) 
             ((((β' ∘≈ cut≈2 g' (cut-ident-left f')) ∘≈ cut≈2 g' (cut≈1 β f')) ∘≈ cut≈2 g' (cut-assoc g f f')) ∘≈ !≈ (cut-assoc g' g (cut f f'))) 

  !i : {p : Mode} {A B : Tp p} → Iso A B → Iso B A
  !i (iso f g α β) = iso g f β α

  record Functor (p q : Mode) : Set where 
    constructor func
    field
     ob : Tp p -> Tp q  
     ar : ∀ {A B : Tp p} → A [ 1m ]⊢ B → ob A [ 1m ]⊢ ob B
     ar≈ : ∀ {A B : Tp p} {D1 D2 : A [ 1m ]⊢ B} → D1 ≈ D2 → ar D1 ≈ ar D2
     presid  : ∀ {A : Tp p} → ar (ident A) ≈ ident (ob A)
     prescut : ∀ {A B C : Tp p} (D1 : A [ 1m ]⊢ B) (D2 : B [ 1m ]⊢ C)
             → ar (cut D1 D2) ≈ cut (ar D1) (ar D2)
    ar-iso : ∀ {A B : Tp p} → Iso A B → Iso (ob A) (ob B)
    ar-iso i = iso (ar (Iso.f i)) (ar (Iso.g i)) ((presid ∘≈ ar≈ (Iso.α i)) ∘≈ !≈ (prescut _ _)) ((presid ∘≈ ar≈ (Iso.β i)) ∘≈ !≈ (prescut _ _))

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

  _∘Func-cong_ : ∀ {p q r} {G G' : Functor p q} {H H' :  Functor q r}
                → NatTrans H H'
                → NatTrans G G'
                → NatTrans (H ∘Func G) (H' ∘Func G')
  _∘Func-cong_ {G = G} {G'} {H} {H'} nh ng = nat (cut (Functor.ar H (NatTrans.mor ng)) (NatTrans.mor nh)) (λ D → !≈ (cut-assoc (Functor.ar H (Functor.ar G D)) (Functor.ar H (NatTrans.mor ng)) (NatTrans.mor nh)) ∘≈ cut≈1 (Functor.prescut H (Functor.ar G D) (NatTrans.mor ng) ∘≈ Functor.ar≈ H (NatTrans.square ng D)) (NatTrans.mor nh) ∘≈ (cut≈1 (!≈ (Functor.prescut H (NatTrans.mor ng) (Functor.ar G' D))) (NatTrans.mor nh) ∘≈ cut-assoc (Functor.ar H (NatTrans.mor ng)) (Functor.ar H (Functor.ar G' D)) (NatTrans.mor nh)) ∘≈ cut≈2 (Functor.ar H (NatTrans.mor ng)) (NatTrans.square nh (Functor.ar G' D)) ∘≈ !≈ (cut-assoc (Functor.ar H (NatTrans.mor ng)) (NatTrans.mor nh) (Functor.ar (H' ∘Func G') D)))

  -- it's a theorem that a natural isomorphism is the same as an isomorphism of natural transformations
  record NatIso {p q : Mode} (G1 G2 : Functor p q) : Set where
    constructor natiso
    field
      mor    : {A : Tp p} → Iso (Functor.ob G1 A) (Functor.ob G2 A) 
      square : {A B : Tp p} (D : A [ 1m ]⊢ B)
             → cut (Iso.f (mor {A})) (Functor.ar G2 D) ≈ cut (Functor.ar G1 D) (Iso.f (mor {B}))

  
  square' : {p q : Mode} {G1 G2 : Functor p q} {A B : Tp p} 
          → (i : NatIso G1 G2) (D : A [ 1m ]⊢ B)
          → (Functor.ar G1 D) ≈ cut (Iso.f (NatIso.mor i {A})) (cut (Functor.ar G2 D) (Iso.g (NatIso.mor i {B})))
  square' {G1 = G1} {G2 = G2} i D = !≈ (cut-assoc (Iso.f (NatIso.mor i)) (Functor.ar G2 D) (Iso.g (NatIso.mor i))) ∘≈ !≈ (cut≈1 (NatIso.square i D) (Iso.g (NatIso.mor i))) ∘≈ !≈ ((cut-ident-right (Functor.ar G1 D) ∘≈ cut≈2 (Functor.ar G1 D) (Iso.α (NatIso.mor i))) ∘≈ !≈ (cut-assoc (Functor.ar G1 D) (Iso.f (NatIso.mor i)) (Iso.g (NatIso.mor i))))

  flipsquare : {p q : Mode} (G1 G2 : Functor p q) (i : {A : Tp p} → Iso (Functor.ob G1 A) (Functor.ob G2 A) ) →
               (∀ {A B} (D : A [ 1m ]⊢ B) → cut (Iso.f (i {A})) (Functor.ar G2 D) ≈ cut (Functor.ar G1 D) (Iso.f (i {B}))) 
             → (∀ {A B} (D : A [ 1m ]⊢ B) → cut (Iso.g i) (Functor.ar G1 D) ≈ cut (Functor.ar G2 D) (Iso.g i))
  flipsquare G1 G2 i sq1 D = 
    cut≈1 ((cut-ident-left (Functor.ar G2 D) ∘≈ cut≈1 (Iso.β (i)) (Functor.ar G2 D)) ∘≈ cut-assoc (Iso.g (i)) (Iso.f (i)) (Functor.ar G2 D)) (Iso.g (i)) ∘≈ !≈ (cut≈1 (cut≈2 (Iso.g (i)) (sq1 D)) (Iso.g (i))) ∘≈ !≈ (cut≈2 (Iso.g (i)) ((cut-ident-right (Functor.ar G1 D) ∘≈ cut≈2 (Functor.ar G1 D) (Iso.α (i))) ∘≈ !≈ (cut-assoc (Functor.ar G1 D) (Iso.f (i)) (Iso.g (i)))) ∘≈ !≈ (cut-assoc (Iso.g (i)) (cut (Functor.ar G1 D) (Iso.f (i))) (Iso.g (i))))

  1NatIso : {p q : Mode} (G : Functor p q) → NatIso G G
  1NatIso G = natiso 1i (NatTrans.square (1NatTrans { G = G }))

  !natiso : {p q : Mode} {G1 G2 : Functor p q} → NatIso G1 G2 → NatIso G2 G1
  !natiso {G1 = G1} {G2 = G2} i = natiso (!i (NatIso.mor i)) (flipsquare G1 G2 (NatIso.mor i) (NatIso.square i))

  NatIso-forward : ∀ {p q : Mode} {G1 G2 : Functor p q} → NatIso G1 G2 → NatTrans G1 G2
  NatIso-forward i = nat (Iso.f (NatIso.mor i)) (NatIso.square i)

  _·NatIso_ : ∀ {p q : Mode} {G1 G2 G3 : Functor p q} → NatIso G1 G2 → NatIso G2 G3 → NatIso G1 G3
  _·NatIso_ {G1 = G1}{G2}{G3} n1 n2 = natiso (NatIso.mor n1 ·i NatIso.mor n2) (NatTrans.square (NatIso-forward n1 ·NatTrans NatIso-forward n2))

  _∘Func-cong-iso_ : ∀ {p q r} {G G' : Functor p q} {H H' :  Functor q r}
                → NatIso H H'
                → NatIso G G'
                → NatIso (H ∘Func G) (H' ∘Func G')
  _∘Func-cong-iso_ {G = G} {G'} {H} {H'} nh ng = natiso (Functor.ar-iso H (NatIso.mor ng) ·i (NatIso.mor nh)) (NatTrans.square (NatIso-forward nh ∘Func-cong NatIso-forward ng))

  ∘Func-unit-r-natiso : ∀ {p q} {G : Functor p q} → NatIso G (G ∘Func 1Func)
  ∘Func-unit-r-natiso = (natiso (iso hyp hyp (cut-ident-left _) (cut-ident-left _)) (λ D → !≈ (cut-ident-right _) ∘≈ cut-ident-left _))

  ∘Func-unit-l-natiso : ∀ {p q} {G : Functor p q} → NatIso (1Func ∘Func G) G
  ∘Func-unit-l-natiso = (natiso (iso hyp hyp (cut-ident-left _) (cut-ident-left _)) (λ D → !≈ (cut-ident-right _) ∘≈ cut-ident-left _))

  ∘Func-assoc-natiso : ∀ {p q r s : Mode} (G1 : Functor p q) (G2 : Functor q r) (G3 : Functor r s) 
                     → NatIso ((G3 ∘Func G2) ∘Func G1) (G3 ∘Func (G2 ∘Func G1))
  ∘Func-assoc-natiso G1 G2 G3 = (natiso (iso hyp hyp (cut-ident-left _) (cut-ident-left _)) (λ D → !≈ (cut-ident-right _) ∘≈ cut-ident-left _))

  record FullAndFaithfull {p q : Mode} (G : Functor p q) : Set where
    constructor ff 
    field
      back : ∀ {A B} → Functor.ob G A [ 1m ]⊢ Functor.ob G B → A [ 1m ]⊢ B
      composite1 : ∀ {A B} → (D : A [ 1m ]⊢ B) → back (Functor.ar G D) ≈ D
      composite2 : ∀ {A B} → (D : Functor.ob G A [ 1m ]⊢ Functor.ob G B) → (Functor.ar G (back D)) ≈ D

  retraction-ff : {p q : Mode} {G : Functor p q}
                → (H : Functor q p) (i : NatIso (H ∘Func G) 1Func)
                → (∀ {A B} (D : Functor.ob G A [ 1m ]⊢ Functor.ob G B) →
                     cut (Functor.ar G (Functor.ar H D)) (Functor.ar G (Iso.f (NatIso.mor i)))
                     ≈ cut (Functor.ar G (Iso.f (NatIso.mor i))) D)
                → FullAndFaithfull G
  retraction-ff {G = G} H i s = ff (λ D → cut (Iso.g (NatIso.mor i)) (cut (Functor.ar H D) (Iso.f (NatIso.mor i)))) 
                                   (λ D → ((cut-ident-left D ∘≈ cut≈1 (Iso.β (NatIso.mor i)) D) ∘≈ cut-assoc (Iso.g (NatIso.mor i)) (Iso.f (NatIso.mor i)) (Functor.ar 1Func D)) ∘≈ !≈ (cut≈2 (Iso.g (NatIso.mor i)) (NatIso.square i D))) 
                                   (λ D → ((((cut-ident-left D ∘≈ cut≈1 (Functor.presid G ∘≈ Functor.ar≈ G (Iso.β (NatIso.mor i)) ∘≈ !≈ (Functor.prescut G (Iso.g (NatIso.mor i)) (Iso.f (NatIso.mor i)))) D) ∘≈ cut-assoc (Functor.ar G (Iso.g (NatIso.mor i))) (Functor.ar G (Iso.f (NatIso.mor i))) D) ∘≈ cut≈2 (Functor.ar G (Iso.g (NatIso.mor i))) (s D)) ∘≈ cut≈2 (Functor.ar G (Iso.g (NatIso.mor i))) (Functor.prescut G (Functor.ar H D) (Iso.f (NatIso.mor i)))) ∘≈ Functor.prescut G (Iso.g (NatIso.mor i)) (cut (Functor.ar H D) (Iso.f (NatIso.mor i))))


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
    RtoLnat D1 D D2 = LtoRtoL _ ∘≈ RtoL≈ goal1 ∘≈ !≈ (LtoRtoL _) where 
      goal1 : LtoR (RtoL (cut D1 (cut D (Functor.ar R D2)))) ≈ LtoR (cut (Functor.ar L D1) (cut (RtoL D) D2))
      goal1 = (!≈ (LtoRnat D1 (RtoL D) D2) ∘≈ cut≈2 D1 (cut≈1 (!≈ (RtoLtoR D)) (Functor.ar R D2))) ∘≈ RtoLtoR _

  1Adj : ∀ {p} → Adjunction p p
  1Adj = adj 1Func 1Func (λ D → D) (λ D → D) (\ q -> q) (\ q -> q) (λ _ → id) (λ _ → id) (λ _ _ _ → id) 

  _·Adj_ : ∀ {p q r} → Adjunction p q → Adjunction q r → Adjunction p r 
  _·Adj_ a1 a2 = adj (Adjunction.L a2 ∘Func Adjunction.L a1) (Adjunction.R a1 ∘Func Adjunction.R a2)
                   (λ D → Adjunction.LtoR a1 (Adjunction.LtoR a2 D)) 
                   (λ D → Adjunction.RtoL a2 (Adjunction.RtoL a1 D))
                   (λ q → Adjunction.LtoR≈ a1 (Adjunction.LtoR≈ a2 q)) 
                   (λ q → Adjunction.RtoL≈ a2 (Adjunction.RtoL≈ a1 q))
                   (λ D → Adjunction.LtoRtoL a2 D ∘≈ Adjunction.RtoL≈ a2 (Adjunction.LtoRtoL a1 _))
                   (λ D → Adjunction.RtoLtoR a1 D ∘≈ Adjunction.LtoR≈ a1 (Adjunction.RtoLtoR a2 _))
                   (λ D1 D D2 → (Adjunction.LtoRnat a1 D1 (Adjunction.LtoR a2 D) (Functor.ar (Adjunction.R a2) D2)) ∘≈ Adjunction.LtoR≈ a1 (Adjunction.LtoRnat a2 (Functor.ar (Adjunction.L a1) D1) D D2)) 

  record AdjMor {p q : Mode} (a1 : Adjunction p q) (a2 : Adjunction p q) : Set where
    constructor adjmor
    field
      LL        : NatTrans (Adjunction.L a1) (Adjunction.L a2)
      RR        : NatTrans (Adjunction.R a2) (Adjunction.R a1)
      conjugate : ∀ {A B} {D : Functor.ob (Adjunction.L a2) A [ 1m ]⊢ B}
                → Adjunction.LtoR a1 (cut (NatTrans.mor LL) D) ≈ cut (Adjunction.LtoR a2 D) (NatTrans.mor RR)

  record _==AdjMor_ {p q : Mode} {a1 : Adjunction p q} {a2 : Adjunction p q} (mor1 : AdjMor a1 a2) (mor2 : AdjMor a1 a2) : Set where
    constructor eqadjmor
    field 
      eq1 : ∀ {A} → NatTrans.mor (AdjMor.LL mor1) {A = A} ≈ NatTrans.mor (AdjMor.LL mor2)
      eq2 : ∀ {A} → NatTrans.mor (AdjMor.RR mor1) {A = A} ≈ NatTrans.mor (AdjMor.RR mor2)

  1AdjMor : {p q : Mode} {a : Adjunction p q}
          → AdjMor a a 
  1AdjMor {a = a} = adjmor 1NatTrans 1NatTrans (!≈ (cut-ident-right _) ∘≈ Adjunction.LtoR≈ a (cut-ident-left _)) 

  _·AdjMor_ : {p q : Mode} {a1 : Adjunction p q} {a2 : Adjunction p q} {a3 : Adjunction p q}
          → AdjMor a1 a2
          → AdjMor a2 a3
          → AdjMor a1 a3
  _·AdjMor_ {a1 = a1}{a2}{a3} mor1 mor2 = 
    adjmor (AdjMor.LL mor1 ·NatTrans AdjMor.LL mor2)
           (AdjMor.RR mor2 ·NatTrans AdjMor.RR mor1) 
           (λ {A} {B} {D} → ((!≈ (cut-assoc (Adjunction.LtoR a3 D) (NatTrans.mor (AdjMor.RR mor2)) (NatTrans.mor (AdjMor.RR mor1))) ∘≈ cut≈1 (AdjMor.conjugate mor2) (NatTrans.mor (AdjMor.RR mor1))) ∘≈ AdjMor.conjugate mor1) ∘≈ Adjunction.LtoR≈ a1 (!≈ (cut-assoc (NatTrans.mor (AdjMor.LL mor1)) (NatTrans.mor (AdjMor.LL mor2)) D)))

  _·Adj-cong_ : ∀ {p q r} {a1 a1' : Adjunction p q} {a2 a2' :  Adjunction q r}
                → AdjMor a1 a1'
                → AdjMor a2 a2'
                → AdjMor (a1 ·Adj a2) (a1' ·Adj a2')
  _·Adj-cong_ {a1 = a1}{a1'}{a2}{a2'} mor1 mor2 = 
    adjmor (AdjMor.LL mor2 ∘Func-cong AdjMor.LL mor1) 
           (AdjMor.RR mor1 ∘Func-cong AdjMor.RR mor2) 
           (λ {A}{B}{D} → (((((!≈ (cut-assoc (Adjunction.LtoR a1' (Adjunction.LtoR a2' D)) (Functor.ar (Adjunction.R a1') (NatTrans.mor (AdjMor.RR mor2))) (NatTrans.mor (AdjMor.RR mor1))) ∘≈ cut≈1 (cut-ident-left _ ∘≈ Adjunction.LtoRnat a1' hyp (Adjunction.LtoR a2' D) (NatTrans.mor (AdjMor.RR mor2)) ∘≈ Adjunction.LtoR≈ a1' (!≈ (cut-ident-left _ ∘≈ cut≈1 (Functor.presid (Adjunction.L a1')) (cut (Adjunction.LtoR a2' D) (NatTrans.mor (AdjMor.RR mor2)))) ∘≈ cut≈2 (Adjunction.LtoR a2' D) (cut-ident-left _ ∘≈ cut≈1 (Functor.presid (Adjunction.R a2')) (NatTrans.mor (AdjMor.RR mor2)))) ∘≈ !≈ (Adjunction.LtoR≈ a1' (cut-assoc (Adjunction.LtoR a2' D) (Functor.ar (Adjunction.R a2') hyp) (NatTrans.mor (AdjMor.RR mor2))))) (NatTrans.mor (AdjMor.RR mor1))) ∘≈ AdjMor.conjugate mor1) ∘≈ !≈ (Adjunction.LtoR≈ a1 (cut-assoc (NatTrans.mor (AdjMor.LL mor1)) (cut (Adjunction.LtoR a2' D) (Functor.ar (Adjunction.R a2') hyp)) (NatTrans.mor (AdjMor.RR mor2))))) ∘≈ Adjunction.LtoR≈ a1 (cut≈1 (Adjunction.LtoRnat a2' (NatTrans.mor (AdjMor.LL mor1)) D hyp) (NatTrans.mor (AdjMor.RR mor2))) ∘≈ !≈ (Adjunction.LtoR≈ a1 (cut≈1 (Adjunction.LtoR≈ a2' (cut≈2 (Functor.ar (Adjunction.L a2') (NatTrans.mor (AdjMor.LL mor1))) (cut-ident-right D))) (NatTrans.mor (AdjMor.RR mor2))))) ∘≈ Adjunction.LtoR≈ a1 (AdjMor.conjugate mor2)) ∘≈ Adjunction.LtoR≈ a1 (Adjunction.LtoR≈ a2 (!≈ (cut-assoc (NatTrans.mor (AdjMor.LL mor2)) (Functor.ar (Adjunction.L a2') (NatTrans.mor (AdjMor.LL mor1))) D) ∘≈ cut≈1 (!≈ (NatTrans.square (AdjMor.LL mor2) (NatTrans.mor (AdjMor.LL mor1)))) D)))

  record AdjIso {p q : Mode} (a1 : Adjunction p q) (a2 : Adjunction p q) : Set where
    constructor adjiso
    field
      LL        : NatIso (Adjunction.L a1) (Adjunction.L a2)
      RR        : NatIso (Adjunction.R a2) (Adjunction.R a1)
      conjugate : ∀ {A B} {D : Functor.ob (Adjunction.L a2) A [ 1m ]⊢ B}
                → Adjunction.LtoR a1 (cut (Iso.f (NatIso.mor LL)) D) ≈ cut (Adjunction.LtoR a2 D) (Iso.f (NatIso.mor RR))

  AdjIso-forward : {p q : Mode} {a1 : Adjunction p q} {a2 : Adjunction p q}
                → AdjIso a1 a2 → AdjMor a1 a2
  AdjIso-forward i = adjmor (NatIso-forward (AdjIso.LL i)) (NatIso-forward (AdjIso.RR i)) (AdjIso.conjugate i) 

  AdjIso-backward : {p q : Mode} {a1 : Adjunction p q} {a2 : Adjunction p q}
                → AdjIso a1 a2 → AdjMor a2 a1
  AdjIso-backward {a1 = a1}{a2} i = adjmor (NatIso-forward (!natiso (AdjIso.LL i)))
                                           (NatIso-forward (!natiso (AdjIso.RR i))) 
                                           (λ {A}{B}{D} → Adjunction.RtoLtoR a2 _ ∘≈ Adjunction.LtoR≈ a2 goal1) where
    goal1 : ∀ {A}{B}{D : Functor.ob (Adjunction.L a1) A [ 1m ]⊢ B} → 
              (cut (NatTrans.mor (NatIso-forward (!natiso (AdjIso.LL i)))) D) 
            ≈ Adjunction.RtoL a2
                (cut (Adjunction.LtoR a1 D)
                 (NatTrans.mor (NatIso-forward (!natiso (AdjIso.RR i)))))
    goal1 {D = D} = !≈ (Adjunction.RtoL≈ a2 (cut≈1 (AdjIso.conjugate i {D = cut (Iso.g (NatIso.mor (AdjIso.LL i))) D} ∘≈ Adjunction.LtoR≈ a1 (!≈ (cut-assoc (Iso.f (NatIso.mor (AdjIso.LL i))) (Iso.g (NatIso.mor (AdjIso.LL i))) D) ∘≈ cut≈1 (!≈ (Iso.α (NatIso.mor (AdjIso.LL i)))) D ∘≈ !≈ (cut-ident-left D))) (NatTrans.mor (NatIso-forward (!natiso (AdjIso.RR i)))))) ∘≈ !≈ (Adjunction.LtoRtoL a2 _ ∘≈ Adjunction.RtoL≈ a2 ((cut-ident-right (Adjunction.LtoR a2 (cut (Iso.g (NatIso.mor (AdjIso.LL i))) D)) ∘≈ cut≈2 (Adjunction.LtoR a2 (cut (Iso.g (NatIso.mor (AdjIso.LL i))) D)) (Iso.α (NatIso.mor (AdjIso.RR i)))) ∘≈ !≈ (cut-assoc (Adjunction.LtoR a2 (cut (Iso.g (NatIso.mor (AdjIso.LL i))) D)) (Iso.f (NatIso.mor (AdjIso.RR i))) (Iso.g (NatIso.mor (AdjIso.RR i))))))

  -- note: Adj is really be a strict 2-category,
  --       but since we didn't make ≈ proof-irrelevant (or us a quotient)
  --       this isn't true up to Agda propositional equality.
  --       however, rather than fixing this, it's easier to use the weaker bifunctor law below.
  ·Adj-unit-l : ∀ {p q : Mode} (a1 : Adjunction p q)  → AdjIso (1Adj ·Adj a1) a1
  ·Adj-unit-l a1 = adjiso (natiso (iso hyp hyp (cut-ident-left _) (cut-ident-left _)) (λ D → !≈ (cut-ident-right _) ∘≈ cut-ident-left _)) (natiso (iso hyp hyp (cut-ident-left _) (cut-ident-left _)) (λ D → !≈ (cut-ident-right _) ∘≈ cut-ident-left _)) (!≈ (cut-ident-right _) ∘≈ Adjunction.LtoR≈ a1 (cut-ident-left _))

  ·Adj-unit-r : ∀ {p q : Mode} (a1 : Adjunction p q)  → AdjIso a1 (a1 ·Adj 1Adj)
  ·Adj-unit-r a1 = adjiso (natiso (iso hyp hyp (cut-ident-left _) (cut-ident-left _)) (λ D → !≈ (cut-ident-right _) ∘≈ cut-ident-left _)) (natiso (iso hyp hyp (cut-ident-left _) (cut-ident-left _)) (λ D → !≈ (cut-ident-right _) ∘≈ cut-ident-left _)) (!≈ (cut-ident-right _) ∘≈ Adjunction.LtoR≈ a1 (cut-ident-left _))

  ·Adj-assoc : ∀ {p q r s : Mode} (a1 : Adjunction p q) (a2 : Adjunction q r) (a3 : Adjunction r s) 
             → AdjIso ((a1 ·Adj a2) ·Adj a3) (a1 ·Adj (a2 ·Adj a3))
  ·Adj-assoc a1 a2 a3 = adjiso (natiso (iso hyp hyp (cut-ident-left _) (cut-ident-left _)) (λ D → !≈ (cut-ident-right _) ∘≈ cut-ident-left _)) (natiso (iso hyp hyp (cut-ident-left _) (cut-ident-left _)) (λ D → !≈ (cut-ident-right _) ∘≈ cut-ident-left _)) (!≈ (cut-ident-right _) ∘≈ Adjunction.LtoR≈ (a1 ·Adj (a2 ·Adj a3)) (cut-ident-left _))


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
  -- functoriality of type constructors

  ⊕func : ∀ {p : Mode} {A A' B B' : Tp p} → A [ 1m ]⊢ A' → B [ 1m ]⊢ B' → (A ⊕ B) [ 1m ]⊢ (A' ⊕ B')
  ⊕func f f₁ = (Case (cut f (Inl hyp)) (cut f₁ (Inr hyp)))

  -- ENH: check equations

  Ffunc : ∀ {p q : Mode} {α : q ≥ p} {A B} → A [ 1m ]⊢ B → F α A [ 1m ]⊢ F α B
  Ffunc {α = α} D =  FL {α = α} {β = 1m} (FR 1m 1⇒ D)

  Ffunc-ident : ∀ {p q : Mode} {α : q ≥ p} {A} → Ffunc (ident A) ≈ (ident (F α A))
  Ffunc-ident = id

  Ffunc-cut : ∀ {p q : Mode} {α : q ≥ p} {A B C} (D : A [ 1m ]⊢ B) (E : B [ 1m ]⊢ C) → Ffunc {α = α} (cut D E) ≈ cut (Ffunc D) (Ffunc E)
  Ffunc-cut D E = eq (! (ap FL (transport⊢1 _)) ∘ ap FL (! (cutFR D)) )

  Ffunctor : ∀ {p q} (α : q ≥ p) → Functor q p 
  Ffunctor α = func (F α) Ffunc (λ D → FL≈ (FR≈ D)) Ffunc-ident Ffunc-cut

  Ufunc : ∀ {p q : Mode} {α : q ≥ p} {A B} → A [ 1m ]⊢ B → U α A [ 1m ]⊢ U α B
  Ufunc {α = α} D =  UR {α = α} {β = 1m} (UL 1m 1⇒ D)

  Ufunc-ident : ∀ {p q : Mode} {α : q ≥ p} {A} → Ufunc (ident A) ≈ (ident (U α A))
  Ufunc-ident = id

  Ufunc-cut : ∀ {p q : Mode} {α : q ≥ p} {A B C} (D : A [ 1m ]⊢ B) (E : B [ 1m ]⊢ C) → Ufunc {α = α} (cut D E) ≈ cut (Ufunc D) (Ufunc E)
  Ufunc-cut D E = UR≈ (eq (! (transport⊢1 _)) ∘≈ (!≈ (cutUL E)))

  Ufunctor : ∀ {p q} (α : q ≥ p) → Functor p q
  Ufunctor α = func (U α) Ufunc (λ D → UR≈ (UL≈ D)) Ufunc-ident Ufunc-cut

  -- functoriality preserves equivalence
  
  ⊕func-i : ∀ {p : Mode} {A A' B B' : Tp p} → Iso A A' → Iso B B' → Iso (A ⊕ B) (A' ⊕ B')
  ⊕func-i (iso f g α β) (iso f₁ g₁ α₁ β₁) = 
    iso (⊕func f f₁) (⊕func g g₁) 
        (Case≈ ((((cut-ident-left _ ∘≈  cut≈1 α (Inl hyp)) ∘≈ cut-assoc f g (Inl hyp)) ∘≈ (cut≈2 f (cut-ident-left _))) ∘≈ !≈ (cut-assoc f (Inl hyp) (Case (cut g (Inl hyp)) (cut g₁ (Inr hyp))))) ((((cut-ident-left _ ∘≈ cut≈1 α₁ (Inr hyp)) ∘≈ cut-assoc f₁ g₁ (Inr hyp)) ∘≈ cut≈2 f₁ (cut-ident-left _)) ∘≈ !≈ (cut-assoc f₁ (Inr hyp) (Case (cut g (Inl hyp)) (cut g₁ (Inr hyp))))))
        (Case≈ ((((cut-ident-left _ ∘≈ cut≈1 β (Inl hyp)) ∘≈ cut-assoc g f (Inl hyp)) ∘≈ cut≈2 g (cut-ident-left _)) ∘≈ !≈ (cut-assoc g (Inl hyp) (Case (cut f (Inl hyp)) (cut f₁ (Inr hyp))))) ((((cut-ident-left _ ∘≈ cut≈1 β₁ (Inr hyp)) ∘≈ cut-assoc g₁ f₁ (Inr hyp)) ∘≈ cut≈2 g₁ (cut-ident-left _)) ∘≈ !≈ (cut-assoc g₁ (Inr hyp) (Case (cut f (Inl hyp)) (cut f₁ (Inr hyp))))))

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

  Fpres-coprod1-nat : ∀ {p q} {α : p ≥ q} {A B A' B'} 
                    → (D1 : A [ 1m ]⊢ A') (D2 : B [ 1m ]⊢ B')
                    → cut Fpres-coprod1 (⊕func (Ffunc {α = α} D1) (Ffunc D2))
                     ≈ cut (Ffunc (⊕func D1 D2)) Fpres-coprod1 
  Fpres-coprod1-nat D1 D2 = FL≈ (Case≈ ((!≈ (!≈ (cut-assoc D1 (Inl hyp) (Case (Inl (FR 1m 1⇒ hyp)) (Inr (FR 1m 1⇒ hyp)))) ∘≈ eq (transport⊢1 _)) ∘≈ !≈ (cut≈2 D1 (cut-ident-left (Inl (FR 1m 1⇒ hyp)))) ∘≈ !≈ (eq (ap Inl (cutFR D1) ∘ cutInl D1))) ∘≈ Inl≈ (eq (cutFR D1) ∘≈ eq (transport⊢1 _) ∘≈ cut-ident-left _ ∘≈ eq (transport⊢1 _))) ((!≈ (!≈ (cut-assoc D2 (Inr hyp) (Case (Inl (FR 1m 1⇒ hyp)) (Inr (FR 1m 1⇒ hyp)))) ∘≈ eq (transport⊢1 _)) ∘≈ !≈ (cut≈2 D2 (cut-ident-left (Inr (FR 1m 1⇒ hyp)))) ∘≈ !≈ (eq (ap Inr (cutFR D2) ∘ cutInr D2))) ∘≈ Inr≈ (eq (cutFR D2) ∘≈ eq (transport⊢1 _) ∘≈ cut-ident-left _ ∘≈ eq (transport⊢1 _))))

  ----------------------------------------------------------------------
  -- monads

  □ : ∀ {p q} (α : q ≥ p) → Tp p → Tp p 
  □ α A = F α (U α A)

  ◯ : ∀ {p q} (α : q ≥ p) → Tp q → Tp q 
  ◯ α A = U α (F α A)

  □func : ∀ {p q : Mode} {α : q ≥ p} {A B} → A [ 1m ]⊢ B → □ α A [ 1m ]⊢ □ α B
  □func D = Ffunc (Ufunc D)

  □functor : ∀ {p q : Mode} (α : q ≥ p) → Functor p p
  □functor α = Ffunctor α ∘Func Ufunctor α

  ◯func : ∀ {p q : Mode} {α : q ≥ p} {A B} → A [ 1m ]⊢ B → ◯ α A [ 1m ]⊢ ◯ α B
  ◯func D = Ufunc (Ffunc D)

  ◯functor : ∀ {p q : Mode} (α : q ≥ p) → Functor q q
  ◯functor α = Ufunctor α ∘Func Ffunctor α

  □counit : {p q : Mode} {A : Tp p} {α : q ≥ p} → □ α A [ 1m ]⊢ A
  □counit {α = α} = FL {α = α} {β = 1m} (UL 1m 1⇒ hyp)

  □counit-nattrans : ∀ {p q} {α : q ≥ p} → NatTrans (□functor α) 1Func
  □counit-nattrans = nat □counit (λ D → FL≈ ((!≈ (cut-ident-right (UL 1m 1⇒ D) ∘≈ eq (transport⊢1 _ ∘ transport⊢1 _)) ∘≈ UL≈ (cut-ident-left D)) ∘≈ cutUL D) ∘≈ cutFL D)

  □comult : {p q : Mode} {A : Tp p} {α : q ≥ p} → □ α A [ 1m ]⊢ □ α (□ α A)
  □comult {α = α} = FL {α = α} {β = 1m} (FR 1m 1⇒ (UR (FR 1m 1⇒ hyp))) 

  □comult-nattrans : ∀ {p q} {α : q ≥ p} → NatTrans (□functor α) (□functor α ∘Func □functor α)
  □comult-nattrans = nat □comult (λ D → FL≈ (FR≈ (UR≈ (FR≈ (UR≈ (transport⊢≈ 1⇒ (!≈ (cut-ident-right _) ∘≈ UL≈ (cut-ident-left D) ∘≈ cutUL D)))))))

  ◯unit : {p q : Mode} {A : Tp q} {α : q ≥ p} → A [ 1m ]⊢ ◯ α A
  ◯unit {α = α} = UR (FR 1m 1⇒ hyp)

  ◯unit-nat : {p q : Mode} {A A' : Tp q} {α : q ≥ p} (D : A [ 1m ]⊢ A')
             → cut D (◯unit {α = α}) ≈ cut ◯unit (◯func D)
  ◯unit-nat D = UR≈ (((eq (! (transport⊢1 _)) ∘≈ eq (! (transport⊢1 _)) ∘≈ !≈ (cut-ident-left (FR 1m 1⇒ D))) ∘≈ FR≈ (cut-ident-right D)) ∘≈ eq (cutFR D)) ∘≈ eq (cutUR D)

  ◯unit-nattrans : ∀ {p q} {α : q ≥ p} → NatTrans 1Func (◯functor α)
  ◯unit-nattrans = nat ◯unit (\ D -> !≈ (◯unit-nat D))

  ◯mult : {p q : Mode} {A : Tp q} {α : q ≥ p} → ◯ α (◯ α A) [ 1m ]⊢ ◯ α A
  ◯mult {α = α} = UR {α = α} {β = 1m} (UL 1m 1⇒ (FL (UL 1m 1⇒ hyp))) 

  ◯mult-nat : {p q : Mode} {A A' : Tp q} {α : q ≥ p} (D : A [ 1m ]⊢ A') 
            → cut (◯mult {α = α}) (◯func D) ≈ cut (◯func (◯func D)) ◯mult 
  ◯mult-nat D = UR≈ (UL≈ (FL≈ (UL≈ (FL≈ (transport⊢≈ 1⇒ ((eq (! (cutFR D)) ∘≈ FR≈ (!≈ (cut-ident-right _))) ∘≈ cut-ident-left _))))))

  ◯mult-nattrans : ∀ {p q} {α : q ≥ p} → NatTrans (◯functor α ∘Func ◯functor α) (◯functor α)
  ◯mult-nattrans = nat ◯mult (\ D -> (◯mult-nat D))

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
  -- F -| U

  FUadjunction1 : ∀ {p q} {A B} {α : q ≥ p} → F α A [ 1m ]⊢ B → A [ 1m ]⊢ U α B
  FUadjunction1 {α = α} D = UR {α = α} {β = 1m} (cut (FR 1m 1⇒ hyp) D) 

  FUadjunction2 : ∀ {p q} {A B} {α : q ≥ p} → A [ 1m ]⊢ U α B → F α A [ 1m ]⊢ B 
  FUadjunction2 {α = α} D = FL {α = α} {β = 1m} (cut D (UL 1m 1⇒ hyp)) 

  FUadj-composite2 : ∀ {p q} {A B} {α : q ≥ p} (D : F α A [ 1m ]⊢ B ) -> FUadjunction2 (FUadjunction1 D) ≈ D
  FUadj-composite2 D = (!≈ (Fη D) ∘≈ FL≈ (cut-ident-right _ ∘≈ eq (transport⊢1 _)))

  FUadj-composite1 : ∀ {p q} {A B} {α : q ≥ p} (D : A [ 1m ]⊢ U α B) -> FUadjunction1 (FUadjunction2 D) ≈ D
  FUadj-composite1 D = !≈ (Uη D) ∘≈ UR≈ (cut-ident-left _ ∘≈ eq (transport⊢1 _))

  FUadjunction-nat1 : ∀ {p q} {A A' B B'} {α : q ≥ p} 
                      (D1 : A' [ 1m ]⊢ A) (D : F α A [ 1m ]⊢ B) (D2 : B [ 1m ]⊢ B')
                    → FUadjunction1 (cut (Ffunc D1) (cut D D2))
                    ≈ cut D1 (cut (FUadjunction1 D) (Ufunc D2))
  FUadjunction-nat1 D1 D D2 = !≈ (eq (cutUR D1)) ∘≈ UR≈ {β = 1m} ((((!≈ (cut≈2 D1 (eq (transport⊢1 (cut (cut (FR 1m 1⇒ hyp) D) D2)))) ∘≈ !≈ (cut-assoc D1 (cut (FR 1m 1⇒ hyp) D) D2) ∘≈ !≈ (cut≈1 (cut-assoc D1 (FR 1m 1⇒ hyp) D) D2) ∘≈ !≈ (cut≈1 (cut≈1 (eq (cutFR D1)) D) D2) ∘≈ !≈ (cut≈1 (cut≈1 (FR≈ (cut-ident-right D1)) D) D2) ∘≈ cut-assoc (FR 1m 1⇒ D1) D D2) ∘≈ cut≈1 (cut-ident-left (FR 1m 1⇒ D1)) (cut D D2)) ∘≈ cut≈1 (eq (transport⊢1 (cut hyp (FR 1m 1⇒ D1)))) (cut D D2)) ∘≈ cut-assoc (FR 1m 1⇒ hyp) (Ffunc D1) (cut D D2))

  FUadjunction-nat2 : ∀ {p q} {A A' B B'} {α : q ≥ p} 
                      (D1 : A' [ 1m ]⊢ A) (D : A [ 1m ]⊢ U α B) (D2 : B [ 1m ]⊢ B')
                    → FUadjunction2 (cut D1 (cut D (Ufunc D2)))
                    ≈ cut (Ffunc D1) (cut (FUadjunction2 D) D2)
  FUadjunction-nat2 {α = α} D1 D D2 = !≈ (cutFL {α = 1m} (cut (FL {α = α} {β = 1m} (cut D (UL 1m 1⇒ hyp))) D2)) ∘≈ FL≈ {α = α} {β = 1m} (!≈ (cut-assoc (FR 1m 1⇒ D1) (FL {α = α} {β = 1m} (cut D (UL 1m 1⇒ hyp))) D2) ∘≈ (((cut≈1 (eq (! (transport⊢1 (cut D1 (cut D (UL 1m 1⇒ hyp)))))) D2 ∘≈ cut-assoc D1 (cut D (UL 1m 1⇒ hyp)) D2 ∘≈ cut≈2 D1 (cut-assoc D (UL 1m 1⇒ hyp) D2) ∘≈ cut≈2 D1 (cut≈2 D (!≈ (cutUL D2))) ∘≈ cut≈2 D1 (cut≈2 D (UL≈ (!≈ (cut-ident-left D2))))) ∘≈ cut≈2 D1 (cut≈2 D (cut-ident-right (UL 1m 1⇒ D2) ∘≈ eq (transport⊢1 _)))) ∘≈ !≈ (cut≈2 D1 (cut-assoc D (UR {α = α} {β = 1m} (UL 1m 1⇒ D2)) (UL 1m 1⇒ hyp)))) ∘≈ !≈ (cut-assoc D1 (cut D (UR {α = α} {β = 1m} (UL 1m 1⇒ D2))) (UL 1m 1⇒ hyp)))

  FUadjunction : ∀ {p q} → q ≥ p → Adjunction q p
  FUadjunction α = adj (Ffunctor α) (Ufunctor α) FUadjunction1 FUadjunction2 (λ q → UR≈ {α = α} {β = 1m} (cut≈2 (FR 1m 1⇒ hyp) q)) (λ q → FL≈ {α = α} {β = 1m} (cut≈1 q (UL 1m 1⇒ hyp))) FUadj-composite2 FUadj-composite1 FUadjunction-nat1 

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

  FU1-conjugate : ∀ {p} {A B : Tp p}
                  {D : A [ 1m ]⊢ B} →
                  Adjunction.LtoR (FUadjunction 1m) (cut F11 D) ≈ cut D U12
  FU1-conjugate {D = D} = !≈ (eq (cutUR D)) ∘≈ UR≈ {α = 1m} {β = 1m ∘1 1m} (!≈ (cut-ident-right D) ∘≈ (cut-ident-left D ∘≈ cut≈1 (cut-ident-left hyp ∘≈ eq (transport⊢1 _)) D) ∘≈ cut-assoc (FR 1m 1⇒ hyp) (FL {α = 1m} hyp) D)

  FU1-adjiso : ∀ {p} → AdjIso (FUadjunction 1m) (1Adj {p}) 
  FU1-adjiso = adjiso F1-natiso (!natiso U1-natiso) (\ {A}{B}{D} → FU1-conjugate {D = D})

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

  FU∘-adjiso : ∀ {p q r} {α : r ≥ q} {β : q ≥ p} → AdjIso (FUadjunction (α ∘1 β)) (FUadjunction α ·Adj FUadjunction β)
  FU∘-adjiso {α = α} {β = β} = adjiso F∘-natiso (!natiso U∘-natiso) (\ {A}{B}{D} → UR≈ {α = α ∘1 β} {β = 1m} (((!≈ (eq (transport⊢1 _ ∘ transport⊢1 _)) ∘≈ !≈ (cut-ident-right (cut (FR 1m 1⇒ hyp) (cut (FR 1m 1⇒ hyp) D))) ∘≈ !≈ (cut-assoc (FR 1m 1⇒ hyp) (FR 1m 1⇒ hyp) D) ∘≈ cut≈1 (FR≈ {α = β} {β = (1m ∘1 α) ∘1 ((1m ∘1 β) ∘1 1m)} (!≈ (cut-ident-left (FR 1m 1⇒ (ident A)) ∘≈ eq (transport⊢1 _)))) D) ∘≈ cut≈1 (cut-ident-left _ ∘≈ eq (transport⊢1 _)) D) ∘≈ cut-assoc (FR 1m 1⇒ (ident A)) (FL {α = α ∘1 β} {β = 1m} (FR α 1⇒ (FR 1m 1⇒ (ident A)))) D))

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

  -- ----------------------------------------------------------------------
  -- 2-cells induce morphisms of adjunctions (conjugate pairs of functors)
  -- F is contravariant; U is covariant

  F2 : ∀ {p q} {A : Tp q} {α β : q ≥ p} → β ⇒ α → F α A [ 1m ]⊢ F β A
  F2 {α = α} e = FL {α = α} {β = 1m} (FR 1m e hyp)

  F21 : ∀ {p q} {A : Tp q} {α : q ≥ p} → F2 {A = A} (1⇒ {α = α}) ≈ hyp 
  F21 = id

  F2· : ∀ {p q} {A : Tp q} {α β γ : q ≥ p} {e1 : β ⇒ α} {e2 : γ ⇒ β} → F2 {A = A} (e2 ·2 e1) ≈ cut (F2 {A = A} e1) (F2 {A = A} e2)
  F2· = FL≈ (!≈ (transport⊢≈ _ (cut-ident-left _)))

  F2-natural : ∀ {p q : Mode} {α β : p ≥ q} {A B : Tp p} (e : α ⇒ β) (D : A [ 1m ]⊢ B) →
                     cut {α = 1m} (F2 e) (Ffunc {α = α} D) ≈ (cut {β = 1m} (Ffunc {α = β} D) (F2 e))
  F2-natural {β = β} e D = FL≈ {α = β} {β = 1m ∘1 1m} (!≈ (eq (transport⊢1 _)) ∘≈ (!≈ (eq (cutFR D)) ∘≈ (!≈ (FR≈ {γ = 1m} {e = e} (cut-ident-right D)) ∘≈ transport⊢≈ e (cut-ident-left (FR 1m 1⇒ D)))))

  F2-nattrans : ∀ {p q} {α β : q ≥ p} (e : α ⇒ β) → NatTrans (Ffunctor β) (Ffunctor α)
  F2-nattrans e = nat (F2 e) (F2-natural e)

  U2 : ∀ {p q} {A : Tp p} {α β : q ≥ p} → α ⇒ β → U α A [ 1m ]⊢ U β A
  U2 {α = α} {β = β} e = UR {α = β} {β = 1m} (UL 1m e hyp)

  U21 : ∀ {p q} {A : Tp p} {α : q ≥ p} → U2 {A = A} (1⇒ {α = α}) ≈ hyp 
  U21 = id

  U2· : ∀ {p q} {A : Tp p} {α β γ : q ≥ p} {e1 : β ⇒ α} {e2 : γ ⇒ β} → U2 {A = A} (e2 ·2 e1) ≈ cut (U2 {A = A} e2) (U2 {A = A} e1)
  U2· {α = α} {e1 = e1} {e2} = UR≈ {α = α} {β = 1m} (!≈ (transport⊢≈ e1 (cut-ident-right (UL 1m e2 hyp))))

  U2-natural : ∀ {p q : Mode} {α β : p ≥ q} {A B : Tp q} (e : α ⇒ β) (D : A [ 1m ]⊢ B) →
                     cut {α = 1m} (U2 e) (Ufunc {α = β} D) ≈ (cut {β = 1m} (Ufunc {α = α} D) (U2 e))
  U2-natural {α = α} {β = β} e D = UR≈ {α = β} {β = 1m ∘1 1m} ((((!≈ (transport⊢≈ e (cut-ident-right (UL 1m 1⇒ D)))) ∘≈ UL≈ {γ = 1m}{e = e} (cut-ident-left D)) ∘≈ cutUL D) ∘≈ eq (transport⊢1 _))

  U2-nattrans : ∀ {p q} {α β : q ≥ p} (e : α ⇒ β) → NatTrans (Ufunctor α) (Ufunctor β)
  U2-nattrans e = nat (U2 e) (U2-natural e)

  FUadjunction-mor : ∀ {p q} {α β : q ≥ p} (e : α ⇒ β) → AdjMor (FUadjunction β) (FUadjunction α)
  FUadjunction-mor {α = α}{β} e = adjmor (F2-nattrans e) (U2-nattrans e) (λ {A} {B} {D} → UR≈ {α = β} {β = 1m} (((!≈ (transport⊢≈ e (cut-ident-right (cut (FR 1m 1⇒ hyp) D))) ∘≈ !≈ (transport⊢cut2 {e1 = e} (FR 1m 1⇒ (ident A)) D)) ∘≈ cut≈1 (cut-ident-left (FR 1m e (ident A)) ∘≈ eq (transport⊢1 _)) D) ∘≈ cut-assoc (FR 1m 1⇒ (ident A)) (FL {β = 1m} (FR 1m e (ident A))) D)) 

  -- ----------------------------------------------------------------------
  -- pseudofunctor from M into Adj


  -- (0) each object of M determines a category:
  --     objects of p are A : Tp p
  --     morphisms are D : A [ 1m ]⊢ B mod ≈ 
  --               id and comp are ident and cut, which are associative and unital up to ≈

  -- (1) functor from each hom category q ≥ p to category of Adjunction q p and AdjMor's 
  
  P1-ob : ∀ {p q} → q ≥ p → Adjunction q p
  P1-ob = FUadjunction

  P1-mor : ∀ {p q} {α β : q ≥ p} (e : α ⇒ β) → AdjMor (P1-ob β) (P1-ob α)
  P1-mor e = FUadjunction-mor e

  P1-mor-1 : ∀ {p q} {α : q ≥ p} → P1-mor (1⇒{_}{_}{α}) ==AdjMor 1AdjMor
  P1-mor-1 = eqadjmor F21 U21

  P1-mor-· : ∀ {p q} {α β γ : q ≥ p} (e1 : α ⇒ β) (e2 : β ⇒ γ)
           → (P1-mor (e1 ·2 e2)) ==AdjMor ((P1-mor e2) ·AdjMor (P1-mor e1))
  P1-mor-· e1 e2 = eqadjmor F2· U2·

  -- (2) for each p, a 2-cell isomorphism between P1-ob(1m:p≥p) and the identity 1-cell on P0(p)
  --     i.e. P1 preserves 1 up to isomorphism
  --     in this case, the identity 1-cell is the 1 -| 1 adjunction

  P1-1 : ∀ {p} → AdjIso (P1-ob 1m) (1Adj {p}) 
  P1-1 = FU1-adjiso

  -- (3) for composable α and β, a 2-cell natural isomorphism between P1-ob(α ∘1 β) and the composite of P1-ob(α) and P1-ob(β) 

  P1-∘ : ∀ {p q r} {α : r ≥ q} {β : q ≥ p} → AdjIso (P1-ob (α ∘1 β)) (P1-ob α ·Adj P1-ob β)
  P1-∘ = FU∘-adjiso

  -- P1(α ∘1 β) is a functor (r ≥ q × q ≥ p -> Adjunction r p)
  --    it's really P1 o (\ α β → (α ∘1 β))
  --    so it's functorial action is P1-mor o _∘1cong_
  -- 
  -- P1(α) ·Adj P1(β) is also a functor (r ≥ q × q ≥ p -> Adjunction r p)
  --    it's really P1 × P1 : r ≥ q × q ≥ p → Adjunction r q × Adjunction q p
  --    composed with ·Adj : Adjunction r q × Adjunction q p → Adjunction r p
  --    so it's functorial action is _·Adj-cong_ o (P1-mor × P1-mor)
  -- 
  -- so the naturality we want is as follows:

  P1-∘-nat : ∀ {p q r} {α α' : r ≥ q} {β β' : q ≥ p} (e1 : α ⇒ α') (e2 : β ⇒ β')
              → (P1-mor (e1 ∘1cong e2) ·AdjMor AdjIso-forward (P1-∘ {α = α} {β = β})) ==AdjMor (AdjIso-forward (P1-∘ {α = α'} {β = β'}) ·AdjMor (P1-mor e1 ·Adj-cong P1-mor e2))
  P1-∘-nat {α = α}{α'}{β}{β'} e1 e2 = 
    eqadjmor (FL≈ {α = α' ∘1 β'} {β = 1m} (!≈ (FR2 {α = β} {β = α' ∘1 β'} {γ = α'} {γ' = α} {e = _} {e' = e1 ∘1cong e2} {D = cut (FR 1m 1⇒ hyp) (cut (FL {α = α'} {β = 1m} (FR 1m e1 hyp)) hyp)} {D' = FR 1m 1⇒ hyp} e1 (! (interchange {e1 = e1} {e2 = 1⇒} {f1 = 1⇒} {f2 = e2})) ((( transport⊢≈ e1 (cut-ident-left (FR 1m 1⇒ hyp))) ∘≈ cut-ident-left _) ∘≈ eq (transport⊢1 _))) ∘≈ transport⊢≈ _ (cut-ident-left (FR α 1⇒ (FR 1m 1⇒ hyp)))))
             (UR≈ {α = α' ∘1 β'} {β = 1m} (!≈ (cut-ident-right (UL β' (e1 ∘1cong 1⇒) (transport⊢ 1⇒ (cut (UL 1m e2 hyp) hyp))) ∘≈ eq (transport⊢1 _) ∘≈ eq (transport⊢1 _)) ∘≈ !≈ (UL2 {e = e1 ∘1cong 1⇒} {e' = 1⇒ ·2 (e1 ∘1cong e2)} {D = transport⊢ 1⇒ (cut (UL 1m e2 hyp) hyp)} {D' = UL 1m 1⇒ hyp} e2 (! (interchange {e1 = 1⇒} {e2 = e1} {f1 = e2} {f2 = 1⇒})) (cut-ident-right (UL 1m e2 hyp) ∘≈ eq (transport⊢1 _))) ∘≈ transport⊢≈ (e1 ∘1cong e2) (cut-ident-right (UL β 1⇒ (UL 1m 1⇒ hyp))) ))

  -- (4) parts (2) and (3) are coherent

  -- P1-∘(1 , α) is related to P1-1 (congruenced with P1(α) and adjusted by the unitor for Adj, which is not an equality
  -- because we didn't squash ≈, so we use the weak 2-category formulation)
  P1-1-∘-l : ∀ {p q} {α : q ≥ p} 
           → AdjIso-forward (P1-∘ {α = 1m} {β = α}) 
             ==AdjMor 
             (AdjIso-backward (·Adj-unit-l (P1-ob α)) ·AdjMor (AdjIso-backward P1-1 ·Adj-cong 1AdjMor {a = P1-ob α})) 
  P1-1-∘-l {α = α} = eqadjmor (FL≈ {α = α} {β = 1m} (!≈ (cut-ident-left _ ∘≈ eq (transport⊢1 _)) ∘≈ FR≈ {α = α} {β = 1m ∘1 α} (!≈ (cut-ident-left _ ∘≈ eq (transport⊢1 _))))) (UR≈ {α = α} {β = 1m} (!≈ (cut-ident-right (UL {α = 1m} {β = α} α 1⇒ (transport⊢ 1⇒ (cut (UL {α = α} {β = α} 1m 1⇒ hyp) hyp))) ∘≈ eq (transport⊢1 (cut (UL {α = 1m} {β = α} α 1⇒ (transport⊢ 1⇒ (cut (UL 1m 1⇒ hyp) hyp))) hyp))) ∘≈ UL≈ (!≈ (cut-ident-right _ ∘≈ eq (transport⊢1 _)))))

  -- P1-∘(α , 1) is related to P1-1 (congruenced with P1(α) and adjusted by the unitor for Adj)
  P1-1-∘-r : ∀ {p q} {α : q ≥ p} 
           → AdjIso-forward (P1-∘ {α = α} {β = 1m}) 
             ==AdjMor 
             (AdjIso-forward (·Adj-unit-r (P1-ob α)) ·AdjMor (1AdjMor {a = P1-ob α} ·Adj-cong AdjIso-backward P1-1)) 
  P1-1-∘-r {α = α} = eqadjmor (!≈ (Fη _) ∘≈ FL≈ {α = α ∘1 1m} {β = 1m} (FR≈ (!≈ (cut-ident-left _ ∘≈ eq (transport⊢1 _) ∘≈ cut-ident-left _ ∘≈ eq (transport⊢1 _) ∘≈ cut-ident-left _ ∘≈ eq (transport⊢1 _))))) 
                             (UR≈ (!≈ (cut-ident-right _ ∘≈ eq (transport⊢1 _) ∘≈ cut-ident-right _ ∘≈ eq (transport⊢1 _))))

  -- P-∘(γ, β ∘ α) and P-∘(β,α)  is the same as  P-∘(γ ∘ β, α) and P-∘(γ,β)  up to the associator
  P1-∘-assoc : ∀ {p q r s} {α : q ≥ p} {β : r ≥ q} {γ : s ≥ r}
             → ((1AdjMor {a = P1-ob γ} ·Adj-cong AdjIso-backward (P1-∘ {α = β} {β = α})) ·AdjMor AdjIso-backward (P1-∘ {α = γ} {β = β ∘1 α}))
                ==AdjMor 
                (AdjIso-backward (·Adj-assoc (P1-ob γ) (P1-ob β) (P1-ob α)) ·AdjMor
                 ((AdjIso-backward (P1-∘ {α = γ} {β = β}) ·Adj-cong 1AdjMor {a = P1-ob α}) ·AdjMor
                 AdjIso-backward (P1-∘ {α = γ ∘1 β} {β = α})))
  P1-∘-assoc {α = α} {β}{γ} = eqadjmor (FL≈ {α = α} {β = 1m} (FL≈ {α = β} {β = α ∘1 1m} (FL≈ {α = γ} {β = β ∘1 (α ∘1 1m)} ((!≈ (((((cut-ident-left _ ∘≈ eq (transport⊢1 _)) ∘≈ cut≈1 (cut-ident-left (FR 1m 1⇒ hyp) ∘≈ eq (transport⊢1 _)) (FL {α = γ ∘1 β} {β = α} (FR 1m 1⇒ hyp))) ∘≈ eq (transport⊢1 _)) ∘≈ cut-ident-left _) ∘≈ eq (transport⊢1 _ ∘ transport⊢1 _ ∘ transport⊢1 _)) ∘≈ cut-ident-left (FR 1m 1⇒ hyp) ∘≈ eq (transport⊢1 _)) ∘≈ cut≈1 (cut-ident-left _ ∘≈ eq (transport⊢1 _)) (FL (FR 1m 1⇒ hyp)) ∘≈ eq (transport⊢1 _)))))
                                      (UR≈ {α = γ} {β = 1m}(UR≈ {α = β} {β = 1m ∘1 γ}(UR≈ {α = α} {β = (1m ∘1 γ) ∘1 β} (((!≈ (((((cut-ident-right _ ∘≈ eq (transport⊢1 _)) ∘≈ cut≈2 (UR {α = α} {β = γ ∘1 β} (UL 1m 1⇒ hyp)) (cut-ident-right (UL 1m 1⇒ hyp) ∘≈ eq (transport⊢1 _))) ∘≈ eq (transport⊢1 _)) ∘≈ cut-ident-right (transport⊢ 1⇒ (cut (UR {α = α} {β = γ ∘1 β} (UL 1m 1⇒ hyp)) (transport⊢ 1⇒ (cut (UL 1m 1⇒ hyp) hyp))))) ∘≈ eq (transport⊢1 _ ∘ transport⊢1 _ ∘ transport⊢1 _)) ∘≈ cut-ident-right (UL 1m 1⇒ hyp) ∘≈ eq (transport⊢1 _)) ∘≈ cut≈2 (UR {α = β ∘1 α} {β = γ} (UL 1m 1⇒ hyp)) (cut-ident-right (UL 1m 1⇒ hyp) ∘≈ eq (transport⊢1 _) ∘≈ eq (transport⊢1 _))) ∘≈ eq (transport⊢1 _)))))

