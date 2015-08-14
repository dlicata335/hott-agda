
open import adjointlogic.Lib
open import adjointlogic.Rules
open import adjointlogic.Properties

module adjointlogic.General where

  record QEquiv {p : Mode} (A B : Tp p) : Set where
    constructor qequiv
    field
      f : A [ 1m ]⊢ B
      g : B [ 1m ]⊢ A
      α : cut f g == hyp
      β : cut g f == hyp

  _·qeq_ : {p : Mode} {A B C : Tp p} → QEquiv A B → QEquiv B C → QEquiv A C
  qequiv f g α β ·qeq qequiv f' g' α' β' = 
      qequiv (cut f f') (cut g' g) 
             ((((α ∘ ap (cut f) (cut-ident-left g)) ∘ ap (λ H → cut f (cut H g)) α') ∘ ap (cut f) (cut-assoc f' g' g)) ∘ ! (cut-assoc f f' (cut g' g))) 
             ((((β' ∘ ap (cut g') (cut-ident-left f')) ∘ ap (λ H → cut g' (cut H f')) β) ∘ ap (cut g') (cut-assoc g f f')) ∘ ! (cut-assoc g' g (cut f f'))) 

  !qeq : {p : Mode} {A B : Tp p} → QEquiv A B → QEquiv B A
  !qeq (qequiv f g α β) = qequiv g f β α

  ⊕qeq : ∀ {p : Mode} {A A' B B' : Tp p} → QEquiv A A' → QEquiv B B' → QEquiv (A ⊕ B) (A' ⊕ B')
  ⊕qeq (qequiv f g α β) (qequiv f₁ g₁ α₁ β₁) = 
    qequiv (Case (cut f (Inl hyp)) (cut f₁ (Inr hyp))) (Case (cut g (Inl hyp)) (cut g₁ (Inr hyp))) 
           (ap2 Case ((((cut-ident-left _ ∘ ap (λ x → cut x (Inl hyp)) α) ∘ cut-assoc f g (Inl hyp)) ∘ ap (cut f) (cut-ident-left _)) ∘ ! (cut-assoc f (Inl hyp) (Case (cut g (Inl hyp)) (cut g₁ (Inr hyp)))))
                     ((((cut-ident-left _ ∘ ap (λ x → cut x (Inr hyp)) α₁) ∘ cut-assoc f₁ g₁ (Inr hyp)) ∘ ap (cut f₁) (cut-ident-left _)) ∘ ! (cut-assoc f₁ (Inr hyp) (Case (cut g (Inl hyp)) (cut g₁ (Inr hyp)))))) 
           (ap2 Case ((((cut-ident-left _ ∘ ap (λ x → cut x (Inl hyp)) β) ∘ cut-assoc g f (Inl hyp)) ∘ ap (cut g) (cut-ident-left _)) ∘ ! (cut-assoc g (Inl hyp) (Case (cut f (Inl hyp)) (cut f₁ (Inr hyp)))))
                     ((((cut-ident-left _ ∘ ap (λ x → cut x (Inr hyp)) β₁) ∘ cut-assoc g₁ f₁ (Inr hyp)) ∘ ap (cut g₁) (cut-ident-left _)) ∘ ! (cut-assoc g₁ (Inr hyp) (Case (cut f (Inl hyp)) (cut f₁ (Inr hyp))))))


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
  -- functoriality of F and U on 1-cells in the diagrams

  -- F is contravariant
  
  Ffunc11 : ∀ {p} {A : Tp p} → F 1m A [ 1m ]⊢ A
  Ffunc11 = FL {α = 1m} {β = 1m} hyp

  Ffunc12 : ∀ {p} {A : Tp p} → A [ 1m ]⊢ F 1m A
  Ffunc12 = FR 1m 1⇒ hyp

  Ffunc1-composite-1 : ∀ {p} {A : Tp p} → (cut (Ffunc11 {p = p} {A}) Ffunc12) == hyp {_}{F 1m A}
  Ffunc1-composite-1 = ap (λ x → FL (FR 1m 1⇒ x)) (cut-ident-left _ ∘ transport⊢1 _) ∘ (Fη (FR 1m 1⇒ (FL {α = 1m} {β = 1m} hyp)) ∘ ap (FR 1m 1⇒) (cut-ident-right _))

  Ffunc1-composite-2 : ∀ {p} {A : Tp p} → (cut Ffunc12 (Ffunc11 {p = p} {A})) == hyp
  Ffunc1-composite-2 = cut-ident-left _ ∘ transport⊢1 _

  Ffunc1 : {p : Mode} {A : Tp p} → QEquiv (F 1m A) A
  Ffunc1 = qequiv Ffunc11 Ffunc12 Ffunc1-composite-1 Ffunc1-composite-2 


  Ffunc∘1 : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _}
          → F α (F β A) [ 1m ]⊢ F (β ∘1 α) A
  Ffunc∘1 = FL (FL (FR 1m 1⇒ hyp))

  Ffunc∘2 : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _}
          → F (β ∘1 α) A [ 1m ]⊢ F α (F β A)
  Ffunc∘2 {α = α} {β = β} = FL {α = β ∘1 α} {β = 1m} (FR β 1⇒ (FR 1m 1⇒ hyp)) 

  Ffunc∘-composite-1 : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _}
          → cut (Ffunc∘1 {α = α} {β = β} {A = A}) Ffunc∘2 == hyp
  Ffunc∘-composite-1 {α = α} {β = β} =
    cut Ffunc∘1 Ffunc∘2 =〈 ap FL (ap FL (transport⊢1 _)) 〉 
    FL (FL (cut (ident _) (FR β 1⇒ (FR 1m 1⇒ hyp)))) =〈 ap (λ x → FL (FL x)) (cut-ident-left _) 〉 
    FL (FL (FR β 1⇒ (FR 1m 1⇒ hyp))) =〈 ! (ap (λ x → FL (FL (FR β 1⇒ x))) (cut-ident-left _)) 〉
    FL (FL (FR β 1⇒ (cut (ident _) (FR 1m 1⇒ hyp)))) =〈 ! (ap (λ x → FL (FL (FR β 1⇒ x))) (transport⊢1 _)) 〉 
    FL (FL (FR β 1⇒ (transport⊢ 1⇒ (cut hyp (FR 1m 1⇒ hyp))))) =〈 ap FL (! (Fη (FR 1m 1⇒ (FL (FR 1m 1⇒ hyp))))) 〉 
    hyp ∎

  Ffunc∘-composite-2 : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _}
          → cut Ffunc∘2 (Ffunc∘1 {α = α} {β = β} {A = A}) == hyp
  Ffunc∘-composite-2 = ap FL ((cut-ident-left _ ∘ transport⊢1 _) ∘ transport⊢1 _)

  Ffunc∘ : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _} → QEquiv (F α (F β A)) (F (β ∘1 α) A)
  Ffunc∘ = qequiv Ffunc∘1 Ffunc∘2 Ffunc∘-composite-1 Ffunc∘-composite-2



  Ufunc11 : ∀ {p} {A : Tp p} → U 1m A [ 1m ]⊢ A
  Ufunc11 = UL 1m 1⇒ hyp

  Ufunc12 : ∀ {p} {A : Tp p} → A [ 1m ]⊢ U 1m A
  Ufunc12 = UR {α = 1m} {β = 1m} hyp

  Ufunc1-composite-1 : ∀ {p} {A : Tp p} → cut Ufunc11 Ufunc12 == ident (U 1m A)
  Ufunc1-composite-1  = ap (UR {α = 1m}{β = 1m ∘1 1m}) (ap (UL 1m 1⇒) (cut-ident-left hyp) ∘ cutUL hyp)

  Ufunc1-composite-2 : ∀ {p} {A : Tp p} → cut Ufunc12 Ufunc11 == ident A
  Ufunc1-composite-2 = cut-ident-left hyp ∘ transport⊢1 _

  Ufunc1 : {p : Mode} {A : Tp p} → QEquiv (U 1m A) A
  Ufunc1 = qequiv Ufunc11 Ufunc12 Ufunc1-composite-1 Ufunc1-composite-2 


  Ufunc∘1 : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _}
          → U β (U α A) [ 1m ]⊢ U (β ∘1 α) A
  Ufunc∘1 {α = α} {β = β} = UR {α = β ∘1 α} {β = 1m} (UL α 1⇒ (UL 1m 1⇒ hyp))

  Ufunc∘2 : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _}
          → U (β ∘1 α) A [ 1m ]⊢ U β (U α A)
  Ufunc∘2 {α = α} {β = β} = UR {α = β} {β = 1m} (UR (UL 1m 1⇒ hyp)) 

  Ufunc∘ : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _} → QEquiv (U β (U α A)) (U (β ∘1 α) A)
  Ufunc∘ {α = α} {β = β} = 
    qequiv Ufunc∘1 Ufunc∘2
           (ap (UR {α = β} {β = 1m ∘1 1m}) (! (Uη _) ∘ ap UR ((ap (UL _ 1⇒) (! (transport⊢1 _) ∘ ! (cut-ident-right _)) ∘ cut-ident-right (UL _ 1⇒ (UL 1m 1⇒ hyp))) ∘ transport⊢1 _)) ) 
           (ap UR (cut-ident-right _ ∘ (transport⊢1 _ ∘ transport⊢1 _)))

  -- ----------------------------------------------------------------------
  -- functoriality of F and U on terms

  Ffunc : ∀ {p q : Mode} {α : q ≥ p} {A B} → A [ 1m ]⊢ B → F α A [ 1m ]⊢ F α B
  Ffunc {α = α} D =  FL {α = α} {β = 1m} (FR 1m 1⇒ D)

  Ffunc-ident : ∀ {p q : Mode} {α : q ≥ p} {A} → Ffunc (ident A) == (ident (F α A))
  Ffunc-ident = id

  Ffunc-cut : ∀ {p q : Mode} {α : q ≥ p} {A B C} {D : A [ 1m ]⊢ B} {E : B [ 1m ]⊢ C} → Ffunc {α = α} (cut D E) == cut (Ffunc D) (Ffunc E)
  Ffunc-cut {D = D} {E = E} = FL (FR 1m 1⇒ (cut D E))  =〈 ap FL (! (cutFR D))〉 
                              FL (cut D (FR 1m 1⇒ E)) =〈 ! (ap FL (transport⊢1 _)) 〉
                              _ ∎

  -- action of F on terms is functorial in α

  Ffunc-func1 : ∀ {p : Mode} {A B : Tp p} (D : A [ 1m ]⊢ B) → Ffunc {α = 1m} {A} {B} D == cut {α = 1m} {β = 1m} Ffunc11 (cut {α = 1m} {β = 1m} D Ffunc12)
  Ffunc-func1 {A = A} {B = B} D = ! (ap (cut Ffunc11) (cutFR D)) ∘ (! (Fη _) ∘ ap FL (ap (FR 1m 1⇒) (! (cut-assoc (FR 1m 1⇒ hyp) (FL {α = 1m} {β = 1m} hyp) (cut D hyp)) ∘ 
                                    (! (ap (cut (transport⊢ 1⇒ (cut (ident A) (ident A)))) (cut-ident-right D)) ∘ (ap (λ x → cut x D) (! (cut-ident-left (ident A) ∘ transport⊢1 _)) ∘ ! (cut-ident-left D))))))

  Ffunc-func∘ : ∀ {p q r : Mode} {α : p ≥ q} {β : q ≥ r} {A B : Tp p} (D : A [ 1m ]⊢ B) 
                  → Ffunc {α = β} (Ffunc {α = α} D) == cut {α = 1m} {β = 1m} Ffunc∘1 (cut {α = 1m} {β = 1m} (Ffunc {α = α ∘1 β} D) Ffunc∘2)
  Ffunc-func∘ D = ap FL (ap FL (! (transport⊢1 _) ∘ (! (cut-ident-left _) ∘ (! (transport⊢1 _) ∘ ( ! (cutFR D) ∘ ap (FR _ 1⇒) (((! (cutFR D) ∘ ap (FR 1m 1⇒) (! (cut-ident-right _))) ∘ cut-ident-left _) ∘ transport⊢1 _))))) ∘ Fη (FR 1m 1⇒ (Ffunc D)))

  -- functoriality preserves equivalence
  
  Ffunc-qeq : ∀ {p q} {α : p ≥ q} {A B : Tp p} → QEquiv A B → QEquiv (F α A) (F α B)
  Ffunc-qeq (qequiv f g α β) = qequiv (Ffunc f) (Ffunc g) (ap FL ((ap (FR 1m 1⇒) α ∘ cutFR f) ∘ transport⊢1 (cut f (FR 1m 1⇒ g)))) (ap FL ((ap (FR 1m 1⇒) β ∘ cutFR g) ∘ transport⊢1 (cut g (FR 1m 1⇒ f))))



  Ufunc : ∀ {p q : Mode} {α : q ≥ p} {A B} → A [ 1m ]⊢ B → U α A [ 1m ]⊢ U α B
  Ufunc {α = α} D =  UR {α = α} {β = 1m} (UL 1m 1⇒ D)

  Ufunc-ident : ∀ {p q : Mode} {α : q ≥ p} {A} → Ufunc (ident A) == (ident (U α A))
  Ufunc-ident = id

  Ufunc-cut : ∀ {p q : Mode} {α : q ≥ p} {A B C} {D : A [ 1m ]⊢ B} {E : B [ 1m ]⊢ C} → Ufunc {α = α} (cut D E) == cut (Ufunc D) (Ufunc E)
  Ufunc-cut {D = D} {E} = ap UR (! (transport⊢1 _) ∘ (! (cutUL E)))

  Ufunc-func1 : ∀ {p : Mode} {A B : Tp p} (D : A [ 1m ]⊢ B) → Ufunc {α = 1m} {A} {B} D == cut {α = 1m} {β = 1m} Ufunc11 (cut {α = 1m} {β = 1m} D Ufunc12)
  Ufunc-func1 {A = A} {B = B} D = ! ((ap UR (ap (UL 1m 1⇒) (((cut-ident-right D ∘ ap (cut D) (cut-ident-left _ ∘ transport⊢1 _)) ∘ ! (cut-assoc D (UR {β = 1m} hyp) (UL 1m 1⇒ (ident B)))) ∘ ap (λ x → cut x (UL 1m 1⇒ (ident B))) (cut-ident-left (cut D (UR {β = 1m} hyp))))) ∘ Uη _) ∘ cutUL (cut D (UR {α = 1m} {β = 1m} hyp)))

  Ufunc-func∘ : ∀ {p q r : Mode} {α : p ≥ q} {β : q ≥ r} {A B : Tp r} (D : A [ 1m ]⊢ B) 
                → Ufunc {α = α} (Ufunc {α = β} D) == cut {α = 1m} {β = 1m} Ufunc∘1 (cut {α = 1m} {β = 1m} (Ufunc {α = α ∘1 β} D) Ufunc∘2)
  Ufunc-func∘ {α = α} {β = β} D = ap (UR {α = α} {β = 1m}) (ap (UR {α = β} {β = 1m ∘1 α}) (! (((ap (UL β 1⇒) ((! (transport⊢1 _) ∘ (! (cutUL hyp) ∘ ap (UL 1m 1⇒) (! (cut-ident-right D) ∘ cut-ident-left D))) ∘ cutUL D) ∘ cutUL D) ∘ transport⊢1 _) ∘ ap (cut (UR {α = α ∘1 β} {β = 1m} (UL β 1⇒ (UL 1m 1⇒ hyp)))) (cut-ident-right (UL 1m 1⇒ D) ∘ transport⊢1 (cut (UL 1m 1⇒ D) hyp))) ) ∘ Uη _)

  -- functoriality preserves equivalences

  Ufunc-qeq : ∀ {p q} {α : p ≥ q} {A B : Tp q} → QEquiv A B → QEquiv (U α A) (U α B)
  Ufunc-qeq {α = α1} (qequiv f g α β) = qequiv (Ufunc f) (Ufunc g) (ap (UR {α = α1} {β = 1m ∘1 1m}) ((ap (UL 1m 1⇒) α ∘ cutUL g) ∘ transport⊢1 _)) (ap (UR {α = α1} {β = 1m ∘1 1m}) ((ap (UL 1m 1⇒) β ∘ cutUL f) ∘ transport⊢1 _)) 


  -- ----------------------------------------------------------------------
  -- F -| U

  UFadjunction1 : ∀ {p q} {A B} {α : q ≥ p} → F α A [ 1m ]⊢ B → A [ 1m ]⊢ U α B
  UFadjunction1 {α = α} D = UR {α = α} {β = 1m} (cut (FR 1m 1⇒ hyp) D) 

  UFadjunction2 : ∀ {p q} {A B} {α : q ≥ p} → A [ 1m ]⊢ U α B → F α A [ 1m ]⊢ B 
  UFadjunction2 {α = α} D = FL {α = α} {β = 1m} (cut D (UL 1m 1⇒ hyp)) 

  UFadj-composite2 : ∀ {p q} {A B} {α : q ≥ p} (D : F α A [ 1m ]⊢ B ) -> UFadjunction2 (UFadjunction1 D) == D
  UFadj-composite2 D = (! (Fη D) ∘ ap FL (cut-ident-right _ ∘ transport⊢1 _))

  UFadj-composite1 : ∀ {p q} {A B} {α : q ≥ p} (D : A [ 1m ]⊢ U α B) -> UFadjunction1 (UFadjunction2 D) == D
  UFadj-composite1 D = ! (Uη D) ∘ ap UR (cut-ident-left _ ∘ transport⊢1 _)


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

  ◯assoc : ∀ {p q : Mode} {A : Tp q} {α : q ≥ p} 
          -> _==_ {◯ α (◯ α (◯ α A)) [ 1m ]⊢ ◯ α A} (cut (◯func ◯mult) ◯mult) (cut ◯mult ◯mult)
  ◯assoc = id

  ◯unit1 : ∀ {p q : Mode} {A : Tp q} {α : q ≥ p} 
              -> _==_ {◯ α A [ 1m ]⊢ ◯ α A} (cut ◯unit ◯mult) hyp
  ◯unit1 {α = α} = ap (λ x → UR {α = α} {β = 1m} (UL 1m 1⇒ (FL x))) (cut-ident-left _ ∘ transport⊢1 _)

  ◯unit2 : ∀ {p q : Mode} {A : Tp q} {α : q ≥ p} 
              -> _==_ {◯ α A [ 1m ]⊢ ◯ α A} (cut (◯func ◯unit) ◯mult) hyp
  ◯unit2 {α = α} = ap (λ x → UR {α = α} {β = 1m} (UL 1m 1⇒ (FL x))) (cut-ident-left _ ∘ (transport⊢1 _ ∘ (transport⊢1 _ ∘ transport⊢1 _)))

  □assoc : ∀ {p q : Mode} {A : Tp p} {α : q ≥ p} 
          -> _==_ {□ α A [ 1m ]⊢ □ α (□ α (□ α A)) } (cut □comult (□func □comult)) (cut □comult □comult)
  □assoc = id

  □unit1 : ∀ {p q : Mode} {A : Tp p} {α : q ≥ p} 
              -> _==_ {□ α A [ 1m ]⊢ □ α A} (cut □comult □counit) hyp
  □unit1 {α = α} = ap (λ x → FL (FR 1m 1⇒ (UR x))) (cut-ident-right _ ∘ transport⊢1 _) 

  □unit2 : ∀ {p q : Mode} {A : Tp p} {α : q ≥ p} 
              -> _==_ {□ α A [ 1m ]⊢ □ α A} (cut □comult (□func □counit)) hyp
  □unit2 {α = α} = ap (λ x → FL (FR 1m 1⇒ (UR x))) (((cut-ident-right _ ∘ transport⊢1 _) ∘ transport⊢1 _) ∘ transport⊢1 _)

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
                     cut {α = 1m} (F2 e) (Ffunc {α = α} D) == (cut {β = 1m} (Ffunc {α = β} D) (F2 e))
  F2-natural {β = β} e D = ap (FL {α = β} {β = 1m ∘1 1m}) (! (transport⊢1 _) ∘ (! (cutFR D) ∘ (! (ap (FR 1m e) (cut-ident-right D)) ∘ ap (transport⊢ e) (cut-ident-left (FR 1m 1⇒ D)))))

  F21 : ∀ {p q} {A : Tp q} {α : q ≥ p} → F2 {A = A} (1⇒ {α = α}) == hyp 
  F21 = id

  F2· : ∀ {p q} {A : Tp q} {α β γ : q ≥ p} {e1 : β ⇒ α} {e2 : γ ⇒ β} → F2 {A = A} (e2 ·2 e1) == cut (F2 {A = A} e1) (F2 {A = A} e2)
  F2· = ap FL (! (ap (transport⊢ _) (cut-ident-left _)))

  U2 : ∀ {p q} {A : Tp p} {α β : q ≥ p} → α ⇒ β → U α A [ 1m ]⊢ U β A
  U2 {α = α} {β = β} e = UR {α = β} {β = 1m} (UL 1m e hyp)

  U2-natural : ∀ {p q : Mode} {α β : p ≥ q} {A B : Tp q} (e : α ⇒ β) (D : A [ 1m ]⊢ B) →
                     cut {α = 1m} (U2 e) (Ufunc {α = β} D) == (cut {β = 1m} (Ufunc {α = α} D) (U2 e))
  U2-natural {α = α} {β = β} e D = ap (UR {α = β} {β = 1m ∘1 1m}) ((((! (ap (transport⊢ e) (cut-ident-right (UL 1m 1⇒ D)))) ∘ ap (UL 1m e) (cut-ident-left D)) ∘ cutUL D) ∘ transport⊢1 _)

  U21 : ∀ {p q} {A : Tp p} {α : q ≥ p} → U2 {A = A} (1⇒ {α = α}) == hyp 
  U21 = id

  U2· : ∀ {p q} {A : Tp p} {α β γ : q ≥ p} {e1 : β ⇒ α} {e2 : γ ⇒ β} → U2 {A = A} (e2 ·2 e1) == cut (U2 {A = A} e2) (U2 {A = A} e1)
  U2· {α = α} {e1 = e1} {e2} = ap (UR {α = α} {β = 1m}) (! (ap (transport⊢ e1) (cut-ident-right (UL 1m e2 hyp)))) 

  -- one of many ways to phrase this; see
  -- https://unapologetic.wordpress.com/2007/07/30/transformations-of-adjoints/
  F2U2conjugate : ∀ {p q} {A : Tp q} {α β : q ≥ p} {e : β ⇒ α}
            → cut (◯unit  {A = A} {α = α}) (Ufunc (F2 e)) == cut (◯unit {A = A} {α = β}) (U2 {A = F β A} e)
  F2U2conjugate {A = A} {α = α} {β = β} {e} = 
     ap (UR {α = α} {β = 1m}) (! (ap (transport⊢ e) (cut-ident-left _ ∘ transport⊢1 (cut (ident A) (FR 1m 1⇒ (ident A))))) ∘ (cut-ident-left _ ∘ transport⊢1 _)) ∘ transport⊢1 _

  -- equivalently:
  {-
  F2U2conjugate' : ∀ {p q} {A : Tp p} {α β : q ≥ p} {e : β ⇒ α}
                 → cut (Ffunc (U2 e)) (□counit {A = A} {α = α}) == cut (F2 e) (□counit {A = A} {α = β})
  F2U2conjugate' {α = α} {β} {e} = ap (FL {α = α} {β = 1m ∘1 1m}) {!!}
  -}


  -- ----------------------------------------------------------------------
  -- F preserves coproducts

  Fpres-coprod1 : ∀ {p q} {α : p ≥ q} {A B} → F α (A ⊕ B) [ 1m ]⊢ (F α A ⊕ F α B)
  Fpres-coprod1 {α = α} = FL {α = α} {β = 1m} (Case (Inl (FR 1m 1⇒ hyp)) (Inr (FR 1m 1⇒ hyp)))

  Fpres-coprod2 : ∀ {p q} {α : p ≥ q} {A B} → (F α A ⊕ F α B) [ 1m ]⊢ (F α (A ⊕ B))
  Fpres-coprod2 = Case (FL (FR 1m 1⇒ (Inl hyp))) (FL (FR 1m 1⇒ (Inr hyp)))

  Fpres-coprod-composite-1 : ∀ {p q} {α : p ≥ q} {A B} 
                           → cut (Fpres-coprod2 {α = α}{A}{B}) Fpres-coprod1 == hyp
  Fpres-coprod-composite-1 = ap2 Case (! (Fη _) ∘ ap FL (ap Inl (! (cut-ident-left _ ∘ transport⊢1 _)) ∘ (cut-ident-left _ ∘ transport⊢1 _))) (! (Fη _) ∘ ap FL (ap Inr (! (cut-ident-left _ ∘ transport⊢1 _)) ∘ (cut-ident-left _ ∘ transport⊢1 _)))

  Fpres-coprod-composite-2 : ∀ {p q} {α : p ≥ q} {A B} 
                           → cut (Fpres-coprod1 {α = α}{A}{B}) Fpres-coprod2 == hyp
  Fpres-coprod-composite-2 {α = α} = ap (FL {α = α} {β = 1m ∘1 1m}) (! (⊕η _) ∘ ap2 Case (! (ap (FR 1m 1⇒) (cut-ident-left _)) ∘ (cut-ident-left _ ∘ transport⊢1 _)) (! (ap (FR 1m 1⇒) (cut-ident-left _)) ∘ (cut-ident-left _ ∘ transport⊢1 _)))

  Fpres-coprod : ∀ {p q} {α : p ≥ q} {A B} → QEquiv (F α (A ⊕ B)) (F α A ⊕ F α B)
  Fpres-coprod = qequiv Fpres-coprod1 Fpres-coprod2 Fpres-coprod-composite-2 Fpres-coprod-composite-1
