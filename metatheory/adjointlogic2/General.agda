
open import adjointlogic2.Lib
open import adjointlogic2.Rules
open import adjointlogic2.Properties

module adjointlogic2.General where

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

  Ffunc1-composite-1 : ∀ {p} {A : Tp p} → (cut (Ffunc11 {p = p} {A}) Ffunc12) ≈ hyp {_}{F 1m A}
  Ffunc1-composite-1 = FL≈ (FR≈ {e = 1⇒} (cut-ident-left _ ∘≈ eq (transport⊢1 _))) ∘≈ (Fη (FR 1m 1⇒ (FL {α = 1m} {β = 1m} hyp)) ∘≈ FR≈ (cut-ident-right _))

  Ffunc1-composite-2 : ∀ {p} {A : Tp p} → (cut Ffunc12 (Ffunc11 {p = p} {A})) ≈ hyp
  Ffunc1-composite-2 = cut-ident-left _ ∘≈ eq (transport⊢1 _)

  Ffunc1 : {p : Mode} {A : Tp p} → Iso (F 1m A) A
  Ffunc1 = iso Ffunc11 Ffunc12 Ffunc1-composite-1 Ffunc1-composite-2 


  Ffunc∘1 : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _}
          → F α (F β A) [ 1m ]⊢ F (β ∘1 α) A
  Ffunc∘1 = FL (FL (FR 1m 1⇒ hyp))

  Ffunc∘2 : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _}
          → F (β ∘1 α) A [ 1m ]⊢ F α (F β A)
  Ffunc∘2 {α = α} {β = β} = FL {α = β ∘1 α} {β = 1m} (FR β 1⇒ (FR 1m 1⇒ hyp)) 

  Ffunc∘-composite-1 : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _}
          → cut (Ffunc∘1 {α = α} {β = β} {A = A}) Ffunc∘2 ≈ hyp
  Ffunc∘-composite-1 {α = α} {β = β} = FL≈ (!≈ (Fη (FR 1m 1⇒ (FL (FR 1m 1⇒ hyp))))) ∘≈ eq (! (ap (λ x → FL (FL (FR β 1⇒ x))) (transport⊢1 _)) ) ∘≈ !≈ (FL≈ (FL≈ (FR≈ (cut-ident-left _)))) ∘≈ FL≈ (FL≈  (cut-ident-left _)) ∘≈ eq (ap FL (ap FL (transport⊢1 _))) 

  Ffunc∘-composite-2 : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _}
          → cut Ffunc∘2 (Ffunc∘1 {α = α} {β = β} {A = A}) ≈ hyp
  Ffunc∘-composite-2 = FL≈ ((cut-ident-left _ ∘≈ eq (transport⊢1 _)) ∘≈ eq (transport⊢1 _))

  Ffunc∘ : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _} → Iso (F α (F β A)) (F (β ∘1 α) A)
  Ffunc∘ = iso Ffunc∘1 Ffunc∘2 Ffunc∘-composite-1 Ffunc∘-composite-2



  Ufunc11 : ∀ {p} {A : Tp p} → U 1m A [ 1m ]⊢ A
  Ufunc11 = UL 1m 1⇒ hyp

  Ufunc12 : ∀ {p} {A : Tp p} → A [ 1m ]⊢ U 1m A
  Ufunc12 = UR {α = 1m} {β = 1m} hyp

  Ufunc1-composite-1 : ∀ {p} {A : Tp p} → cut Ufunc11 Ufunc12 ≈ ident (U 1m A)
  Ufunc1-composite-1  = UR≈ {α = 1m}{β = 1m ∘1 1m} (UL≈ (cut-ident-left hyp) ∘≈ cutUL hyp)

  Ufunc1-composite-2 : ∀ {p} {A : Tp p} → cut Ufunc12 Ufunc11 ≈ ident A
  Ufunc1-composite-2 = cut-ident-left hyp ∘≈ eq (transport⊢1 _)


  Ufunc1 : {p : Mode} {A : Tp p} → Iso (U 1m A) A
  Ufunc1 = iso Ufunc11 Ufunc12 Ufunc1-composite-1 Ufunc1-composite-2 

  Ufunc∘1 : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _}
          → U β (U α A) [ 1m ]⊢ U (β ∘1 α) A
  Ufunc∘1 {α = α} {β = β} = UR {α = β ∘1 α} {β = 1m} (UL α 1⇒ (UL 1m 1⇒ hyp))

  Ufunc∘2 : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _}
          → U (β ∘1 α) A [ 1m ]⊢ U β (U α A)
  Ufunc∘2 {α = α} {β = β} = UR {α = β} {β = 1m} (UR (UL 1m 1⇒ hyp)) 

  Ufunc∘ : ∀ {x y z : Mode} {α : y ≥ x} {β : z ≥ y} {A : Tp _} → Iso (U β (U α A)) (U (β ∘1 α) A)
  Ufunc∘ {α = α} {β = β} = 
    iso Ufunc∘1 Ufunc∘2
           (UR≈ {α = β} {β = 1m ∘1 1m} (!≈ (Uη _) ∘≈ UR≈ ((UL≈ {e = 1⇒} (!≈ (eq (transport⊢1 _)) ∘≈ !≈ (cut-ident-right _)) ∘≈ cut-ident-right (UL _ 1⇒ (UL 1m 1⇒ hyp))) ∘≈ eq (transport⊢1 _)) ) )
           (UR≈ (cut-ident-right _ ∘≈ (eq (transport⊢1 _ ∘ transport⊢1 _))))

  -- ----------------------------------------------------------------------
  -- functoriality of F and U on terms

  Ffunc : ∀ {p q : Mode} {α : q ≥ p} {A B} → A [ 1m ]⊢ B → F α A [ 1m ]⊢ F α B
  Ffunc {α = α} D =  FL {α = α} {β = 1m} (FR 1m 1⇒ D)

  Ffunc-ident : ∀ {p q : Mode} {α : q ≥ p} {A} → Ffunc (ident A) ≈ (ident (F α A))
  Ffunc-ident = id

  Ffunc-cut : ∀ {p q : Mode} {α : q ≥ p} {A B C} {D : A [ 1m ]⊢ B} {E : B [ 1m ]⊢ C} → Ffunc {α = α} (cut D E) ≈ cut (Ffunc D) (Ffunc E)
  Ffunc-cut {D = D} {E = E} = eq (! (ap FL (transport⊢1 _)) ∘ ap FL (! (cutFR D)) )

  -- action of F on terms is functorial in α

  Ffunc-func1 : ∀ {p : Mode} {A B : Tp p} (D : A [ 1m ]⊢ B) → Ffunc {α = 1m} {A} {B} D ≈ cut {α = 1m} {β = 1m} Ffunc11 (cut {α = 1m} {β = 1m} D Ffunc12)
  Ffunc-func1 {A = A} {B = B} D = eq (! (ap (cut Ffunc11) (cutFR D))) ∘≈ (!≈ (Fη _) ∘≈ FL≈ (FR≈ {e = 1⇒} (!≈ (cut-assoc (FR 1m 1⇒ hyp) (FL {α = 1m} {β = 1m} hyp) (cut D hyp)) ∘≈ 
                                    (!≈ (cut≈2 (transport⊢ 1⇒ (cut (ident A) (ident A))) (cut-ident-right D)) ∘≈ (cut≈1 (!≈ (cut-ident-left (ident A) ∘≈ eq (transport⊢1 _))) D) ∘≈ !≈ (cut-ident-left D)))))

  Ffunc-func∘ : ∀ {p q r : Mode} {α : p ≥ q} {β : q ≥ r} {A B : Tp p} (D : A [ 1m ]⊢ B) 
                  → Ffunc {α = β} (Ffunc {α = α} D) ≈ cut {α = 1m} {β = 1m} Ffunc∘1 (cut {α = 1m} {β = 1m} (Ffunc {α = α ∘1 β} D) Ffunc∘2)
  Ffunc-func∘ D = FL≈ (FL≈ (eq (! (transport⊢1 _)) ∘≈ !≈ (cut-ident-left _) ∘≈ eq (! (transport⊢1 _)) ∘≈ eq (! (cutFR D)) ∘≈ FR≈ {e = 1⇒} (((!≈ (eq (cutFR D)) ∘≈ FR≈ (!≈ (cut-ident-right _))) ∘≈ cut-ident-left _) ∘≈ eq (transport⊢1 _))) ∘≈ Fη (FR 1m 1⇒ (Ffunc D)))

  -- functoriality preserves equivalence
  
  Ffunc-i : ∀ {p q} {α : p ≥ q} {A B : Tp p} → Iso A B → Iso (F α A) (F α B)
  Ffunc-i (iso f g α β) = iso (Ffunc f) (Ffunc g) (FL≈ ((FR≈ α ∘≈ eq (cutFR f)) ∘≈ eq (transport⊢1 (cut f (FR 1m 1⇒ g))))) (FL≈ ((FR≈ β ∘≈ eq (cutFR g)) ∘≈ eq (transport⊢1 (cut g (FR 1m 1⇒ f)))))


  Ufunc : ∀ {p q : Mode} {α : q ≥ p} {A B} → A [ 1m ]⊢ B → U α A [ 1m ]⊢ U α B
  Ufunc {α = α} D =  UR {α = α} {β = 1m} (UL 1m 1⇒ D)

  Ufunc-ident : ∀ {p q : Mode} {α : q ≥ p} {A} → Ufunc (ident A) ≈ (ident (U α A))
  Ufunc-ident = id

  Ufunc-cut : ∀ {p q : Mode} {α : q ≥ p} {A B C} {D : A [ 1m ]⊢ B} {E : B [ 1m ]⊢ C} → Ufunc {α = α} (cut D E) ≈ cut (Ufunc D) (Ufunc E)
  Ufunc-cut {D = D} {E} = UR≈ (eq (! (transport⊢1 _)) ∘≈ (!≈ (cutUL E)))

  Ufunc-func1 : ∀ {p : Mode} {A B : Tp p} (D : A [ 1m ]⊢ B) → Ufunc {α = 1m} {A} {B} D ≈ cut {α = 1m} {β = 1m} Ufunc11 (cut {α = 1m} {β = 1m} D Ufunc12)
  Ufunc-func1 {A = A} {B = B} D = !≈ ((UR≈ (UL≈ (((cut-ident-right D ∘≈ (cut≈2 D (cut-ident-left _ ∘≈ eq (transport⊢1 _)))) ∘≈ !≈ (cut-assoc D (UR {β = 1m} hyp) (UL 1m 1⇒ (ident B)))) ∘≈ cut≈1 (cut-ident-left (cut D (UR {β = 1m} hyp))) (UL 1m 1⇒ (ident B)))) ∘≈ Uη _) ∘≈ cutUL (cut D (UR {α = 1m} {β = 1m} hyp)))

  Ufunc-func∘ : ∀ {p q r : Mode} {α : p ≥ q} {β : q ≥ r} {A B : Tp r} (D : A [ 1m ]⊢ B) 
                → Ufunc {α = α} (Ufunc {α = β} D) ≈ cut {α = 1m} {β = 1m} Ufunc∘1 (cut {α = 1m} {β = 1m} (Ufunc {α = α ∘1 β} D) Ufunc∘2)
  Ufunc-func∘ {α = α} {β = β} D = UR≈ {α = α} {β = 1m} (UR≈ {α = β} {β = 1m ∘1 α} (!≈ (((UL≈ {e = 1⇒} ((eq (! (transport⊢1 _)) ∘≈ (!≈ (cutUL hyp) ∘≈ UL≈ {e = 1⇒} (!≈ (cut-ident-right D) ∘≈ cut-ident-left D))) ∘≈ cutUL D) ∘≈ cutUL D) ∘≈ eq (transport⊢1 _)) ∘≈ (cut≈2 (UR {α = α ∘1 β} {β = 1m} (UL β 1⇒ (UL 1m 1⇒ hyp))) (cut-ident-right (UL 1m 1⇒ D) ∘≈ eq (transport⊢1 (cut (UL 1m 1⇒ D) hyp)))) )) ∘≈ Uη _)

  -- functoriality preserves equivalences

  Ufunc-i : ∀ {p q} {α : p ≥ q} {A B : Tp q} → Iso A B → Iso (U α A) (U α B)
  Ufunc-i {α = α1} (iso f g α β) = iso (Ufunc f) (Ufunc g) (UR≈ {α = α1} {β = 1m ∘1 1m} ((UL≈ {e = 1⇒} α ∘≈ cutUL g) ∘≈ eq (transport⊢1 _))) (UR≈ {α = α1} {β = 1m ∘1 1m} ((UL≈ {e = 1⇒} β ∘≈ cutUL f) ∘≈ eq (transport⊢1 _)) )


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

  -- one of many ways to phrase this; see
  -- https://unapologetic.wordpress.com/2007/07/30/transformations-of-adjoints/
  F2U2conjugate : ∀ {p q} {A : Tp q} {α β : q ≥ p} {e : β ⇒ α}
            → cut (◯unit  {A = A} {α = α}) (Ufunc (F2 e)) ≈ cut (◯unit {A = A} {α = β}) (U2 {A = F β A} e)
  F2U2conjugate {A = A} {α = α} {β = β} {e} = 
     UR≈ {α = α} {β = 1m} (!≈ (transport⊢≈ e (cut-ident-left _ ∘≈ eq (transport⊢1 (cut (ident A) (FR 1m 1⇒ (ident A)))))) ∘≈ (cut-ident-left _ ∘≈ eq (transport⊢1 _))) ∘≈ eq (transport⊢1 _)

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

