
open import adjointlogic2.Lib
open import adjointlogic2.Rules
open import adjointlogic2.Properties
open import adjointlogic2.General
open import adjointlogic2.Idempotent

module adjointlogic2.Idempotent-Subcalculus4 where

  open IdempotentMonad

  ∘r : ∀ α → (α ∘1 r) == r
  ∘r α with 1-cell-case α
  ∘r .1m | Inl id = id
  ∘r .r | Inr id = id

  r∘ : ∀ α → (r ∘1 α) == r
  r∘ α with 1-cell-case α
  r∘ .1m | Inl id = id
  r∘ .r | Inr id = id


  -- ----------------------------------------------------------------------
  -- restricted sequent calculus

  data _[_]⊢'_ : Tp c → (c ≥ c) → Tp c → Set where
    copy' : ∀ {A} → A [ r ]⊢' A
    ident' : ∀ {A} → A [ 1m ]⊢' A
    cut' : ∀ {α : c ≥ c} {β : c ≥ c} {A : Tp c} {B : Tp c} {C : Tp c}
         → A [ β ]⊢' B
         → B [ α ]⊢' C
         → A [ β ∘1 α ]⊢' C
    ♯R' : ∀ { A B α } → A [ r ]⊢' B → A [ α ]⊢' ♯ B -- not restricted
    ♯L' : ∀ { A B } → A [ r ]⊢' B → ♯ A [ r ]⊢' B
    ♭L' : ∀ {A C} → A [ r ]⊢' C → ♭ A [ 1m ]⊢' C 
    ♭R' : ∀ {A B} → A [ r ]⊢' B → A [ r ]⊢' ♭ B
    Inl' : ∀ {α C A B} → C [ α ]⊢' A → C [ α ]⊢' (A ⊕ B)
    Inr' : ∀ {α C A B} → C [ α ]⊢' B → C [ α ]⊢' (A ⊕ B)
    Case' : ∀ {C A B} → A [ 1m ]⊢' C → B [ 1m ]⊢' C → (A ⊕ B) [ 1m ]⊢' C
    -- U1R' : ∀ { A B α } → A [ α ]⊢' B → A [ α ]⊢' U 1m B
    -- U1L' : ∀ { A B α } → A [ α ]⊢' B → U 1m A [ α ]⊢' B
    -- F1L' : ∀ {A B α} → A [ α ]⊢' B → F 1m A [ α ]⊢' B
    -- F1R' : ∀ {A B α} → A [ α ]⊢' B → A [ α ]⊢' F 1m B

  ♭L'r : ∀ {A B C} → A [ r ]⊢' B → B [ r ]⊢' C → ♭ A [ r ]⊢' C
  ♭L'r {A}{B} D E = cut' (♭L' (♯R' D)) (♯L' E)

  Case'r : ∀ {A B C D} → A [ r ]⊢' C → B [ r ]⊢' C → C [ r ]⊢' D → (A ⊕ B) [ r ]⊢' D
  Case'r D1 D2 E = cut' (Case' (♯R' D1) (♯R' D2)) (♯L' E) 

  -- ident and copy are not admissible in general, 
  -- but they could be restricted to positives, and admissible for negatives:
  copy♯ : ∀ {A} → ♯ A [ r ]⊢' ♯ A
  copy♯ = ♯R' (♯L' copy')

  ident♯ : ∀ {A} → ♯ A [ 1m ]⊢' ♯ A
  ident♯ = ♯R' (♯L' copy')

  unrestrict : ∀ {A B α} → A [ α ]⊢' B → A [ α ]⊢ B
  unrestrict ident' = hyp
  unrestrict copy' = copy
  unrestrict (cut' D E) = cut (unrestrict D) (unrestrict E)
  unrestrict {α = α} (♯R' D) with 1-cell-case α
  unrestrict (♯R' D) | Inl id = ♯R1 (unrestrict D)
  unrestrict (♯R' D) | Inr id = ♯Rr (unrestrict D)
  unrestrict (♯L' D) = ♯L (unrestrict D)
  unrestrict (♭L' D) = (♭L1 (unrestrict D))
  unrestrict (♭R' D) = ♭R (unrestrict D)
  unrestrict (Inl' D) = Inl (unrestrict D)
  unrestrict (Inr' D) = Inr (unrestrict D)
  unrestrict (Case' D D₁) = (Case (unrestrict D) (unrestrict D₁))
  -- unrestrict (U1R' D) = UR {α = 1m} (unrestrict D)
  -- unrestrict {α = α} (U1L' D) = UL {α = 1m} {β = α} α 1⇒ (unrestrict D)
  -- unrestrict (F1L' D) = FL {α = 1m} (unrestrict D)
  -- unrestrict {α = α} (F1R' D) = FR {α = 1m} {β = α} α 1⇒ (unrestrict D)

  unrestrict♯R1 : ∀ {A B} {D : A [ r ]⊢' B} → unrestrict (♯R' {α = 1m} D) ≈ UR {α = r} {β = 1m} (unrestrict D)
  unrestrict♯R1 with 1-cell-case 1m
  ...   | Inl id = id
  ...   | Inr q = 1≠r q 

  unrestrict♯Rr : ∀ {A B} {D : A [ r ]⊢' B} → unrestrict (♯R' {α = r} D) ≈ UR {α = r} {β = r} (unrestrict D)
  unrestrict♯Rr with 1-cell-case r
  ...   | Inl q = 1≠r (! q)
  ...   | Inr id = id

  ident-or-copy : ∀ {A α} → A [ α ]⊢' A
  ident-or-copy {α = α} with 1-cell-case α
  ident-or-copy | Inl id = ident'
  ident-or-copy | Inr id = copy'

  wlog : ∀ {A B α} → A [ α ]⊢ B → A [ α ]⊢' B
  wlog (hypp x) = ident-or-copy 
  wlog (hypq x) = ident-or-copy
  wlog {α = α} (FL {r = m} {α = α1} D) with 0-cell-case {m}
  wlog {α = α} (FL {α = α1} D) | id with 1-cell-case α1
  wlog (FL D) | id | Inl id = {! F1L' (wlog D) !}
  wlog (FL D) | id | Inr id = cut' (♭L' (transport (λ x → _ [ x ]⊢' _) (r∘ _) (wlog D))) ident-or-copy
  wlog {α = α} (FR {q = q} {α = α1} γ e D) with 0-cell-case {q}
  wlog {α = α} (FR {α = α1} γ e D) | id with 1-cell-case α1 | 1-cell-case γ | 1-cell-case α
  wlog (FR .1m e D) | id | Inl id | Inl id | Inl id = {! F1R' (wlog D) !}
  wlog (FR .1m e D) | id | Inl id | Inl id | Inr id = {! F1R' (trunit' id (wlog D)) !}
  wlog (FR .r e D) | id | Inl id | Inr id | Inl id = r⇒/1 e
  wlog (FR .r e D) | id | Inl id | Inr id | Inr id = {! F1R' (wlog D) !}
  wlog (FR .1m e D) | id | Inr id | Inl id | Inl id = r⇒/1 e
  wlog (FR .1m e D) | id | Inr id | Inl id | Inr id = ♭R' (cut' copy' (wlog D))
  wlog (FR .r e D) | id | Inr id | Inr id | Inl id = r⇒/1 e
  wlog (FR .r e D) | id | Inr id | Inr id | Inr id = ♭R' (wlog D)
  wlog {α = α} (UL {q = q} {α = α1} γ e D) with 0-cell-case {q} 
  wlog {α = α} (UL {α = α1} γ e D) | id with 1-cell-case α | 1-cell-case α1 | 1-cell-case γ 
  wlog (UL .1m e D) | id | Inl id | Inl id | Inl id = {! U1L' (wlog D) !}
  wlog (UL .r e D) | id | Inl id | Inl id | Inr id = r⇒/1 e
  wlog (UL .1m e D) | id | Inl id | Inr id | Inl id = r⇒/1 e
  wlog (UL .r e D) | id | Inl id | Inr id | Inr id = r⇒/1 e
  wlog (UL .1m e D) | id | Inr id | Inl id | Inl id = {! U1L' (trunit' id (wlog D)) !}
  wlog (UL .r e D) | id | Inr id | Inl id | Inr id = {! U1L' (wlog D) !}
  wlog (UL .1m e D) | id | Inr id | Inr id | Inl id = ♯L' (cut' copy' (wlog D))
  wlog (UL .r e D) | id | Inr id | Inr id | Inr id = ♯L' (wlog D)
  wlog (UR {p = p} {α = α} D) with 0-cell-case {p}
  wlog (UR {α = α₁} D) | id with 1-cell-case α₁ 
  wlog (UR D) | id | Inl id = {! U1R' (wlog D) !}
  wlog {α = α} (UR D) | id | Inr id = ♯R' (transport (λ x → _ [ x ]⊢' _) (∘r _) (wlog D))
  wlog (Inl D) = Inl' (wlog D)
  wlog (Inr D) = Inr' (wlog D)
  wlog {α = α} (Case D D₁) with 1-cell-case α
  wlog (Case D D₁) | Inl id = Case' (wlog D) (wlog D₁)
  wlog (Case D D₁) | Inr id = Case'r (wlog D) (wlog D₁) copy'

  unrest-wlog : ∀ {A B α} → (D : A [ α ]⊢ B) → unrestrict (wlog D) ≈ D
  unrest-wlog {α = α} (hypp x) with 1-cell-case α
  unrest-wlog (hypp x) | Inl id = !≈ (eq (ap hypp (2-cell-case-loop x)))
  unrest-wlog (hypp x) | Inr id = !≈ (eq (ap hypp (2-cell-case1r x)))
  unrest-wlog {α = α} (hypq x) with 1-cell-case α
  unrest-wlog (hypq x) | Inl id = !≈ (eq (ap hypq (2-cell-case-loop x)))
  unrest-wlog (hypq x) | Inr id = !≈ (eq (ap hypq (2-cell-case1r x)))
  unrest-wlog (Inl D) = Inl≈ (unrest-wlog D)
  unrest-wlog (Inr D) = Inr≈ (unrest-wlog D)
  unrest-wlog {α = α} (Case D D₁) with 1-cell-case α
  unrest-wlog (Case D D₁) | Inl id = Case≈ (unrest-wlog D) (unrest-wlog D₁)
  unrest-wlog (Case D D₁) | Inr id with 1-cell-case 1m 
  ... | Inl id = Case≈ ((unrest-wlog D ∘≈ cut-r-copy _) ∘≈ eq (transport⊢1 _)) ((unrest-wlog D₁ ∘≈ cut-r-copy _) ∘≈ eq (transport⊢1 _))
  ... | Inr q = 1≠r q
  -- CASE
  unrest-wlog {α = α} (FL {r = m} {α = α1} D) with 0-cell-case {m}
  unrest-wlog {α = α} (FL {α = α1} D) | id with 1-cell-case α1
  unrest-wlog {α = α} (FL D) | id | Inl id = {! F1U1 !}
  unrest-wlog {α = α} (FL D) | id | Inr id with 1-cell-case α
  unrest-wlog (FL D) | id | Inr id | Inl id = FL≈ {α = r} {β = 1m} (unrest-wlog D) ∘≈ cut-ident-right (♭L1 (unrestrict (wlog D))) 
  unrest-wlog (FL D) | id | Inr id | Inr id = (FL≈ {α = r} {β = r} (cut-r-copy D) ∘≈ cutFL {α = r} {β = 1m} {D = D} copy) ∘≈ cut≈1 (FL≈ {α = r} {β = 1m} (unrest-wlog D)) copy
  -- CASE
  unrest-wlog {α = α} (FR {q = q} {α = α1} γ e D) with 0-cell-case {q}
  unrest-wlog {α = α} (FR {α = α1} γ e D) | id with 1-cell-case α1 | 1-cell-case γ | 1-cell-case α
  unrest-wlog (FR .1m e D) | id | Inl id | Inl id | Inl id = {!F1U1 !}
  unrest-wlog (FR .1m e D) | id | Inl id | Inl id | Inr id = {!F1U1!}
  unrest-wlog (FR .r e D) | id | Inl id | Inr id | Inl id = r⇒/1 e
  unrest-wlog (FR .r e D) | id | Inl id | Inr id | Inr id = {! F1U1 !}
  unrest-wlog (FR .1m e D) | id | Inr id | Inl id | Inl id = r⇒/1 e
  -- interesting case
  unrest-wlog (FR .1m e D) | id | Inr id | Inl id | Inr id = FR2 {α = r} {β = r} {γ = r} {γ' = 1m} {e = 1⇒} {e' = e} {D = unrestrict (cut' copy' (wlog D))}
                                                               {D' = D} runit (! (2-cell-case-loop e) ∘ adjeq1) (((transport⊢≈ runit (cut-ident-left D) ∘≈ !≈ (transport⊢cut2 {e1 = runit} hyp D)) ∘≈ cut≈2 copy (unrest-wlog D)))
  unrest-wlog (FR .r e D) | id | Inr id | Inr id | Inl id = r⇒/1 e
  unrest-wlog (FR .r e D) | id | Inr id | Inr id | Inr id = eq (ap (λ x → FR {α = r} r x D) (! (2-cell-case-loop e))) ∘≈ FR≈ (unrest-wlog D)
  -- CASE
  unrest-wlog {α = α} (UL {q = q} {α = α1} γ e D) with 0-cell-case {q} 
  unrest-wlog {α = α} (UL {α = α1} γ e D) | id with 1-cell-case α | 1-cell-case α1 | 1-cell-case γ 
  unrest-wlog (UL .1m e D) | id | Inl id | Inl id | Inl id = {! F1U1 !}
  unrest-wlog (UL .r e D) | id | Inl id | Inl id | Inr id = r⇒/1 e
  unrest-wlog (UL .1m e D) | id | Inl id | Inr id | Inl id = r⇒/1 e
  unrest-wlog (UL .r e D) | id | Inl id | Inr id | Inr id = r⇒/1 e
  -- interesting case
  unrest-wlog (UL .1m e D) | id | Inr id | Inl id | Inl id = {!F1U1!}
  unrest-wlog (UL .r e D) | id | Inr id | Inl id | Inr id = {!F1U1 !}
  -- interesting case
  unrest-wlog (UL .1m e D) | id | Inr id | Inr id | Inl id = UL2 {α = r} {β = r} {γ = r} {γ' = 1m} {e = 1⇒} {e' = e} {D = unrestrict (cut' copy' (wlog D))} {D' = D} runit (! (2-cell-case-loop e) ∘ adjeq2) (((transport⊢≈ runit (cut-ident-left D) ∘≈ !≈ (transport⊢cut2 {e1 = runit} hyp D)) ∘≈ cut≈2 copy (unrest-wlog D)))
  unrest-wlog (UL .r e D) | id | Inr id | Inr id | Inr id = eq (ap (λ x → UL {α = r} r x D) (! (2-cell-case-loop e))) ∘≈ UL≈ (unrest-wlog D)
  -- CASE
  unrest-wlog (UR {p = p} {α = α} D) with 0-cell-case {p}
  unrest-wlog (UR {α = α₁} D) | id with 1-cell-case α₁ 
  unrest-wlog (UR D) | id | Inl id = {! F1U1 !}
  unrest-wlog {α = α} (UR D) | id | Inr id with 1-cell-case α
  unrest-wlog (UR D) | id | Inr id | Inl id = UR≈ {α = r} {β = 1m} (unrest-wlog D)
  unrest-wlog (UR D) | id | Inr id | Inr id = UR≈ {α = r} {β = r} (unrest-wlog D)

  -- ----------------------------------------------------------------------
  -- canonical/atomic natural deduction

  mutual
    data _[_]⊢nd_ : Tp c → (c ≥ c) → Tp c → Set where
      cv : ∀ {A} → A [ r ]⊢nd A
      v  : ∀ {A} → A [ 1m ]⊢nd A
      ♯E : ∀ { A C} → C [ r ]⊢nd ♯ A → C [ r ]⊢nd A
      ♭rec : ∀ {A B C α} → C [ α ]⊢nd ♭ A → A [ r ]⊢nd B → C [ α ]⊢nd B -- substituting crisp var for var breaks if we don't have the α here
      Case : ∀ {C D A B α} → C [ α ]⊢nd (A ⊕ B) → A [ 1m ]⊢nd D → B [ 1m ]⊢nd D → C [ α ]⊢nd D -- substituting crisp var for var breaks if we don't have the α here
      ♯I : ∀ { A B α } → A [ r ]⊢nd B → A [ α ]⊢nd ♯ B -- not restricted
      ♭I : ∀ {A B} → A [ r ]⊢nd B → A [ r ]⊢nd ♭ B
      Inl : ∀ {α C A B} → C [ α ]⊢nd A → C [ α ]⊢nd (A ⊕ B)
      Inr : ∀ {α C A B} → C [ α ]⊢nd B → C [ α ]⊢nd (A ⊕ B)

  -- not used for anything, but provable
  Caser : ∀ {C D A B} → C [ r ]⊢nd (A ⊕ B) → A [ r ]⊢nd D → B [ r ]⊢nd D → C [ r ]⊢nd D
  Caser D D1 D2 = ♯E (Case D (♯I D1) (♯I D2))

  -- substituting a crisp var for a cohesive one
  substvv : ∀ {α A B} → α == 1m → A [ α ]⊢nd B → A [ r ]⊢nd B
  substvv p cv = 1≠r (! p)
  substvv p v = cv
  substvv p (♯E D) = 1≠r (! p)
  substvv p (♭rec D D1) = ♭rec (substvv p D) D1
  substvv p (Case D D1 D2) = Case (substvv p D) D1 D2
  substvv p (♯I D) = ♯I D
  substvv p (♭I D) = ♭I D
  substvv p (Inl D) = Inl (substvv p D)
  substvv p (Inr D) = Inr (substvv p D)

  -- substituting an atomic term for a variable
  subst : ∀ {α : c ≥ c} {β : c ≥ c} {A : Tp c} {B : Tp c} {C : Tp c}
            → A [ β ]⊢nd B
            → B [ α ]⊢nd C
            → A [ β ∘1 α ]⊢nd C
  subst {β = β} D cv with 1-cell-case β 
  subst D cv | Inl id = substvv id D
  subst D cv | Inr id = D
  subst D v = D
  subst D (♯E E) = transport (λ x → _ [ x ]⊢nd _) (! (∘r _)) (♯E (transport (λ x → _ [ x ]⊢nd _) (∘r _) (subst D E)))
  subst D (♭rec E E') = ♭rec (subst D E) E'
  subst D (Case E E1 E2) = Case (subst D E) E1 E2
  subst {α = α} D (♯I E) = ♯I (transport (λ x → _ [ x ]⊢nd _) (∘r _) (subst D E))
  subst D (♭I E) = transport (λ x → _ [ x ]⊢nd _) (! (∘r _)) (♭I (transport (λ x → _ [ x ]⊢nd _) (∘r _) (subst D E)))
  subst D (Inl E) = Inl (subst D E)
  subst D (Inr E) = Inr (subst D E)

  -- ----------------------------------------------------------------------
  -- translations between sequent calc and natural deduction

  toseq : ∀ {α A B} → A [ α ]⊢nd B → A [ α ]⊢' B
  toseq cv = copy'
  toseq v = ident'
  toseq (♯E D) = cut' (toseq D) (♯L' copy') 
  toseq (♭rec D D1) = cut' {α = 1m} (toseq D) (♭L' (toseq D1))
  toseq (Case D D1 D2) = cut' (toseq D) (Case' (toseq D1) (toseq D2))
  toseq (♯I D) = ♯R' (toseq D)
  toseq (♭I D) = ♭R' (toseq D)
  toseq (Inl D) = Inl' (toseq D)
  toseq (Inr D) = Inr' (toseq D) 

  tond : ∀ {α A B} → A [ α ]⊢' B → A [ α ]⊢nd B 
  tond copy' = cv
  tond ident' = v
  tond (cut' D E) = subst (tond D) (tond E)
  tond (♯R' D) = ♯I (tond D)
  tond (♭R' D) = ♭I (tond D)
  tond (Inl' D) = Inl (tond D)
  tond (Inr' D) = Inr (tond D)
  tond (♯L' D) = subst (♯E cv) (tond D) 
  tond (♭L' D1) = (♭rec v (tond D1)) 
  tond {A = A1 ⊕ A2} {B = B} (Case' D1 D2) = (Case v (tond D1) (tond D2)) 

  toseq-substvv : ∀ {A B α} (D : A [ α ]⊢nd B) (p : α == 1m) 
                  → unrestrict (toseq (substvv p D)) ≈ transport⊢ runit (transport (λ x → _ [ x ]⊢ _) p (unrestrict (toseq D)))
  toseq-substvv cv p = 1≠r (! p)
  toseq-substvv v id = id
  toseq-substvv (♯E D) p = 1≠r (! p)
  toseq-substvv (♭rec D D') id = !≈ (transport⊢cut2 {e1 = runit} (unrestrict (toseq D)) (FL {α = r} {β = 1m} (unrestrict (toseq D')))) ∘≈ cut≈1 (toseq-substvv D id) (♭L1 (unrestrict (toseq D')))
  toseq-substvv (Case D D1 D2) id = !≈ (transport⊢cut2 {e1 = runit} (unrestrict (toseq D)) (Case (unrestrict (toseq D1)) (unrestrict (toseq D2)))) ∘≈ cut≈1 (toseq-substvv D id) (Case (unrestrict (toseq D1)) (unrestrict (toseq D2)))
  toseq-substvv (♯I D) id = (!≈ (transport⊢≈ runit unrestrict♯R1) ∘≈ UR≈ {α = r} {β = r} (!≈ (eq (transport⊢1 _) ∘≈ eq (ap (λ x → transport⊢ x (unrestrict (toseq D))) adjeq1)))) ∘≈ unrestrict♯Rr
  toseq-substvv (♭I D) p = 1≠r (! p)
  toseq-substvv (Inl D) id = Inl≈ (toseq-substvv D id)
  toseq-substvv (Inr D) id = Inr≈ (toseq-substvv D id)

  -- FIXME this is definitional now; eliminate in the proofs below
  unrestrict-cut' : ∀ {α : c ≥ c} {β : c ≥ c} {A : Tp c} {B : Tp c} {C : Tp c}
       (D : A [ β ]⊢' B) (E : B [ α ]⊢' C) →
       unrestrict (cut' D E) ≈ cut (unrestrict D) (unrestrict E)
  unrestrict-cut' D E = id

  toseq-subst : ∀ {α : c ≥ c} {β : c ≥ c} {A : Tp c} {B : Tp c} {C : Tp c}
            (D : A [ β ]⊢nd B) (E : B [ α ]⊢nd C) →
            unrestrict (toseq (subst D E)) ≈ unrestrict(cut' (toseq D) (toseq E))
  toseq-subst {β = β} D cv with 1-cell-case β
  toseq-subst D cv | Inl id = !≈ (!≈ ((transport⊢cut1 {e2 = runit} (unrestrict (toseq D)) hyp ∘≈ transport⊢≈ runit (!≈ (cut-ident-right (unrestrict (toseq D))))) ∘≈ toseq-substvv D id))
  toseq-subst D cv | Inr id = !≈ (cut-r-copy _)
  toseq-subst D v = !≈ (cut-ident-right _)
  toseq-subst {β = β} D (♯E E) with 1-cell-case β 
  toseq-subst D (♯E E) | Inl id = !≈ (cut-assoc (unrestrict (toseq D)) (unrestrict (toseq E)) (♯L copy)) ∘≈ cut≈1 (toseq-subst D E) (♯L copy)
  toseq-subst D (♯E E) | Inr id = !≈ ((((cut≈1 (!≈ (toseq-subst D E)) (♯L copy) ∘≈ cut≈1 ( !≈ (unrestrict-cut' (toseq D) (toseq E))) (♯L copy)) ∘≈ cut-assoc (unrestrict (toseq D)) (unrestrict (toseq E)) (♯L copy)) ∘≈ cut≈2 (unrestrict (toseq D)) (unrestrict-cut' (toseq E) (♯L' copy'))) ∘≈ unrestrict-cut' (toseq D) (cut' (toseq E) (♯L' copy'))) ∘≈ unrestrict-cut' (toseq (subst D E)) (♯L' copy')
  toseq-subst D (♭rec E E') = !≈ (cut-assoc (unrestrict (toseq D)) (unrestrict (toseq E)) (unrestrict (♭L' (toseq E')))) ∘≈ cut≈1 (toseq-subst D E) (unrestrict (♭L' (toseq E')))
  toseq-subst D (Case E1 E2 E') = cut≈2 (unrestrict (toseq D)) (cut≈2 (unrestrict (toseq E1)) (cut-ident-right (Case (unrestrict (toseq E2)) (unrestrict (toseq E'))))) ∘≈ (!≈ (cut-assoc (unrestrict (toseq D)) (unrestrict (toseq E1)) (cut (Case (unrestrict (toseq E2)) (unrestrict (toseq E'))) hyp)) ∘≈ cut≈1 (toseq-subst D E1) (cut (Case (unrestrict (toseq E2)) (unrestrict (toseq E'))) hyp)) ∘≈ cut≈2 (unrestrict (toseq (subst D E1))) (!≈ (cut-ident-right (Case (unrestrict (toseq E2)) (unrestrict (toseq E')))))
  toseq-subst {α = α} {β = β} D (♯I E) with 1-cell-case β | 1-cell-case α | 1-cell-case (β ∘1 α) 
  toseq-subst D (♯I E) | Inl id | Inl id | Inl id =  !≈ (eq (cutUR (unrestrict (toseq D)))) ∘≈ UR≈ {α = r} {β = 1m ∘1 1m} (unrestrict-cut' (toseq D) (toseq E) ∘≈ toseq-subst D E)
  toseq-subst D (♯I E) | Inl id | Inr id | Inl p = 1≠r (! p)
  toseq-subst D (♯I E) | Inr id | Inl id | Inl p = 1≠r (! p)
  toseq-subst D (♯I E) | Inr id | Inr id | Inl p = 1≠r (! p)
  toseq-subst D (♯I E) | Inl id | Inl id | Inr p = 1≠r p
  toseq-subst D (♯I E) | Inl id | Inr id | Inr id = !≈ (eq (cutUR (unrestrict (toseq D)))) ∘≈ UR≈ {α = r} {β = r} (unrestrict-cut' (toseq D) (toseq E) ∘≈ toseq-subst D E)
  toseq-subst D (♯I E) | Inr id | Inl id | Inr id = !≈ (eq (cutUR {α = 1m} {β = r} (unrestrict (toseq D)))) ∘≈ UR≈ {α = r} {β = r} (unrestrict-cut' (toseq D) (toseq E) ∘≈ toseq-subst D E)
  toseq-subst D (♯I E) | Inr id | Inr id | Inr id = !≈ (eq (cutUR {α = r} {β = r} (unrestrict (toseq D)))) ∘≈ UR≈ {α = r} {β = r} (unrestrict-cut' (toseq D) (toseq E) ∘≈ toseq-subst D E)
  toseq-subst {β = β} D (♭I E) with 1-cell-case β 
  toseq-subst D (♭I E) | Inl id = !≈ ((FR≈ (!≈ (toseq-subst D E) ∘≈ !≈ (unrestrict-cut' (toseq D) (toseq E))) ∘≈ eq (cutFR (unrestrict (toseq D)))) ∘≈ unrestrict-cut' (toseq D) (♭R' (toseq E)))
  toseq-subst D (♭I E) | Inr id with 1-cell-case r 
  ... | Inl q = 1≠r (! q)
  ... | Inr id = !≈ (unrestrict-cut' (toseq D) (♭R' (toseq E))) ∘≈ !≈ (eq (cutFR {α = r} {β = r} {α' = r} {γ = r} {e = 1⇒} (unrestrict (toseq D)))) ∘≈ FR≈ (unrestrict-cut' (toseq D) (toseq E) ∘≈ toseq-subst D E)
  toseq-subst D (Inl E) = !≈ (unrestrict-cut' (toseq D) (Inl' (toseq E))) ∘≈ !≈ (eq (cutInl (unrestrict (toseq D)))) ∘≈ Inl≈ (unrestrict-cut' (toseq D) (toseq E) ∘≈ toseq-subst D E)
  toseq-subst D (Inr E) = !≈ (unrestrict-cut' (toseq D) (Inr' (toseq E))) ∘≈ !≈ (eq (cutInr (unrestrict (toseq D)))) ∘≈ Inr≈ (unrestrict-cut' (toseq D) (toseq E) ∘≈ toseq-subst D E)

  tond-toseq : ∀ {A B α} (D : A [ α ]⊢' B) → unrestrict (toseq (tond D)) ≈ unrestrict D
  tond-toseq copy' = id
  tond-toseq ident' = id
  tond-toseq (cut' D E) = (cut≈2 (unrestrict D) (tond-toseq E) ∘≈ cut≈1 (tond-toseq D) (unrestrict (toseq (tond E)))) ∘≈ toseq-subst (tond D) (tond E)
  tond-toseq {α = α} (♯R' D) with 1-cell-case α
  tond-toseq (♯R' D) | Inl id = UR≈ {α = r} {β = 1m} (tond-toseq D) 
  tond-toseq (♯R' D) | Inr id = UR≈ {α = r} {β = r} (tond-toseq D) 
  tond-toseq (♭R' D) = FR≈ (tond-toseq D) 
  tond-toseq (Inl' D) = Inl≈ (tond-toseq D)
  tond-toseq (Inr' D) = Inr≈ (tond-toseq D) 
  tond-toseq (♯L' D) = (((((UL≈ {α = r} {β = r} (cut-ident-left (unrestrict D)) ∘≈ eq (ap (λ x → UL {α = r} {β = r} r x (cut hyp (unrestrict D))) (ap (λ x → x ∘1cong 1⇒ {_} {_} {r}) adjeq1))) ∘≈ cutUL {α = r} {β = r} {γ = 1m} (unrestrict D)) ∘≈ cut≈1 (cut-r-copy (UL {α = r} 1m (runit ∘1cong 1⇒) hyp)) (unrestrict D)) ∘≈ cut≈1 (eq (transport⊢1 (cut {α = r} {β = r} (UL {α = r} 1m (runit ∘1cong 1⇒) hyp) copy))) (unrestrict D)) ∘≈ cut≈2 (transport⊢ 1⇒ (cut {α = r} {β = r} (UL {α = r} 1m (runit ∘1cong 1⇒) hyp) copy)) (tond-toseq D)) ∘≈ toseq-subst (♯E cv) (tond D)
  tond-toseq (♭L' D) = FL≈ {α = r} {β = 1m} (tond-toseq D ∘≈ cut-ident-left (unrestrict (toseq (tond D))) ∘≈ eq (transport⊢1 _))  
  tond-toseq (Case' D₁ D₂) = Case≈ (tond-toseq D₁ ∘≈ cut-ident-left _) (tond-toseq D₂ ∘≈ cut-ident-left _)
  
  orig-to-nd : ∀ {A B α} → A [ α ]⊢ B → A [ α ]⊢nd B
  orig-to-nd D = tond (wlog D)

  nd-to-orig : ∀ {A B α} → A [ α ]⊢nd B → A [ α ]⊢ B 
  nd-to-orig D = unrestrict (toseq D)

  overall-nd : ∀ {A B α} (D : A [ α ]⊢ B) → nd-to-orig (orig-to-nd D) ≈ D
  overall-nd D = unrest-wlog D ∘≈ tond-toseq (wlog D)


{-
  -- examples

  example : (P ⊕ Q) [ r ]⊢nd (Q ⊕ P)
  example = ⊢nd⊢nd (Case cv (Inr (⊢nd⊢nd v)) (Inl (⊢nd⊢ v)))

  example' : toseq example == Case' (♯R' (Inr' copy')) (♯R' (Inl' copy')) (♯L' copy')
  example' with 1-cell-case 1m 
  example' | Inl id = id
  example' | Inr q = 1≠r q
  
  example'' : unrestrict (toseq example) ≈ Case (Inr (hypp runit)) (Inl (hypq runit))
  example'' with 1-cell-case 1m 
  example'' | Inl id with 1-cell-case 1m
  example'' | Inl id | Inl id = Case≈ (Inr≈ (eq (ap hypp runit-idemp))) (Inl≈ (eq (ap hypq runit-idemp)))
  ... | Inr q = 1≠r q
  example'' | Inr q = 1≠r q
-}
