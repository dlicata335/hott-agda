
open import adjointlogic2.Lib
open import adjointlogic2.Rules
open import adjointlogic2.Properties
open import adjointlogic2.General
open import adjointlogic2.Idempotent

module adjointlogic2.Idempotent-Subcalculus3 where

  open IdempotentMonad

  -- ----------------------------------------------------------------------
  -- restricted sequent calculus

  data _[_]⊢'_ : Tp c → (c ≥ c) → Tp c → Set where
    copy' : ∀ {A} → A [ r ]⊢' A
    ident' : ∀ {A} → A [ 1m ]⊢' A
    ♯R' : ∀ { A B α } → A [ r ]⊢' B → A [ α ]⊢' ♯ B -- not restricted
    ♯L' : ∀ { A B } → A [ r ]⊢' B → ♯ A [ r ]⊢' B
    ♭L' : ∀ {A C D α} → A [ r ]⊢' C → C [ α ]⊢' D → ♭ A [ α ]⊢' D -- builds in a cut, like →L
    ♭R' : ∀ {A B} → A [ r ]⊢' B → A [ r ]⊢' ♭ B
    Inl' : ∀ {α C A B} → C [ α ]⊢' A → C [ α ]⊢' (A ⊕ B)
    Inr' : ∀ {α C A B} → C [ α ]⊢' B → C [ α ]⊢' (A ⊕ B)
    Case' : ∀ {C D A B α} → A [ 1m ]⊢' C → B [ 1m ]⊢' C → C [ α ]⊢' D → (A ⊕ B) [ α ]⊢' D -- builds in a cut, like →L
    -- U1R' : ∀ { A B α } → A [ α ]⊢' B → A [ α ]⊢' U 1m B
    -- U1L' : ∀ { A B α } → A [ α ]⊢' B → U 1m A [ α ]⊢' B
    -- F1L' : ∀ {A B α} → A [ α ]⊢' B → F 1m A [ α ]⊢' B
    -- F1R' : ∀ {A B α} → A [ α ]⊢' B → A [ α ]⊢' F 1m B

  ♭L'r : ∀ {A B C} → A [ r ]⊢' B → B [ r ]⊢' C → ♭ A [ r ]⊢' C
  ♭L'r {A}{B} D E = ♭L' (♯R' D) (♯L' E)

  Case'r : ∀ {A B C D} → A [ r ]⊢' C → B [ r ]⊢' C → C [ r ]⊢' D → (A ⊕ B) [ r ]⊢' D
  Case'r D1 D2 E = Case' (♯R' D1) (♯R' D2) (♯L' E) 

  {- doesn't termination check with the extra cuts
  ident' : ∀ A → A [ 1m ]⊢' A
  ident' P = {!!}
  ident' Q = {!!}
  ident' (F {q = q} α A) with 0-cell-case {q} 
  ident' (F α A) | id with 1-cell-case α
  ident' (F .1m A) | id | Inl id = {!!}
  ident' (F .r A) | id | Inr id = ♭L' (♭R' copy') {! (ident' (F r A)) !}
  ident' (U {p = p} α A) with 0-cell-case {p} 
  ident' (U α A) | id with 1-cell-case α 
  ident' (U .1m A) | id | Inl id = {!!}
  ident' (U .r A) | id | Inr id = ♯R' (♯L' copy')
  ident' (A ⊕ A₁) = Case' (Inl' (ident' A)) (Inr' (ident' A₁)) (ident' (A ⊕ A₁))
  -}
  
  {- doesn't seem like it's admissible either
  copy'' : ∀ A → A [ r ]⊢' A
  copy'' P = {!!}
  copy'' Q = {!!}
  copy'' (F {q = q} α A) with 0-cell-case {q} 
  copy'' (F α A) | id with 1-cell-case α
  copy'' (F .1m A) | id | Inl id = {!!}
  copy'' (F .r A) | id | Inr id = ♭L'r (♭R' copy')
  copy'' (U α A) = {!!}
  copy'' (A ⊕ A₁) = {!!}
  -}

  ∘r : ∀ α → (α ∘1 r) == r
  ∘r α with 1-cell-case α
  ∘r .1m | Inl id = id
  ∘r .r | Inr id = id

  r∘ : ∀ α → (r ∘1 α) == r
  r∘ α with 1-cell-case α
  r∘ .1m | Inl id = id
  r∘ .r | Inr id = id

  cut' : ∀ {α : c ≥ c} {β : c ≥ c} {A : Tp c} {B : Tp c} {C : Tp c}
       → A [ β ]⊢' B
       → B [ α ]⊢' C
       → A [ β ∘1 α ]⊢' C
  -- principal 
  cut' (♭R' D) (♭L' E E') = cut' (cut' D E) E'
  cut' (♯R' D) (♯L' E) = transport (λ x → _ [ x ]⊢' _) (! (∘r _)) (cut' D E)
  cut' (Inl' D) (Case' E1 E2 E) = cut' (cut' D E1) E
  cut' (Inr' D) (Case' E1 E2 E) = cut' (cut' D E2) E
  -- ident
  cut' ident' E = E
  cut' D ident' = D
  -- copy
  cut' copy' copy' = copy'
  cut' copy' (♯R' E) = ♯R' E
  cut' copy' (♯L' E) = ♯L' E
  cut' {α = α} copy' (♭L' E E') with 1-cell-case α
  cut' copy' (♭L' E E') | Inl id = ♭L'r E (cut' copy' E')
  cut' copy' (♭L' E E') | Inr id = ♭L' E E'
  cut' copy' (♭R' E) = ♭R' E
  cut' copy' (Inl' E) = Inl' (cut' copy' E)
  cut' copy' (Inr' E) = Inr' (cut' copy' E)
  cut' {α = α} copy' (Case' E E₁ E') with 1-cell-case α
  cut' copy' (Case' E E₁ E') | Inl id = Case'r (cut' copy' E) (cut' copy' E₁) (cut' copy' E')
  cut' copy' (Case' E E₁ E') | Inr id = Case'r (cut' copy' E) (cut' copy' E₁) E'
  cut' (♯R' D) copy' = ♯R' D
  cut' (♯L' D) copy' = ♯L' D
  cut' (♭L' D D₁) copy' = ♭L' D (cut' D₁ copy')
  cut' (♭R' D) copy' = ♭R' D
  -- copy right
  cut' (Inl' D) copy' = Inl' (cut' D copy')
  cut' (Inr' D) copy' = Inr' (cut' D copy')
  cut' (Case' D₁ D₂ D₃) copy' = Case' D₁ D₂ (cut' D₃ copy')
  -- right commutative
  cut' D (♭R' E) = transport (λ x → _ [ x ]⊢' _) (! (∘r _)) (♭R' (transport (λ x → _ [ x ]⊢' _) (∘r _) (cut' D E)))
  cut' D (♯R' E) = ♯R' (transport (λ x → _ [ x ]⊢' _) (∘r _) (cut' D E))
  cut' D (Inl' E) = Inl' (cut' D E)
  cut' D (Inr' E) = Inr' (cut' D E)
  -- left commutative
  cut' (♯L' D) E = transport (λ x → _ [ x ]⊢' _) (! (r∘ _)) (♯L' (transport (λ x → _ [ x ]⊢' _) (r∘ _) (cut' D E)))
  cut' (♭L' D D') E = ♭L' D (cut' D' E)
  cut' (Case' D1 D2 D) E = Case' D1 D2 (cut' D E)

  forget : ∀ {A B α} → A [ α ]⊢' B → A [ α ]⊢ B
  forget ident' = hyp
  forget copy' = copy
  forget {α = α} (♯R' D) with 1-cell-case α
  forget (♯R' D) | Inl id = ♯R1 (forget D)
  forget (♯R' D) | Inr id = ♯Rr (forget D)
  forget (♯L' D) = ♯L (forget D)
  forget {α = α} (♭L' D E) with 1-cell-case α
  forget (♭L' D E) | Inl id = cut (♭L1 (forget D)) (forget E)
  forget (♭L' D E) | Inr id = cut (♭Lr (forget D)) (forget E)
  forget (♭R' D) = ♭R (forget D)
  forget (Inl' D) = Inl (forget D)
  forget (Inr' D) = Inr (forget D)
  forget (Case' D D₁ E) = cut (Case (forget D) (forget D₁)) (forget E)
  -- forget (U1R' D) = UR {α = 1m} (forget D)
  -- forget {α = α} (U1L' D) = UL {α = 1m} {β = α} α 1⇒ (forget D)
  -- forget (F1L' D) = FL {α = 1m} (forget D)
  -- forget {α = α} (F1R' D) = FR {α = 1m} {β = α} α 1⇒ (forget D)

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
  wlog (FL D) | id | Inr id = ♭L' (transport (λ x → _ [ x ]⊢' _) (r∘ _) (wlog D)) ident-or-copy
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
  wlog (Case D D₁) | Inl id = Case' (wlog D) (wlog D₁) ident'
  wlog (Case D D₁) | Inr id = Case'r (wlog D) (wlog D₁) copy'

  -- ----------------------------------------------------------------------
  -- canonical/atomic natural deduction

  mutual
    data _[_]⇓_ : Tp c → (c ≥ c) → Tp c → Set where
      cv : ∀ {A} → A [ r ]⇓ A
      v  : ∀ {A} → A [ 1m ]⇓ A
      ♯E : ∀ { A C} → C [ r ]⇓ ♯ A → C [ r ]⇓ A
      ♭rec : ∀ {A B C α} → C [ α ]⇓ ♭ A → A [ r ]⇑ B → C [ α ]⇓ B -- substituting crisp var for var breaks if we don't have the α here
      Case : ∀ {C D A B α} → C [ α ]⇓ (A ⊕ B) → A [ 1m ]⇑ D → B [ 1m ]⇑ D → C [ α ]⇓ D -- substituting crisp var for var breaks if we don't have the α here

    data _[_]⇑_ : Tp c → (c ≥ c) → Tp c → Set where
      ⇓⇑ : ∀ {A C α} → A [ α ]⇓ C → A [ α ]⇑ C
      ♯I : ∀ { A B α } → A [ r ]⇑ B → A [ α ]⇑ ♯ B -- not restricted
      ♭I : ∀ {A B} → A [ r ]⇑ B → A [ r ]⇑ ♭ B
      Inl : ∀ {α C A B} → C [ α ]⇑ A → C [ α ]⇑ (A ⊕ B)
      Inr : ∀ {α C A B} → C [ α ]⇑ B → C [ α ]⇑ (A ⊕ B)

  Caser : ∀ {C D A B} → C [ r ]⇓ (A ⊕ B) → A [ r ]⇑ D → B [ r ]⇑ D → C [ r ]⇓ D
  Caser D D1 D2 = ♯E (Case D (♯I D1) (♯I D2))

  -- substituting a crisp var for a cohesive one
  substvva : ∀ {α A B} → α == 1m → A [ α ]⇓ B → A [ r ]⇓ B
  substvva p cv = 1≠r (! p)
  substvva p v = cv
  substvva p (♯E D) = 1≠r (! p)
  substvva p (♭rec D D1) = ♭rec (substvva p D) D1
  substvva p (Case D D1 D2) = Case (substvva p D) D1 D2

  substvvc : ∀ {α A B} → α == 1m → A [ α ]⇑ B → A [ r ]⇑ B
  substvvc p (⇓⇑ x) = ⇓⇑ (substvva p x)
  substvvc p (♯I D) = ♯I D
  substvvc p (♭I D) = ♭I D
  substvvc p (Inl D) = Inl (substvvc p D)
  substvvc p (Inr D) = Inr (substvvc p D)

  -- substituting an atomic term for a variable
  substaa : ∀ {α : c ≥ c} {β : c ≥ c} {A : Tp c} {B : Tp c} {C : Tp c}
            → A [ β ]⇓ B
            → B [ α ]⇓ C
            → A [ β ∘1 α ]⇓ C
  substaa {β = β} D cv with 1-cell-case β 
  substaa D cv | Inl id = substvva id D
  substaa D cv | Inr id = D
  substaa D v = D
  substaa D (♯E E) = transport (λ x → _ [ x ]⇓ _) (! (∘r _)) (♯E (transport (λ x → _ [ x ]⇓ _) (∘r _) (substaa D E)))
  substaa D (♭rec E E') = ♭rec (substaa D E) E'
  substaa D (Case E E1 E2) = Case (substaa D E) E1 E2

  substac : ∀ {α : c ≥ c} {β : c ≥ c} {A : Tp c} {B : Tp c} {C : Tp c}
            → A [ β ]⇓ B
            → B [ α ]⇑ C
            → A [ β ∘1 α ]⇑ C
  substac D (⇓⇑ E) = ⇓⇑ (substaa D E)
  substac {α = α} D (♯I E) = ♯I (transport (λ x → _ [ x ]⇑ _) (∘r _) (substac D E))
  substac D (♭I E) = transport (λ x → _ [ x ]⇑ _) (! (∘r _)) (♭I (transport (λ x → _ [ x ]⇑ _) (∘r _) (substac D E)))
  substac D (Inl E) = Inl (substac D E)
  substac D (Inr E) = Inr (substac D E)

  ♭R1inv : ∀ {C A α} → α == 1m → C [ α ]⇑ ♭ A → C [ α ]⇓ ♭ A
  ♭R1inv p (⇓⇑ D) = D
  ♭R1inv p (♭I D) = 1≠r (! p)

  mutual
    hsubstca : ∀ {α : c ≥ c} {β : c ≥ c} {A : Tp c} {B : Tp c} {C : Tp c}
            → A [ β ]⇑ B
            → B [ α ]⇓ C
            → A [ β ∘1 α ]⇑ C
    hsubstca {β = β} D cv with 1-cell-case β 
    hsubstca D cv | Inl id = substvvc id D
    hsubstca D cv | Inr id = D
    hsubstca D v = D
    hsubstca D (♯E E) with hsubstca D E
    ... | ⇓⇑ D' = transport (λ x → _ [ x ]⇑ _) (! (∘r _)) (⇓⇑ (♯E (transport (λ x → _ [ x ]⇓ _) (∘r _) D')))
    ... | ♯I D' = transport (λ x → _ [ x ]⇑ _) (! (∘r _)) D'
    hsubstca {α = α} {β = β} D (♭rec E E1) with 1-cell-case α | 1-cell-case β | hsubstca D E
    hsubstca D (♭rec E E1) | Inl id | Inl id | E' = ⇓⇑ (♭rec (♭R1inv id E') E1) 
    hsubstca D (♭rec E E1) | Inl id | Inr id | ⇓⇑ E' = ⇓⇑ (♭rec E' E1) -- FIXME: could use a lemma to avoid the code duplication
    hsubstca D (♭rec E E1) | Inl id | Inr id | ♭I E' = hsubstcc E' E1
    hsubstca D (♭rec E E1) | Inr id | Inl id | ⇓⇑ E' = ⇓⇑ (♭rec E' E1)
    hsubstca D (♭rec E E1) | Inr id | Inl id | ♭I E' = hsubstcc E' E1
    hsubstca D (♭rec E E1) | Inr id | Inr id | ⇓⇑ E' = ⇓⇑ (♭rec E' E1)
    hsubstca D (♭rec E E1) | Inr id | Inr id | ♭I E' = hsubstcc E' E1
    hsubstca D (Case E E1 E2) with hsubstca D E
    ... | ⇓⇑ E' = ⇓⇑ (Case E' E1 E2)
    ... | Inl E' = hsubstcc E' E1
    ... | Inr E' = hsubstcc E' E2

    hsubstcc : ∀ {α : c ≥ c} {β : c ≥ c} {A : Tp c} {B : Tp c} {C : Tp c}
            → A [ β ]⇑ B
            → B [ α ]⇑ C
            → A [ β ∘1 α ]⇑ C
    hsubstcc D (⇓⇑ E) = hsubstca D E
    hsubstcc D (♯I E) = ♯I (transport (λ x → _ [ x ]⇑ _) (∘r _) (hsubstcc D E))
    hsubstcc D (♭I E) = transport (λ x → _ [ x ]⇑ _) (! (∘r _)) (♭I (transport (λ x → _ [ x ]⇑ _) (∘r _) (hsubstcc D E)))
    hsubstcc D (Inl E) = Inl (hsubstcc D E)
    hsubstcc D (Inr E) = Inr (hsubstcc D E)

  -- ----------------------------------------------------------------------
  -- translations between sequent calc and natural deduction

  mutual
    toseqa : ∀ {α A B} → A [ α ]⇓ B → A [ α ]⊢' B
    toseqa cv = copy'
    toseqa v = ident'
    toseqa (♯E D) = cut' (toseqa D) (♯L' copy') -- FIXME how bad are these cuts?
    toseqa (♭rec D D1) = cut' {α = 1m} (toseqa D) (♭L' (toseqc D1) ident')
    toseqa (Case D D1 D2) = cut' (toseqa D) (Case' (toseqc D1) (toseqc D2) ident')

    toseqc : ∀ {α A B} → A [ α ]⇑ B → A [ α ]⊢' B
    toseqc (⇓⇑ D) = toseqa D
    toseqc (♯I D) = ♯R' (toseqc D)
    toseqc (♭I D) = ♭R' (toseqc D)
    toseqc (Inl D) = Inl' (toseqc D)
    toseqc (Inr D) = Inr' (toseqc D) 

  tond : ∀ {α A B} → A [ α ]⊢' B → A [ α ]⇑ B 
  tond copy' = ⇓⇑ cv
  tond ident' = ⇓⇑ v
  tond (♯R' D) = ♯I (tond D)
  tond (♭R' D) = ♭I (tond D)
  tond (Inl' D) = Inl (tond D)
  tond (Inr' D) = Inr (tond D)
  tond (♯L' D) = substac (♯E cv) (tond D) 
  tond (♭L' D1 E) = substac (♭rec v (tond D1)) (tond E)
  tond {A = A1 ⊕ A2} {B = B} (Case' D1 D2 E) = substac (Case v (tond D1) (tond D2)) (tond E) 
