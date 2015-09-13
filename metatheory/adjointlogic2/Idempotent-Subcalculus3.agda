
open import adjointlogic2.Lib
open import adjointlogic2.Rules
open import adjointlogic2.Properties
open import adjointlogic2.General
open import adjointlogic2.Idempotent

module adjointlogic2.Idempotent-Subcalculus3 where

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

  -- ident and copy are not admissible in general, 
  -- but they could be restricted to positives, and admissible for negatives:
  copy♯ : ∀ {A} → ♯ A [ r ]⊢' ♯ A
  copy♯ = ♯R' (♯L' copy')

  ident♯ : ∀ {A} → ♯ A [ 1m ]⊢' ♯ A
  ident♯ = ♯R' (♯L' copy')

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

  unrestrict : ∀ {A B α} → A [ α ]⊢' B → A [ α ]⊢ B
  unrestrict ident' = hyp
  unrestrict copy' = copy
  unrestrict {α = α} (♯R' D) with 1-cell-case α
  unrestrict (♯R' D) | Inl id = ♯R1 (unrestrict D)
  unrestrict (♯R' D) | Inr id = ♯Rr (unrestrict D)
  unrestrict (♯L' D) = ♯L (unrestrict D)
  unrestrict {α = α} (♭L' D E) with 1-cell-case α
  unrestrict (♭L' D E) | Inl id = cut (♭L1 (unrestrict D)) (unrestrict E)
  unrestrict (♭L' D E) | Inr id = cut (♭Lr (unrestrict D)) (unrestrict E)
  unrestrict (♭R' D) = ♭R (unrestrict D)
  unrestrict (Inl' D) = Inl (unrestrict D)
  unrestrict (Inr' D) = Inr (unrestrict D)
  unrestrict (Case' D D₁ E) = cut (Case (unrestrict D) (unrestrict D₁)) (unrestrict E)
  -- unrestrict (U1R' D) = UR {α = 1m} (unrestrict D)
  -- unrestrict {α = α} (U1L' D) = UL {α = 1m} {β = α} α 1⇒ (unrestrict D)
  -- unrestrict (F1L' D) = FL {α = 1m} (unrestrict D)
  -- unrestrict {α = α} (F1R' D) = FR {α = 1m} {β = α} α 1⇒ (unrestrict D)

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

  unrestrict♯R1 : ∀ {A B} {D : A [ r ]⊢' B} → unrestrict (♯R' {α = 1m} D) ≈ UR {α = r} {β = 1m} (unrestrict D)
  unrestrict♯R1 with 1-cell-case 1m
  ...   | Inl id = id
  ...   | Inr q = 1≠r q 

  unrestrict♯Rr : ∀ {A B} {D : A [ r ]⊢' B} → unrestrict (♯R' {α = r} D) ≈ UR {α = r} {β = r} (unrestrict D)
  unrestrict♯Rr with 1-cell-case r
  ...   | Inl q = 1≠r (! q)
  ...   | Inr id = id

  unrestrict♭L1 : ∀ {A B C} {D : A [ r ]⊢' B} {E : B [ 1m ]⊢' C} 
               → unrestrict (♭L' {α = 1m} D E) ≈ cut (FL {α = r} {β = 1m} (unrestrict D)) (unrestrict E)
  unrestrict♭L1 with 1-cell-case 1m
  ...   | Inl id = id
  ...   | Inr q = 1≠r q 

  unrestrict♭Lr : ∀ {A B C} {D : A [ r ]⊢' B} {E : B [ r ]⊢' C} 
               → unrestrict (♭L' {α = r} D E) ≈ cut (FL {α = r} {β = r} (unrestrict D)) (unrestrict E)
  unrestrict♭Lr with 1-cell-case 1m
  ...   | Inl id = id
  ...   | Inr q = 1≠r q 

  unrestrict-cut' : ∀ {α : c ≥ c} {β : c ≥ c} {A : Tp c} {B : Tp c} {C : Tp c}
       (D : A [ β ]⊢' B) (E : B [ α ]⊢' C) →
       unrestrict (cut' D E) ≈ cut (unrestrict D) (unrestrict E)
{-
  -- quadratic case split to get things to reduce, but a lot of overlap
  -- copy cases 
  unrestrict-cut' copy' copy' = !≈ copy-idempotent
  unrestrict-cut' copy' ident' = !≈ (cut-ident-right copy)
  unrestrict-cut' {α = α} copy' (♯R' E) with 1-cell-case α | 1-cell-case (r ∘1 α)
  unrestrict-cut' copy' (♯R' E) | Inl id | Inl q = 1≠r (! q)
  unrestrict-cut' copy' (♯R' E) | Inl id | Inr id = !≈ (eq (cutUR {α = 1m} {β = r} copy {E = unrestrict E})) ∘≈ UR≈ {α = r} {β = r} (!≈ (cut-copy-r (unrestrict E)))
  unrestrict-cut' copy' (♯R' E) | Inr id | Inl q = 1≠r (! q)
  unrestrict-cut' copy' (♯R' E) | Inr id | Inr id = !≈ (cut-copy-r (UR {α = r} {β = r} (unrestrict E)))
  unrestrict-cut' copy' (♯L' E) = !≈ (((UL≈ (cut-ident-left (unrestrict E)) ∘≈ eq (ap (λ x → UL {α = r} {β = r} r x (cut hyp (unrestrict E))) (ap (λ x → x ∘1cong 1⇒ {_} {_} {r}) adjeq1))) ∘≈ cutUL {α = r} {β = r} {α₁ = r} {γ = 1m} (unrestrict E)) ∘≈ eq (transport⊢1 _))
  unrestrict-cut' {α = α} copy' (♭L' E E₁) with 1-cell-case α
  unrestrict-cut' copy' (♭L' E E₁) | Inl id = (!≈ (cutFL {D = FR 1m (1⇒ ∘1cong runit) hyp} (cut (FL {α = r} {β = 1m} (unrestrict E)) (unrestrict E₁))) ∘≈ FL≈ {α = r} {β = r ∘1 (1m ∘1 1m)} (((!≈ (cut-assoc (FR 1m (1⇒ ∘1cong runit) hyp) (FL {α = r} {β = 1m} (unrestrict E)) (unrestrict E₁)) ∘≈ !≈ (cut≈1 (cut-ident-left (unrestrict E) ∘≈ eq (transport⊢1 _) ∘≈ eq (ap (λ x → transport⊢ x (cut hyp (unrestrict E))) adjeq2)) (unrestrict E₁)) ∘≈ (cut≈1 (cut-r-copy (unrestrict E)) (unrestrict E₁) ∘≈ cut-assoc (unrestrict E) copy (unrestrict E₁)) ∘≈ cut≈2 (unrestrict E) (unrestrict-cut' copy' E₁)) ∘≈ eq (transport⊢1 _)) ∘≈ cut≈1 unrestrict♯Rr (UL r 1⇒ (unrestrict (cut' copy' E₁))))) ∘≈ unrestrict♭Lr
  unrestrict-cut' copy' (♭L' E E₁) | Inr id = (!≈ (cut-assoc (FL (FR 1m (1⇒ ∘1cong runit) hyp)) (FL {α = r} {β = r} (unrestrict E)) (unrestrict E₁)) ∘≈ cut≈1 (!≈ (FL≈ {α = r} {β = r} (cut-ident-left (unrestrict E) ∘≈ eq (transport⊢1 _) ∘≈ eq (ap (λ x → transport⊢ x (cut hyp (unrestrict E))) (ap (λ x → x ∘1cong 1⇒ {_} {_} {r}) adjeq2))))) (unrestrict E₁)) ∘≈ unrestrict♭Lr
  unrestrict-cut' copy' (♭R' E) = !≈ (cut-copy-r _)
  unrestrict-cut' copy' (Inl' E) = !≈ (eq (cutInl copy)) ∘≈ Inl≈ (unrestrict-cut' copy' E)
  unrestrict-cut' copy' (Inr' E) = !≈ (eq (cutInr copy)) ∘≈ Inr≈ (unrestrict-cut' copy' E)
  unrestrict-cut' {α = α} copy' (Case' E E₁ E₂) with 1-cell-case α 
  unrestrict-cut' copy' (Case' E E₁ E₂) | Inl id = !≈ (cutCase (cut (Case (unrestrict E) (unrestrict E₁)) (unrestrict E₂))) ∘≈ !≈ (Case≈ (cut-assoc (Inl copy) (Case (unrestrict E) (unrestrict E₁)) (unrestrict E₂)) (cut-assoc (Inr copy) (Case (unrestrict E) (unrestrict E₁)) (unrestrict E₂))) ∘≈ (Case≈ ((cut≈1 (cut-r-copy (cut copy (unrestrict E))) (unrestrict E₂) ∘≈ cut-assoc (cut copy (unrestrict E)) copy (unrestrict E₂)) ∘≈ cut≈1 (unrestrict-cut' copy' E) (cut copy (unrestrict E₂))) ((cut≈1 (cut-r-copy (cut copy (unrestrict E₁))) (unrestrict E₂) ∘≈ cut-assoc (cut copy (unrestrict E₁)) copy (unrestrict E₂)) ∘≈ cut≈1 (unrestrict-cut' copy' E₁) (cut copy (unrestrict E₂))) ∘≈ Case≈ (cut≈2 (unrestrict (cut' copy' E)) (unrestrict-cut' copy' E₂) ∘≈ eq (transport⊢1 _)) (cut≈2 (unrestrict (cut' copy' E₁)) (unrestrict-cut' copy' E₂) ∘≈ eq (transport⊢1 _))) ∘≈ Case≈ (cut≈1 unrestrict♯R1 (UL r 1⇒ (unrestrict (cut' copy' E₂)))) (cut≈1 unrestrict♯R1 (UL r 1⇒ (unrestrict (cut' copy' E₂))))
  unrestrict-cut' copy' (Case' E E₁ E₂) | Inr id = (!≈ (cutCase {D1 = Inl copy} {D2 = Inr copy} (cut (Case (unrestrict E) (unrestrict E₁)) (unrestrict E₂))) ∘≈ Case≈ (!≈ (cut-assoc (Inl copy) (Case (unrestrict E) (unrestrict E₁)) (unrestrict E₂)) ∘≈ cut≈1 (unrestrict-cut' copy' E) (unrestrict E₂)) (!≈ (cut-assoc (Inr copy) (Case (unrestrict E) (unrestrict E₁)) (unrestrict E₂)) ∘≈ cut≈1 (unrestrict-cut' copy' E₁) (unrestrict E₂))) ∘≈ Case≈ (eq (transport⊢1 _) ∘≈ cut≈1 unrestrict♯R1 (UL r 1⇒ (unrestrict E₂))) (eq (transport⊢1 _) ∘≈ cut≈1 unrestrict♯R1 (UL r 1⇒ (unrestrict E₂)))
  unrestrict-cut' (♯L' D) copy' = !≈ (cut-r-copy (♯L (unrestrict D)))
  unrestrict-cut' {β = β} (♭L' D D₁) copy' with 1-cell-case β
  unrestrict-cut' (♭L' D D₁) copy' | Inl id = (cut-assoc (FL {α = r} {β = 1m} (unrestrict D)) (unrestrict D₁) copy ∘≈ cut≈2 (FL {α = r} {β = 1m} (unrestrict D)) (unrestrict-cut' {α = r} {β = 1m} D₁ copy') ∘≈ !≈ (cutFL {α = r} {β = 1m} (unrestrict (cut' D₁ copy'))) ∘≈ cutFL {β = r} (unrestrict (cut' D₁ copy'))) ∘≈ unrestrict♭Lr
  unrestrict-cut' (♭L' D D₁) copy' | Inr id = (cut-assoc (♭Lr (unrestrict D)) (unrestrict D₁) copy ∘≈ cut≈2 (FL {α = r} {β = r} (unrestrict D)) (unrestrict-cut' D₁ copy')) ∘≈ unrestrict♭Lr
  unrestrict-cut' (Inl' D) copy' = !≈ (eq (cutInl (unrestrict D))) ∘≈ Inl≈ (unrestrict-cut' D copy')
  unrestrict-cut' (Inr' D) copy' = !≈ (eq (cutInr (unrestrict D))) ∘≈ Inr≈ (unrestrict-cut' D copy')
  unrestrict-cut' (Case' D D₁ D₂) copy' = cut-assoc (Case (unrestrict D) (unrestrict D₁)) (unrestrict D₂) copy ∘≈ cut≈2 (Case (unrestrict D) (unrestrict D₁)) (unrestrict-cut' D₂ copy')
  unrestrict-cut' (♭R' D) copy' = !≈ (((FR≈ (cut-ident-right (unrestrict D)) ∘≈ eq (ap (λ x → FR {α = r} {β = r ∘1 r} r x (cut (unrestrict D) hyp)) (ap (λ x → 1⇒ {_} {_} {r} ∘1cong x) adjeq2))) ∘≈ eq (cutFR {α = r} {β = r} {γ = 1m} (unrestrict D))) ∘≈ eq (transport⊢1 _))
  unrestrict-cut' {β = β} (♯R' D) copy' with 1-cell-case β 
  unrestrict-cut' (♯R' D) copy' | Inl id = UR≈ {α = r} {β = r} (!≈ (cut-ident-right (unrestrict D) ∘≈ eq (transport⊢1 _) ∘≈ eq (ap (λ x → transport⊢ x (cut {α = 1m} {β = r} (unrestrict D) hyp)) adjeq1))) ∘≈ unrestrict♯Rr
  unrestrict-cut' (♯R' D) copy' | Inr id = UR≈ {α = r} {β = r} (!≈ (cut-ident-right (unrestrict D) ∘≈ eq (transport⊢1 _) ∘≈ eq (ap (λ x → transport⊢ x (cut {α = 1m} {β = r} (unrestrict D) hyp)) (ap (λ x → 1⇒ {_} {_} {r} ∘1cong x) adjeq1)))) ∘≈ unrestrict♯Rr
  -- identity: same to cancel early or late
  unrestrict-cut' ident' copy' = !≈ (cut-ident-left copy)
  unrestrict-cut' ident' ident' = !≈ (cut-ident-left hyp)
  unrestrict-cut' {α = α} ident' (♯R' E) with 1-cell-case α
  unrestrict-cut' ident' (♯R' E) | Inl id = !≈ (cut-ident-left _) 
  unrestrict-cut' ident' (♯R' E) | Inr id = !≈ (cut-ident-left _)
  unrestrict-cut' ident' (♯L' E) = !≈ (cut-ident-left _)
  unrestrict-cut' {α} ident' (♭L' E E₁) with 1-cell-case α -- (UL≈ {α = ?} {β = ?} {γ = ?} {e = ?} ? ∘≈ {! cutUL {α = r} {β = r} {γ = 1m} {e = 1⇒} {D = hyp} (unrestrict E)!}) ∘≈ eq (transport⊢1 _))
  unrestrict-cut' ident' (♭L' E E₁) | Inl id = !≈ (cut-ident-left _)
  unrestrict-cut' ident' (♭L' E E₁) | Inr id = !≈ (cut-ident-left _)
  unrestrict-cut' ident' (♭R' E) = !≈ (cut-ident-left _)
  unrestrict-cut' ident' (Inl' E) = !≈ (cut-ident-left _)
  unrestrict-cut' ident' (Inr' E) = !≈ (cut-ident-left _)
  unrestrict-cut' ident' (Case' E E₁ E₂) = !≈ (cut-ident-left _)
  unrestrict-cut' {β = β} (♯R' D) ident' with 1-cell-case β
  unrestrict-cut' (♯R' D) ident' | Inl id = !≈ (cut-ident-right _)
  unrestrict-cut' (♯R' D) ident' | Inr id = !≈ (cut-ident-right _)
  unrestrict-cut' (♯L' D) ident' = !≈ (cut-ident-right _)
  unrestrict-cut' (♭L' D D₁) ident' = !≈ (cut-ident-right _)
  unrestrict-cut' (♭R' D) ident' = !≈ (cut-ident-right _)
  unrestrict-cut' (Inl' D) ident' = !≈ (cut-ident-right _)
  unrestrict-cut' (Inr' D) ident' = !≈ (cut-ident-right _)
  unrestrict-cut' (Case' D D₁ D₂) ident' = !≈ (cut-ident-right _)
  -- #R and something
  unrestrict-cut' {α = α}{β} (♯R' D) (♯R' E) with 1-cell-case α | 1-cell-case β | 1-cell-case (β ∘1 α) 
  unrestrict-cut' (♯R' D) (♯R' E) | Inl id | Inl id | Inl id = UR≈{α = r} {β = 1m} (cut≈1 unrestrict♯R1 (unrestrict E) ∘≈ unrestrict-cut' {β = 1m} (♯R' D) E)
  unrestrict-cut' (♯R' D) (♯R' E) | Inl id | Inl id | Inr x₂ = 1≠r x₂
  unrestrict-cut' (♯R' D) (♯R' E) | Inl id | Inr id | Inl x₂ = 1≠r (! x₂)
  unrestrict-cut' (♯R' D) (♯R' E) | Inl id | Inr id | Inr id = UR≈ {α = r} {β = r} (cut≈1 unrestrict♯Rr (unrestrict E) ∘≈ unrestrict-cut' {β = r} (♯R' D) E)
  unrestrict-cut' (♯R' D) (♯R' E) | Inr id | Inl id | Inl x₂ = 1≠r (! x₂)
  unrestrict-cut' (♯R' D) (♯R' E) | Inr id | Inl id | Inr id = UR≈ {α = r} {β = r} (cut≈1 unrestrict♯R1 (unrestrict E) ∘≈ unrestrict-cut' {β = 1m} (♯R' D) E)
  unrestrict-cut' (♯R' D) (♯R' E) | Inr id | Inr id | Inl x₂ = 1≠r (! x₂)
  unrestrict-cut' (♯R' D) (♯R' E) | Inr id | Inr id | Inr id = UR≈ {α = r} {β = r} (cut≈1 unrestrict♯Rr (unrestrict E) ∘≈ unrestrict-cut' {β = r} (♯R' D) E)
  unrestrict-cut' {β = β} (♯R' D) (♯L' E) with 1-cell-case β
  unrestrict-cut' (♯R' D) (♯L' E) | Inl id = !≈ (eq (transport⊢1 _)) ∘≈ unrestrict-cut' D E
  unrestrict-cut' (♯R' D) (♯L' E) | Inr id = !≈ (eq (transport⊢1 _)) ∘≈ unrestrict-cut' D E
  unrestrict-cut' {β = β} (♯R' D) (♭R' E) with 1-cell-case β
  unrestrict-cut' (♯R' D) (♭R' E) | Inl id = FR≈ (sg ∘≈ unrestrict-cut' (♯R' {α = 1m} D) E) where
    sg : cut {α = r} {β = 1m} (unrestrict (♯R' D)) (unrestrict E) ≈ _
    sg with 1-cell-case 1m
    ...   | Inl id = id
    ...   | Inr q = 1≠r q
  unrestrict-cut' (♯R' D) (♭R' E) | Inr id = FR≈ (sg ∘≈ unrestrict-cut' (♯R' {α = r} D) E) where
    sg : cut {α = r} {β = r} (unrestrict (♯R' D)) (unrestrict E) ≈ _
    sg with 1-cell-case 1m
    ...   | Inl id = id
    ...   | Inr q = 1≠r q
  unrestrict-cut' {β = β} (♯R' D) (Inl' E) with 1-cell-case β
  unrestrict-cut' (♯R' D) (Inl' E) | Inl id = Inl≈ (cut≈1 sg (unrestrict E) ∘≈ unrestrict-cut' {β = 1m} (♯R' D) E) where
    sg : unrestrict (♯R' D) ≈ UR {α = r} {β = 1m} (unrestrict D)
    sg with 1-cell-case 1m
    ...   | Inl id = id
    ...   | Inr q = 1≠r q 
  unrestrict-cut' (♯R' D) (Inl' E) | Inr id = Inl≈ (cut≈1 sg (unrestrict E) ∘≈ unrestrict-cut' {β = r} (♯R' D) E) where
    sg : unrestrict (♯R' D) ≈ UR {α = r} {β = r} (unrestrict D)
    sg with 1-cell-case 1m
    ...   | Inl id = id
    ...   | Inr q = 1≠r q 
  unrestrict-cut' {β = β} (♯R' D) (Inr' E) with 1-cell-case β
  unrestrict-cut' (♯R' D) (Inr' E) | Inl id = Inr≈ (cut≈1 sg (unrestrict E) ∘≈ unrestrict-cut' {β = 1m} (♯R' D) E) where
    sg : unrestrict (♯R' D) ≈ UR {α = r} {β = 1m} (unrestrict D)
    sg with 1-cell-case 1m
    ...   | Inl id = id
    ...   | Inr q = 1≠r q 
  unrestrict-cut' (♯R' D) (Inr' E) | Inr id = Inr≈ (cut≈1 sg (unrestrict E) ∘≈ unrestrict-cut' {β = r} (♯R' D) E) where
    sg : unrestrict (♯R' D) ≈ UR {α = r} {β = r} (unrestrict D)
    sg with 1-cell-case 1m
    ...   | Inl id = id
    ...   | Inr q = 1≠r q 
  -- #L and something
  unrestrict-cut' {α = α} (♯L' D) (♯R' E) with 1-cell-case (r ∘1 α) | 1-cell-case α
  unrestrict-cut' (♯L' D) (♯R' E) | Inl x | Inl id = 1≠r (! x)
  unrestrict-cut' (♯L' D) (♯R' E) | Inl x | Inr id = 1≠r (! x)
  unrestrict-cut' (♯L' D) (♯R' E) | Inr id | Inl id = UR≈ {α = r} {β = r} (unrestrict-cut' (♯L' D) E)
  unrestrict-cut' (♯L' D) (♯R' E) | Inr id | Inr id = UR≈ {α = r} {β = r} (unrestrict-cut' (♯L' D) E)
  unrestrict-cut' (♯L' D) (♯L' E) with 1-cell-case r 
  ... | Inl p = 1≠r (! p)
  ... | Inr id = UL≈ {α = r} {β = r} {γ = r} {e = 1⇒} (unrestrict-cut' D (♯L' E))
  unrestrict-cut' {α = α} (♯L' D) (♭L' E E₁) with 1-cell-case α
  unrestrict-cut' (♯L' D) (♭L' E E₁) | Inl id = ((!≈ (cutUL {α = 1m} {β = r} {α₁ = r} {γ = r} {e = 1⇒} (cut (♭L1 (unrestrict E)) (unrestrict E₁)))) ∘≈ UL≈ {α = r} {β = r} {γ = r} {e = 1⇒} (cut≈2 (unrestrict D) unrestrict♭L1)) ∘≈ UL≈ {α = r} {γ = r} {e = 1⇒} (unrestrict-cut' D (♭L' E E₁))
  unrestrict-cut' (♯L' D) (♭L' E E₁) | Inr id = (!≈ (cutUL {α = r} {β = r} {α₁ = r} {γ = r} {e = 1⇒} (cut (♭Lr (unrestrict E)) (unrestrict E₁))) ∘≈ UL≈ {α = r} {β = r} {γ = r} {e = 1⇒} (cut≈2 (unrestrict D) unrestrict♭Lr)) ∘≈ UL≈ {α = r} {γ = r} {e = 1⇒} (unrestrict-cut' D (♭L' E E₁))
  unrestrict-cut' (♯L' D) (♭R' E) with 1-cell-case r 
  ...                               | Inl q = 1≠r (! q)
  ...                               | Inr id = FR≈ {α = r} {β = r} {γ = r} {e = 1⇒} (unrestrict-cut' (♯L' D) E)
  unrestrict-cut' (♯L' D) (Inl' E) = Inl≈ (unrestrict-cut' (♯L' D) E)
  unrestrict-cut' (♯L' D) (Inr' E) = Inr≈ (unrestrict-cut' (♯L' D) E)
  unrestrict-cut' {α = α} (♯L' D₁) (Case' E E₁ E₂) with 1-cell-case α 
  unrestrict-cut' (♯L' D₁) (Case' E E₁ E₂) | Inl id = (!≈ (cutUL {α = 1m} {β = r} {γ = r} {e = _} {D = unrestrict D₁} (cut {α = 1m} {β = 1m} (Case (unrestrict E) (unrestrict E₁)) (unrestrict E₂)))) ∘≈ UL≈ {α = r} {β = r} {γ = r} {e = 1⇒} (unrestrict-cut' {α = 1m} {β = r} D₁ (Case' E E₁ E₂))
  unrestrict-cut' (♯L' D₁) (Case' E E₁ E₂) | Inr id = !≈ (cutUL {α = r} {β = r} {α₁ = r} {γ = r} {e = 1⇒} {D = unrestrict D₁} (cut {α = r} {β = 1m} (Case (unrestrict E) (unrestrict E₁)) (unrestrict E₂))) ∘≈ UL≈ {α = r} {β = r} {γ = r} {e = 1⇒} (unrestrict-cut' {α = r} {β = r} D₁ (Case' E E₁ E₂))
-}
  unrestrict-cut' _ _ = {!!}
{- 
  -- ♭L and something
  unrestrict-cut' (♭L' D D₁) (♯R' E) = {!!}
  unrestrict-cut' (♭L' D D₁) (♯L' E) = {!!}
  unrestrict-cut' (♭L' D D₁) (♭L' E E₁) = {!!}
  unrestrict-cut' (♭L' D D₁) (♭R' E) = {!!≈ (eq (cutFR (unrestrict (♭L' D D₁)))) ∘≈ FR≈ {α = 1m} {β = r} (unrestrict-cut' (♭L' D D₁) E)!}
  unrestrict-cut' (♭L' D D₁) (Inl' E) = !≈ (eq (cutInl (unrestrict (♭L' D D₁)))) ∘≈ Inl≈ (unrestrict-cut' (♭L' D D₁) E)
  unrestrict-cut' (♭L' D D₁) (Inr' E) = !≈ (eq (cutInr (unrestrict (♭L' D D₁)))) ∘≈ Inr≈ (unrestrict-cut' (♭L' D D₁) E)
  unrestrict-cut' (♭L' D D₂) (Case' E E₁ E₂) = {!!}
  -- ♭R and something
  unrestrict-cut' (♭R' D) (♯R' E) = {!!}
  unrestrict-cut' (♭R' D) (♭L' E E₁) = {!!}
  unrestrict-cut' (♭R' D) (♭R' E) = {!!}
  unrestrict-cut' (♭R' D) (Inl' E) = Inl≈ (unrestrict-cut' (♭R' D) E)
  unrestrict-cut' (♭R' D) (Inr' E) = Inr≈ (unrestrict-cut' (♭R' D) E)
  -- Inl 
  unrestrict-cut' (Inl' D) (♯R' E) = {!!}
  unrestrict-cut' (Inl' D) (♭R' E) = {!!}
  unrestrict-cut' (Inl' D) (Inl' E) = Inl≈ (unrestrict-cut' (Inl' D) E)
  unrestrict-cut' (Inl' D) (Inr' E) = Inr≈ (unrestrict-cut' (Inl' D) E)
  unrestrict-cut' (Inl' D₁) (Case' E E₁ E₂) = (!≈ (cut-assoc (Inl (unrestrict D₁)) (Case (unrestrict E) (unrestrict E₁)) (unrestrict E₂)) ∘≈ cut≈1 (unrestrict-cut' D₁ E) (unrestrict E₂)) ∘≈ unrestrict-cut' (cut' D₁ E) E₂
  -- Inr 
  unrestrict-cut' (Inr' D) (♯R' E) = {!!}
  unrestrict-cut' (Inr' D) (♭R' E) = {!!}
  unrestrict-cut' (Inr' D) (Inl' E) = Inl≈ (unrestrict-cut' (Inr' D) E)
  unrestrict-cut' (Inr' D) (Inr' E) = Inr≈ (unrestrict-cut' (Inr' D) E)
  unrestrict-cut' (Inr' D) (Case' E E₁ E₂) = (!≈ (cut-assoc (Inr (unrestrict D)) (Case (unrestrict E) (unrestrict E₁)) (unrestrict E₂)) ∘≈ cut≈1 (unrestrict-cut' D E₁) (unrestrict E₂)) ∘≈ unrestrict-cut' (cut' D E₁) E₂
  -- Case
  unrestrict-cut' (Case' D D₁ D₂) (♯R' E) = {!!}
  unrestrict-cut' (Case' D D₁ D₂) (♯L' E) = {!!}
  unrestrict-cut' (Case' D D₁ D₂) (♭L' E E₁) = {!!}
  unrestrict-cut' (Case' D D₁ D₂) (♭R' E) = {!!}
  unrestrict-cut' (Case' D₁ D₂ D₃) (Inl' E) = !≈ (eq (cutInl (cut (Case (unrestrict D₁) (unrestrict D₂)) (unrestrict D₃)))) ∘≈ Inl≈ (unrestrict-cut' (Case' D₁ D₂ D₃) E)
  unrestrict-cut' (Case' D₁ D₂ D₃) (Inr' E) = !≈ (eq (cutInr (cut (Case (unrestrict D₁) (unrestrict D₂)) (unrestrict D₃)))) ∘≈ Inr≈ (unrestrict-cut' (Case' D₁ D₂ D₃) E)
  unrestrict-cut' (Case' D D₁ D₂) (Case' E E₁ E₂) = cut-assoc (Case (unrestrict D) (unrestrict D₁)) (unrestrict D₂) (cut (Case (unrestrict E) (unrestrict E₁)) (unrestrict E₂)) ∘≈ cut≈2 (Case (unrestrict D) (unrestrict D₁)) (unrestrict-cut' D₂ (Case' E E₁ E₂))
-}

{-

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
  unrest-wlog (Case D D₁) | Inl id = Case≈ (unrest-wlog D) (unrest-wlog D₁) ∘≈ cut-ident-right _
  unrest-wlog (Case D D₁) | Inr id with 1-cell-case 1m 
  ... | Inl id = Case≈ ((unrest-wlog D ∘≈ cut-r-copy _) ∘≈ eq (transport⊢1 _)) ((unrest-wlog D₁ ∘≈ cut-r-copy _) ∘≈ eq (transport⊢1 _))
  ... | Inr q = 1≠r q
  -- CASE
  unrest-wlog {α = α} (FL {r = m} {α = α1} D) with 0-cell-case {m}
  unrest-wlog {α = α} (FL {α = α1} D) | id with 1-cell-case α1
  unrest-wlog {α = α} (FL D) | id | Inl id = {! F1U1 !}
  unrest-wlog {α = α} (FL D) | id | Inr id with 1-cell-case α
  unrest-wlog (FL D) | id | Inr id | Inl id = FL≈ {α = r} {β = 1m} (unrest-wlog D) ∘≈ cut-ident-right (♭L1 (unrestrict (wlog D))) 
  unrest-wlog (FL D) | id | Inr id | Inr id = FL≈ {α = r} {β = r} (unrest-wlog D) ∘≈ cut-r-copy _
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
                                                               {D' = D} runit (! (2-cell-case-loop e) ∘ adjeq1) (((transport⊢≈ runit (cut-ident-left D) ∘≈ !≈ (transport⊢cut2 {e1 = runit} hyp D)) ∘≈ cut≈2 copy (unrest-wlog D)) ∘≈ unrestrict-cut' copy' (wlog D))
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
  unrest-wlog (UL .1m e D) | id | Inr id | Inr id | Inl id = UL2 {α = r} {β = r} {γ = r} {γ' = 1m} {e = 1⇒} {e' = e} {D = unrestrict (cut' copy' (wlog D))} {D' = D} runit (! (2-cell-case-loop e) ∘ adjeq2) (((transport⊢≈ runit (cut-ident-left D) ∘≈ !≈ (transport⊢cut2 {e1 = runit} hyp D)) ∘≈ cut≈2 copy (unrest-wlog D)) ∘≈ unrestrict-cut' copy' (wlog D))
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

  -- not used for anything, but provable
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

  -- hereditary substitution is definable;
  -- this isn't necessary to establish the correspondence with the sequent calculi,
  -- but it's nice to know
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

  toseqa-substvva : ∀ {A B α} (D : A [ α ]⇓ B) (p : α == 1m) 
                  → unrestrict (toseqa (substvva p D)) ≈ transport⊢ runit (transport (λ x → _ [ x ]⊢ _) p (unrestrict (toseqa D)))
  toseqa-substvva cv p = 1≠r (! p)
  toseqa-substvva v id = id
  toseqa-substvva (♯E D) p = 1≠r (! p)
  toseqa-substvva (♭rec D D') id = (!≈ (transport⊢≈ runit (unrestrict-cut' (toseqa D) (♭L' (toseqc D') ident'))) ∘≈ !≈ (transport⊢cut2 {e1 = runit} (unrestrict (toseqa D)) (unrestrict (♭L' (toseqc D') ident'))) ∘≈ cut≈1 (toseqa-substvva D id) (unrestrict (♭L' (toseqc D') ident'))) ∘≈ unrestrict-cut' (toseqa (substvva id D)) (♭L' (toseqc D') ident')
  toseqa-substvva (Case D1 D2 D) id = (!≈ (transport⊢≈ runit (unrestrict-cut' (toseqa D1) (Case' (toseqc D2) (toseqc D) ident'))) ∘≈ !≈ (transport⊢cut2 {e1 = runit} (unrestrict (toseqa D1)) (cut (Case (unrestrict (toseqc D2)) (unrestrict (toseqc D))) hyp)) ∘≈ cut≈1 (toseqa-substvva D1 id) (cut (Case (unrestrict (toseqc D2)) (unrestrict (toseqc D))) hyp)) ∘≈ unrestrict-cut' (toseqa (substvva id D1)) (Case' (toseqc D2) (toseqc D) ident')

  toseq-substaa : ∀ {α : c ≥ c} {β : c ≥ c} {A : Tp c} {B : Tp c} {C : Tp c}
            (D : A [ β ]⇓ B) (E : B [ α ]⇓ C) →
            unrestrict (toseqa (substaa D E)) ≈ unrestrict(cut' (toseqa D) (toseqa E))
  toseq-substaa {β = β} D cv with 1-cell-case β
  toseq-substaa D cv | Inl id = !≈ (!≈ ((transport⊢cut1 {e2 = runit} (unrestrict (toseqa D)) hyp ∘≈ transport⊢≈ runit (!≈ (cut-ident-right (unrestrict (toseqa D))))) ∘≈ toseqa-substvva D id) ∘≈ unrestrict-cut' (toseqa D) copy')
  toseq-substaa D cv | Inr id = !≈ (cut-r-copy _ ∘≈ unrestrict-cut' (toseqa D) copy')
  toseq-substaa D v = !≈ (unrestrict-cut' (toseqa D) ident') ∘≈ !≈ (cut-ident-right _)
  toseq-substaa {β = β} D (♯E E) with 1-cell-case β 
  toseq-substaa D (♯E E) | Inl id = (!≈ (unrestrict-cut' (toseqa D) (cut' (toseqa E) (♯L' copy'))) ∘≈ !≈ (cut≈2 (unrestrict (toseqa D)) (unrestrict-cut' (toseqa E) (♯L' copy'))) ∘≈ !≈ (cut-assoc (unrestrict (toseqa D)) (unrestrict (toseqa E)) (♯L copy)) ∘≈ cut≈1 (unrestrict-cut' (toseqa D) (toseqa E) ∘≈ toseq-substaa D E) (♯L copy)) ∘≈ unrestrict-cut' (toseqa (substaa D E)) (♯L' copy')
  toseq-substaa D (♯E E) | Inr id = !≈ ((((cut≈1 (!≈ (toseq-substaa D E)) (♯L copy) ∘≈ cut≈1 (!≈ (unrestrict-cut' (toseqa D) (toseqa E))) (♯L copy)) ∘≈ cut-assoc (unrestrict (toseqa D)) (unrestrict (toseqa E)) (♯L copy)) ∘≈ cut≈2 (unrestrict (toseqa D)) (unrestrict-cut' (toseqa E) (♯L' copy'))) ∘≈ unrestrict-cut' (toseqa D) (cut' (toseqa E) (♯L' copy'))) ∘≈ unrestrict-cut' (toseqa (substaa D E)) (♯L' copy')
  toseq-substaa D (♭rec E E') = (!≈ (unrestrict-cut' (toseqa D) (cut' (toseqa E) (♭L' (toseqc E') ident'))) ∘≈ !≈ (cut≈2 (unrestrict (toseqa D)) (unrestrict-cut' (toseqa E) (♭L' (toseqc E') ident'))) ∘≈ !≈ (cut-assoc (unrestrict (toseqa D)) (unrestrict (toseqa E)) (unrestrict (♭L' (toseqc E') ident'))) ∘≈ cut≈1 (unrestrict-cut' (toseqa D) (toseqa E) ∘≈ toseq-substaa D E) (unrestrict (♭L' (toseqc E') ident'))) ∘≈ unrestrict-cut' (toseqa (substaa D E)) (♭L' (toseqc E') ident')
  toseq-substaa D (Case E1 E2 E') = (!≈ (unrestrict-cut' (toseqa D) (cut' (toseqa E1) (Case' (toseqc E2) (toseqc E') ident'))) ∘≈ cut≈2 (unrestrict (toseqa D)) (!≈ (unrestrict-cut' (toseqa E1) (Case' (toseqc E2) (toseqc E') ident'))) ∘≈ !≈ (cut-assoc (unrestrict (toseqa D)) (unrestrict (toseqa E1)) (cut (Case (unrestrict (toseqc E2)) (unrestrict (toseqc E'))) hyp)) ∘≈ cut≈1 (unrestrict-cut' (toseqa D) (toseqa E1) ∘≈ toseq-substaa D E1) (cut (Case (unrestrict (toseqc E2)) (unrestrict (toseqc E'))) hyp)) ∘≈ unrestrict-cut' (toseqa (substaa D E1)) (Case' (toseqc E2) (toseqc E') ident')

  toseq-substac : ∀ {α : c ≥ c} {β : c ≥ c} {A : Tp c} {B : Tp c} {C : Tp c}
            (D : A [ β ]⇓ B) (E : B [ α ]⇑ C) →
            unrestrict (toseqc (substac D E)) ≈ unrestrict(cut' (toseqa D) (toseqc E))
  toseq-substac D (⇓⇑ E) = toseq-substaa D E
  toseq-substac {α = α} {β = β} D (♯I E) with 1-cell-case β | 1-cell-case α | 1-cell-case (β ∘1 α) 
  toseq-substac D (♯I E) | Inl id | Inl id | Inl id = !≈ (unrestrict-cut' (toseqa D) (♯R' (toseqc E))) ∘≈ !≈ (cut≈2 (unrestrict (toseqa D)) unrestrict♯R1) ∘≈ !≈ (eq (cutUR (unrestrict (toseqa D)))) ∘≈ UR≈ {α = r} {β = 1m ∘1 1m} (unrestrict-cut' (toseqa D) (toseqc E) ∘≈ toseq-substac D E)
  toseq-substac D (♯I E) | Inl id | Inr id | Inl p = 1≠r (! p)
  toseq-substac D (♯I E) | Inr id | Inl id | Inl p = 1≠r (! p)
  toseq-substac D (♯I E) | Inr id | Inr id | Inl p = 1≠r (! p)
  toseq-substac D (♯I E) | Inl id | Inl id | Inr p = 1≠r p
  toseq-substac D (♯I E) | Inl id | Inr id | Inr id = !≈ (unrestrict-cut' (toseqa D) (♯R' (toseqc E))) ∘≈ !≈ (cut≈2 (unrestrict (toseqa D)) unrestrict♯Rr) ∘≈ !≈ (eq (cutUR (unrestrict (toseqa D)))) ∘≈ UR≈ {α = r} {β = r} (unrestrict-cut' (toseqa D) (toseqc E) ∘≈ toseq-substac D E)
  toseq-substac D (♯I E) | Inr id | Inl id | Inr id = !≈ (unrestrict-cut' {α = 1m} {β = r} (toseqa D) (♯R' (toseqc E))) ∘≈ !≈ (cut≈2 (unrestrict (toseqa D)) unrestrict♯R1) ∘≈ !≈ (eq (cutUR {α = 1m} {β = r} (unrestrict (toseqa D)))) ∘≈ UR≈ {α = r} {β = r} (unrestrict-cut' (toseqa D) (toseqc E) ∘≈ toseq-substac D E)
  toseq-substac D (♯I E) | Inr id | Inr id | Inr id = !≈ (unrestrict-cut' {α = r} {β = r} (toseqa D) (♯R' (toseqc E))) ∘≈ !≈ (cut≈2 (unrestrict (toseqa D)) unrestrict♯Rr) ∘≈ !≈ (eq (cutUR {α = r} {β = r} (unrestrict (toseqa D)))) ∘≈ UR≈ {α = r} {β = r} (unrestrict-cut' (toseqa D) (toseqc E) ∘≈ toseq-substac D E)
  toseq-substac {β = β} D (♭I E) with 1-cell-case β 
  toseq-substac D (♭I E) | Inl id = !≈ ((FR≈ (!≈ (toseq-substac D E) ∘≈ !≈ (unrestrict-cut' (toseqa D) (toseqc E))) ∘≈ eq (cutFR (unrestrict (toseqa D)))) ∘≈ unrestrict-cut' (toseqa D) (♭R' (toseqc E)))
  toseq-substac D (♭I E) | Inr id with 1-cell-case r 
  ... | Inl q = 1≠r (! q)
  ... | Inr id = !≈ (unrestrict-cut' (toseqa D) (♭R' (toseqc E))) ∘≈ !≈ (eq (cutFR {α = r} {β = r} {α' = r} {γ = r} {e = 1⇒} (unrestrict (toseqa D)))) ∘≈ FR≈ (unrestrict-cut' (toseqa D) (toseqc E) ∘≈ toseq-substac D E)
  toseq-substac D (Inl E) = !≈ (unrestrict-cut' (toseqa D) (Inl' (toseqc E))) ∘≈ !≈ (eq (cutInl (unrestrict (toseqa D)))) ∘≈ Inl≈ (unrestrict-cut' (toseqa D) (toseqc E) ∘≈ toseq-substac D E)
  toseq-substac D (Inr E) = !≈ (unrestrict-cut' (toseqa D) (Inr' (toseqc E))) ∘≈ !≈ (eq (cutInr (unrestrict (toseqa D)))) ∘≈ Inr≈ (unrestrict-cut' (toseqa D) (toseqc E) ∘≈ toseq-substac D E)

  tond-toseq : ∀ {A B α} (D : A [ α ]⊢' B) → unrestrict (toseqc (tond D)) ≈ unrestrict D
  tond-toseq copy' = id
  tond-toseq ident' = id
  tond-toseq {α = α} (♯R' D) with 1-cell-case α
  tond-toseq (♯R' D) | Inl id = UR≈ {α = r} {β = 1m} (tond-toseq D) 
  tond-toseq (♯R' D) | Inr id = UR≈ {α = r} {β = r} (tond-toseq D) 
  tond-toseq (♭R' D) = FR≈ (tond-toseq D) 
  tond-toseq (Inl' D) = Inl≈ (tond-toseq D)
  tond-toseq (Inr' D) = Inr≈ (tond-toseq D) 
  tond-toseq (♯L' D) = (((UL≈ {α = r} {β = r} (cut-copy-r (unrestrict D)) ∘≈ cutUL {α = r} {β = r} {γ = r} {e = _} (unrestrict D)) ∘≈ cut≈2 (♯L copy) (tond-toseq D)) ∘≈ unrestrict-cut' (♯L' copy') (toseqc (tond D))) ∘≈ toseq-substac (♯E cv) (tond D)
  tond-toseq {α = α} (♭L' D E) = (sg D E ∘≈ unrestrict-cut' (♭L' (toseqc (tond D)) ident') (toseqc (tond E))) ∘≈ toseq-substac (♭rec v (tond D)) (tond E) where 
      sg : ∀ {A B C α} (D : A [ r ]⊢' C) (E : C [ α ]⊢' B) →
       cut (unrestrict (♭L' (toseqc (tond D)) ident')) (unrestrict (toseqc (tond E))) ≈ (unrestrict (♭L' D E))
      sg {α = α} D E with 1-cell-case 1m 
      ...            | Inr q = 1≠r q
      sg {α = α} D E | Inl id with 1-cell-case α 
      sg D E | Inl id | Inl id = cut≈2 (FL {β = 1m} (unrestrict D)) (tond-toseq E) ∘≈ cut≈1 (FL≈ {β = 1m} (tond-toseq D) ∘≈ cut-ident-right (FL {α = r} {β = 1m} (unrestrict (toseqc (tond D))))) (unrestrict (toseqc (tond E)))
      sg D E | Inl id | Inr id = (((!≈ (cutFL {β = r} (unrestrict E)) ∘≈ cutFL {β = 1m} (unrestrict E)) ∘≈ cut≈2 (FL {α = r} {β = 1m} (unrestrict D)) (tond-toseq E ∘≈ cut-ident-left _)) ∘≈ cut≈1 (FL≈ {α = r} {β = 1m} (tond-toseq D)) (cut hyp (unrestrict (toseqc (tond E))))) ∘≈ !≈ (cut-assoc (FL {α = r} {β = 1m} (unrestrict (toseqc (tond D)))) hyp (unrestrict (toseqc (tond E))))
  tond-toseq (Case' D₁ D₂ E) = (((cut≈2 (Case (unrestrict D₁) (unrestrict D₂)) (tond-toseq E ∘≈ cut-ident-left _) ∘≈ cut≈1 (Case≈ (tond-toseq D₁) (tond-toseq D₂)) (cut hyp (unrestrict (toseqc (tond E))))) ∘≈ !≈ (cut-assoc (Case (unrestrict (toseqc (tond D₁))) (unrestrict (toseqc (tond D₂)))) hyp (unrestrict (toseqc (tond E))))) ∘≈ unrestrict-cut' (Case' (toseqc (tond D₁)) (toseqc (tond D₂)) ident') (toseqc (tond E))) ∘≈ toseq-substac (Case v (tond D₁) (tond D₂)) (tond E)
  
  orig-to-nd : ∀ {A B α} → A [ α ]⊢ B → A [ α ]⇑ B
  orig-to-nd D = tond (wlog D)

  nd-to-orig : ∀ {A B α} → A [ α ]⇑ B → A [ α ]⊢ B 
  nd-to-orig D = unrestrict (toseqc D)

  overall-nd : ∀ {A B α} (D : A [ α ]⊢ B) → nd-to-orig (orig-to-nd D) ≈ D
  overall-nd D = unrest-wlog D ∘≈ tond-toseq (wlog D)


  -- examples

  example : (P ⊕ Q) [ r ]⇑ (Q ⊕ P)
  example = ⇓⇑ (Case cv (Inr (⇓⇑ v)) (Inl (⇓⇑ v)))

  example' : toseqc example == Case' (♯R' (Inr' copy')) (♯R' (Inl' copy')) (♯L' copy')
  example' with 1-cell-case 1m 
  example' | Inl id = id
  example' | Inr q = 1≠r q
  
  example'' : unrestrict (toseqc example) ≈ Case (Inr (hypp runit)) (Inl (hypq runit))
  example'' with 1-cell-case 1m 
  example'' | Inl id with 1-cell-case 1m
  example'' | Inl id | Inl id = Case≈ (Inr≈ (eq (ap hypp runit-idemp))) (Inl≈ (eq (ap hypq runit-idemp)))
  ... | Inr q = 1≠r q
  example'' | Inr q = 1≠r q

-}
