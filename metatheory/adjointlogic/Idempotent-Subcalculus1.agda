
open import adjointlogic.Lib
open import adjointlogic.Rules
open import adjointlogic.Properties
open import adjointlogic.General
open import adjointlogic.Idempotent

module adjointlogic.Idempotent-Subcalculus1 where

  open IdempotentMonad

  -- ----------------------------------------------------------------------
  -- restricted rules

  data _[_]⊢'_ : Tp c → (c ≥ c) → Tp c → Set where
    hypp' : ∀ {α} → P [ α ]⊢' P
    hypq' : ∀ {α} → Q [ α ]⊢' Q
    ♯R' : ∀ { A B α } → A [ r ]⊢' B → A [ α ]⊢' ♯ B
    ♯L' : ∀ { A B } → A [ r ]⊢' B → ♯ A [ r ]⊢' B
    ♭L' : ∀ {A B α} → A [ r ]⊢' B → ♭ A [ α ]⊢' B
    ♭R' : ∀ {A B} → A [ r ]⊢' B → A [ r ]⊢' ♭ B
    Inl' : ∀ {α C A B} → C [ α ]⊢' A → C [ α ]⊢' (A ⊕ B)
    Inr' : ∀ {α C A B} → C [ α ]⊢' B → C [ α ]⊢' (A ⊕ B)
    Case' : ∀ {α C A B} → A [ α ]⊢' C → B [ α ]⊢' C → (A ⊕ B) [ α ]⊢' C
    U1R' : ∀ { A B α } → A [ α ]⊢' B → A [ α ]⊢' U 1m B
    U1L' : ∀ { A B α } → A [ α ]⊢' B → U 1m A [ α ]⊢' B
    F1L' : ∀ {A B α} → A [ α ]⊢' B → F 1m A [ α ]⊢' B
    F1R' : ∀ {A B α} → A [ α ]⊢' B → A [ α ]⊢' F 1m B

  trunit' : ∀ {A B α} → α == 1m → A [ α ]⊢' B → A [ r ]⊢' B
  trunit' _ hypp' = hypp'
  trunit' _ hypq' = hypq'
  trunit' _ (♯R' D) = ♯R' D
  trunit' _ (♭L' D) = ♭L' D
  trunit' eq (Inl' D) = Inl' (trunit' eq D)
  trunit' eq (Inr' D) = Inr' (trunit' eq D)
  trunit' eq (Case' D D₁) = Case' (trunit' eq D) (trunit' eq D₁)
  trunit' eq (♯L' _) = 1≠r (! eq)
  trunit' eq (♭R' _) = 1≠r (! eq)
  trunit' eq (U1R' D) = U1R' (trunit' eq D)
  trunit' eq (U1L' D) = U1L' (trunit' eq D)
  trunit' eq (F1L' D) = F1L' (trunit' eq D)
  trunit' eq (F1R' D) = F1R' (trunit' eq D)

  forget : ∀ {A B α} → A [ α ]⊢' B → A [ α ]⊢ B
  forget {α = α} hypp' with 1-cell-case α
  forget hypp' | Inl id = hypp 1⇒
  forget hypp' | Inr id = hypp runit
  forget {α = α} hypq' with 1-cell-case α
  forget hypq' | Inl id = hypq 1⇒
  forget hypq' | Inr id = hypq runit
  forget {α = α} (♯R' D) with 1-cell-case α
  forget (♯R' D) | Inl id = ♯R1 (forget D)
  forget (♯R' D) | Inr id = ♯Rr (forget D)
  forget (♯L' D) = ♯L (forget D)
  forget {α = α} (♭L' D) with 1-cell-case α
  forget (♭L' D) | Inl id = ♭L1 (forget D)
  forget (♭L' D) | Inr id = ♭Lr (forget D)
  forget (♭R' D) = ♭R (forget D)
  forget (Inl' D) = Inl (forget D)
  forget (Inr' D) = Inr (forget D)
  forget (Case' D D₁) = Case (forget D) (forget D₁)
  forget (U1R' D) = UR {α = 1m} (forget D)
  forget {α = α} (U1L' D) = UL {α = 1m} {β = α} α 1⇒ (forget D)
  forget (F1L' D) = FL {α = 1m} (forget D)
  forget {α = α} (F1R' D) = FR {α = 1m} {β = α} α 1⇒ (forget D)

  ∘r : ∀ α → (α ∘1 r) == r
  ∘r α with 1-cell-case α
  ∘r .1m | Inl id = id
  ∘r .r | Inr id = id

  r∘ : ∀ α → (r ∘1 α) == r
  r∘ α with 1-cell-case α
  r∘ .1m | Inl id = id
  r∘ .r | Inr id = id

  wlog : ∀ {A B α} → A [ α ]⊢ B → A [ α ]⊢' B
  wlog (hypp x) = hypp'
  wlog (hypq x) = hypq'
  wlog {α = α} (FL {r = m} {α = α1} D) with 0-cell-case {m}
  wlog {α = α} (FL {α = α1} D) | id with 1-cell-case α1
  wlog (FL D) | id | Inl id = F1L' (wlog D)
  wlog (FL D) | id | Inr id = ♭L' (transport (λ x → _ [ x ]⊢' _) (r∘ _) (wlog D))
  wlog {α = α} (FR {q = q} {α = α1} γ e D) with 0-cell-case {q}
  wlog {α = α} (FR {α = α1} γ e D) | id with 1-cell-case α1 | 1-cell-case γ | 1-cell-case α
  wlog (FR .1m e D) | id | Inl id | Inl id | Inl id = F1R' (wlog D)
  wlog (FR .1m e D) | id | Inl id | Inl id | Inr id = F1R' (trunit' id (wlog D))
  wlog (FR .r e D) | id | Inl id | Inr id | Inl id = r⇒/1 e
  wlog (FR .r e D) | id | Inl id | Inr id | Inr id = F1R' (wlog D)
  wlog (FR .1m e D) | id | Inr id | Inl id | Inl id = r⇒/1 e
  wlog (FR .1m e D) | id | Inr id | Inl id | Inr id = ♭R' (trunit' id (wlog D))
  wlog (FR .r e D) | id | Inr id | Inr id | Inl id = r⇒/1 e
  wlog (FR .r e D) | id | Inr id | Inr id | Inr id = ♭R' (wlog D)
  wlog {α = α} (UL {q = q} {α = α1} γ e D) with 0-cell-case {q} 
  wlog {α = α} (UL {α = α1} γ e D) | id with 1-cell-case α | 1-cell-case α1 | 1-cell-case γ 
  wlog (UL .1m e D) | id | Inl id | Inl id | Inl id = U1L' (wlog D)
  wlog (UL .r e D) | id | Inl id | Inl id | Inr id = r⇒/1 e
  wlog (UL .1m e D) | id | Inl id | Inr id | Inl id = r⇒/1 e
  wlog (UL .r e D) | id | Inl id | Inr id | Inr id = r⇒/1 e
  wlog (UL .1m e D) | id | Inr id | Inl id | Inl id = U1L' (trunit' id (wlog D))
  wlog (UL .r e D) | id | Inr id | Inl id | Inr id = U1L' (wlog D)
  wlog (UL .1m e D) | id | Inr id | Inr id | Inl id = ♯L' (trunit' id (wlog D))
  wlog (UL .r e D) | id | Inr id | Inr id | Inr id = ♯L' (wlog D)
  wlog (UR {p = p} {α = α} D) with 0-cell-case {p}
  wlog (UR {α = α₁} D) | id with 1-cell-case α₁ 
  wlog (UR D) | id | Inl id = U1R' (wlog D)
  wlog {α = α} (UR D) | id | Inr id = ♯R' (transport (λ x → _ [ x ]⊢' _) (∘r _) (wlog D))
  wlog (Inl D) = Inl' (wlog D)
  wlog (Inr D) = Inr' (wlog D)
  wlog (Case D D₁) = Case' (wlog D) (wlog D₁)

  wlog-forget : ∀ {A B α} → (D : A [ α ]⊢' B) → wlog (forget D) == D
  wlog-forget {α = α} hypp' with 1-cell-case α
  wlog-forget hypp' | Inl id = id
  wlog-forget hypp' | Inr id = id
  wlog-forget {α = α} hypq' with 1-cell-case α
  wlog-forget hypq' | Inl id = id
  wlog-forget hypq' | Inr id = id
  wlog-forget (Inl' D) = ap Inl' (wlog-forget D)
  wlog-forget (Inr' D) = ap Inr' (wlog-forget D)
  wlog-forget (Case' D D₁) = ap2 Case' (wlog-forget D) (wlog-forget D₁)
  -- CASE
  wlog-forget {α = α} (♯R' D) with 1-cell-case α
  wlog-forget (♯R' D) | Inl id with 0-cell-case {c} -- these withs shouldn't be necessary, but it looks like Agda isn't applying the REWRITEs for 0-cell-case/1-cell-case
  wlog-forget (♯R' D) | Inl id | id with 1-cell-case r 
  ... | Inl x = 1≠r (! x)
  wlog-forget (♯R' D) | Inl id | id | Inr id with 1-cell-case r 
  ... | Inl p = 1≠r (! p)
  ... | Inr id = ap ♯R' (wlog-forget D)
  wlog-forget (♯R' D) | Inr id with 0-cell-case {c} 
  ... | id with 1-cell-case r
  ...         | Inl p = 1≠r (! p)
  wlog-forget (♯R' D) | Inr id | id | Inr id with 1-cell-case r 
  ... | Inl p = 1≠r (! p)
  wlog-forget (♯R' D) | Inr id | id | Inr id | Inr id = ap ♯R' (wlog-forget D)
  -- CASE
  wlog-forget (♯L' D) with 0-cell-case {c} -- these withs shouldn't be necessary, but it looks like Agda isn't applying the REWRITEs for 0-cell-case/1-cell-case
  ... | id with 1-cell-case r 
  ...         | Inr id = ap ♯L' (wlog-forget D)
  ...         | Inl p = 1≠r (! p)
  wlog-forget {α = α} (♭L' D) with 1-cell-case α
  -- CASE
  wlog-forget (♭L' D) | Inl id with 0-cell-case {c} -- these withs shouldn't be necessary, but it looks like Agda isn't applying the REWRITEs for 0-cell-case/1-cell-case
  ... | id with 1-cell-case r 
  ...         | Inl p = 1≠r (! p)
  ...         | Inr id with 1-cell-case r 
  ...                     | Inl p = 1≠r (! p)
  ...                     | Inr id = ap ♭L' (wlog-forget D)
  wlog-forget (♭L' D) | Inr id with 0-cell-case {c} -- these withs shouldn't be necessary, but it looks like Agda isn't applying the REWRITEs for 0-cell-case/1-cell-case 
  ... | id with 1-cell-case r 
  ...         | Inl p = 1≠r (! p)
  wlog-forget (♭L' D) | Inr id | id | Inr id with 1-cell-case r 
  ...      | Inl p = 1≠r (! p) 
  ...      | Inr id = ap ♭L' (wlog-forget D)
  -- CASE
  wlog-forget (♭R' D) with 0-cell-case {c} -- these withs shouldn't be necessary, but it looks like Agda isn't applying the REWRITEs for 0-cell-case/1-cell-case
  ...      | id with 1-cell-case r 
  ...              | Inl p = 1≠r (! p)
  ...              | Inr id = ap ♭R' (wlog-forget D)
  -- CASE
  wlog-forget {α = α} (U1R' D) with 1-cell-case α
  wlog-forget (U1R' D) | Inl id with 1-cell-case 1m -- these withs shouldn't be necessary, but it looks like Agda isn't applying the REWRITEs for 0-cell-case/1-cell-case
  ... | Inl id = ap U1R' (wlog-forget D)
  ... | Inr p = 1≠r p
  wlog-forget (U1R' D) | Inr id with 1-cell-case 1m -- these withs shouldn't be necessary, but it looks like Agda isn't applying the REWRITEs for 0-cell-case/1-cell-case
  ... | Inl id = ap U1R' (wlog-forget D)
  ... | Inr p = 1≠r p
  -- CASE
  wlog-forget {α = α} (U1L' D) with 0-cell-case {c} -- these withs shouldn't be necessary, but it looks like Agda isn't applying the REWRITEs for 0-cell-case/1-cell-case
  ... | id with 1-cell-case α | 1-cell-case 1m
  wlog-forget (U1L' D) | id | Inl id | Inl id = ap U1L' (wlog-forget D) -- K alert
  wlog-forget (U1L' D) | id | Inl x | Inr x₁ = 1≠r x₁
  wlog-forget (U1L' D) | id | Inr id | Inl id = ap U1L' (wlog-forget D) -- K alert
  wlog-forget (U1L' D) | id | Inr id | Inr x₁ = 1≠r x₁
  -- CASE
  wlog-forget (F1L' D) with 0-cell-case{c}  -- these withs shouldn't be necessary, but it looks like Agda isn't applying the REWRITEs for 0-cell-case/1-cell-case
  ... | id with 1-cell-case 1m
  ...         | Inl id = ap F1L' (wlog-forget D)
  ...         | Inr p = 1≠r p
  -- CASE
  wlog-forget {α = α} (F1R' D) with 0-cell-case{c} -- these withs shouldn't be necessary, but it looks like Agda isn't applying the REWRITEs for 0-cell-case/1-cell-case
  ... | id with 1-cell-case α | 1-cell-case 1m 
  wlog-forget (F1R' D) | id | Inl id | Inl id = ap F1R' (wlog-forget D) -- K alert
  wlog-forget (F1R' D) | id | Inl id | Inr x₁ = 1≠r x₁
  wlog-forget (F1R' D) | id | Inr id | Inl id = ap F1R' (wlog-forget D) -- K alert
  wlog-forget (F1R' D) | id | Inr id | Inr x₁ = 1≠r x₁

  forget-trunit' : ∀ {A B α} (p : α == 1m) (D : A [ α ]⊢' B) → forget (trunit' p D) ≈ transport⊢ runit (transport (λ x → _ [ x ]⊢ _) p (forget D))
  forget-trunit' p hypp' with p 
  forget-trunit' p hypp' | id with 1-cell-case 1m -- these withs shouldn't be necessary, but it looks like Agda isn't applying the REWRITEs for 0-cell-case/1-cell-case
  ... | Inl id = id
  ... | Inr q = 1≠r q
  forget-trunit' p hypq' with p 
  forget-trunit' p hypq' | id with 1-cell-case 1m -- these withs shouldn't be necessary, but it looks like Agda isn't applying the REWRITEs for 0-cell-case/1-cell-case
  ... | Inl id = id
  ... | Inr q = 1≠r q
  forget-trunit' p (♯R' D) with p 
  ... | id with 1-cell-case 1m -- these withs shouldn't be necessary, but it looks like Agda isn't applying the REWRITEs for 0-cell-case/1-cell-case
  ...         | Inl id = UR≈ {α = r} {β = r} (!≈ (eq (ap (λ x → transport⊢ x (forget D)) adjeq1)) ∘≈ !≈ (eq (transport⊢1 (forget D))))
  ...         | Inr q = 1≠r q
  forget-trunit' p (♯L' D) = 1≠r (! p)
  forget-trunit' p (♭L' D) with p 
  ... | id with 1-cell-case 1m -- these withs shouldn't be necessary, but it looks like Agda isn't applying the REWRITEs for 0-cell-case/1-cell-case
  ...         | Inl id = FL≈ {α = r} {β = r} (!≈ (eq (ap (λ x → transport⊢ x (forget D)) adjeq2)) ∘≈ !≈ (eq (transport⊢1 (forget D))))
  ...         | Inr q = 1≠r q
  forget-trunit' p (♭R' D) = 1≠r (! p)
  forget-trunit' p (Inl' D) with p 
  ... | id = Inl≈ (forget-trunit' id D)
  forget-trunit' p (Inr' D) with p 
  ... | id = Inr≈ (forget-trunit' id D)
  forget-trunit' p (Case' D D₁) with p 
  ... | id = Case≈ (forget-trunit' id D) (forget-trunit' id D₁)
  forget-trunit' p (U1R' D) with p 
  ... | id = UR≈ {α = 1m} {β = r} (forget-trunit' id D)
  -- not syntactically identical
  forget-trunit' p (U1L' D) with p 
  ... | id = UL2 {α = 1m} {β = r} {γ = r} {γ' = 1m} {e = 1⇒} {e' = 1⇒ ·2 runit} {D = forget (trunit' id D)} {D' = forget D} 
                 runit id (forget-trunit' id D)
  forget-trunit' p (F1L' D) with p 
  ... | id = FL≈ {α = 1m} {β = r} (forget-trunit' id D)
  -- not syntactically identical
  forget-trunit' p (F1R' D) with p 
  ... | id = FR2 {α = 1m} {β = r} {γ = r} {γ' = 1m} {e = 1⇒} {e' = 1⇒ ·2 runit} {D = forget (trunit' id D)} {D' = forget D} 
                 runit id (forget-trunit' id D)

  forget-wlog : ∀ {A B α} (D : A [ α ]⊢ B) → forget (wlog D) ≈ D
  forget-wlog {α = α} (hypp x) with 1-cell-case α
  forget-wlog (hypp x) | Inl id = !≈ (eq (ap hypp (2-cell-case-loop x)))
  forget-wlog (hypp x) | Inr id = !≈ (eq (ap hypp (2-cell-case1r x)))
  forget-wlog {α = α} (hypq x) with 1-cell-case α
  forget-wlog (hypq x) | Inl id = !≈ (eq (ap hypq (2-cell-case-loop x)))
  forget-wlog (hypq x) | Inr id = !≈ (eq (ap hypq (2-cell-case1r x)))
  forget-wlog (Inl D) = Inl≈ (forget-wlog D)
  forget-wlog (Inr D) = Inr≈ (forget-wlog D)
  forget-wlog (Case D D₁) = Case≈ (forget-wlog D) (forget-wlog D₁)
  -- CASE
  forget-wlog {α = α} (FL {r = m} {α = α1} D) with 0-cell-case {m}
  forget-wlog {α = α} (FL {α = α1} D) | id with 1-cell-case α1
  forget-wlog {α = α} (FL D) | id | Inl id = FL≈ {α = 1m} {β = α} (forget-wlog D)
  forget-wlog {α = α} (FL D) | id | Inr id with 1-cell-case α
  forget-wlog (FL D) | id | Inr id | Inl id = FL≈ {α = r} {β = 1m} (forget-wlog D)
  forget-wlog (FL D) | id | Inr id | Inr id = FL≈ {α = r} {β = r} (forget-wlog D)
  -- CASE
  forget-wlog {α = α} (FR {q = q} {α = α1} γ e D) with 0-cell-case {q}
  forget-wlog {α = α} (FR {α = α1} γ e D) | id with 1-cell-case α1 | 1-cell-case γ | 1-cell-case α
  forget-wlog (FR .1m e D) | id | Inl id | Inl id | Inl id = eq (ap (λ x → FR 1m x D) (! (2-cell-case-loop e))) ∘≈ FR≈ (forget-wlog D)
  -- interesting case
  forget-wlog (FR .1m e D) | id | Inl id | Inl id | Inr id = eq (ap (λ x → FR 1m x D) (! (2-cell-case1r e))) ∘≈ 
              FR2 {α = 1m} {β = r} {γ = r} {e = 1⇒} {e' = runit} {D = forget (trunit' id (wlog D))} {D' = D} 
                  runit id (transport⊢≈ runit (forget-wlog D) ∘≈ forget-trunit' id (wlog D))
  forget-wlog (FR .r e D) | id | Inl id | Inr id | Inl id = r⇒/1 e
  forget-wlog (FR .r e D) | id | Inl id | Inr id | Inr id = eq (ap (λ x → FR {α = 1m} r x D) (! (2-cell-case-loop e))) ∘≈ FR≈ (forget-wlog D)
  forget-wlog (FR .1m e D) | id | Inr id | Inl id | Inl id = r⇒/1 e
  -- interesting case
  forget-wlog (FR .1m e D) | id | Inr id | Inl id | Inr id = eq (ap (λ x → FR {α = r} 1m x D) (! (2-cell-case-loop e))) ∘≈ 
              FR2 {α = r} {β = 1m ∘1 r} {γ = r} {γ' = 1m} {e = 1⇒} {e' = 1⇒} {D = forget (trunit' id (wlog D))} {D' = D} 
                  runit adjeq1 
                  (transport⊢≈ runit (forget-wlog D) ∘≈ forget-trunit' id (wlog D))
  forget-wlog (FR .r e D) | id | Inr id | Inr id | Inl id = r⇒/1 e
  forget-wlog (FR .r e D) | id | Inr id | Inr id | Inr id = eq (ap (λ x → FR {α = r} r x D) (! (2-cell-case-loop e))) ∘≈ FR≈ (forget-wlog D)
  -- CASE
  forget-wlog {α = α} (UL {q = q} {α = α1} γ e D) with 0-cell-case {q} 
  forget-wlog {α = α} (UL {α = α1} γ e D) | id with 1-cell-case α | 1-cell-case α1 | 1-cell-case γ 
  forget-wlog (UL .1m e D) | id | Inl id | Inl id | Inl id = eq (ap (λ x → UL {α = 1m} 1m x D) (! (2-cell-case-loop e))) ∘≈ UL≈ (forget-wlog D)
  forget-wlog (UL .r e D) | id | Inl id | Inl id | Inr id = r⇒/1 e
  forget-wlog (UL .1m e D) | id | Inl id | Inr id | Inl id = r⇒/1 e
  forget-wlog (UL .r e D) | id | Inl id | Inr id | Inr id = r⇒/1 e
  -- interesting case
  forget-wlog (UL .1m e D) | id | Inr id | Inl id | Inl id = eq (ap (λ x → UL {α = 1m} 1m x D) (! (2-cell-case1r e))) ∘≈ 
              UL2 {α = 1m} {β = r} {γ = r} {γ' = 1m} {e = 1⇒} {e' = runit} {D = forget (trunit' id (wlog D))} {D' = D}
                  runit id (transport⊢≈ runit (forget-wlog D) ∘≈ forget-trunit' id (wlog D))
  forget-wlog (UL .r e D) | id | Inr id | Inl id | Inr id = eq (ap (λ x → UL {α = 1m} r x D) (! (2-cell-case-loop e))) ∘≈ UL≈ (forget-wlog D)
  -- interesting case
  forget-wlog (UL .1m e D) | id | Inr id | Inr id | Inl id = eq (ap (λ x → UL {α = r} 1m x D) (! (2-cell-case-loop e))) ∘≈ 
           UL2 {α = r} {β = r ∘1 1m} {γ = r} {γ' = 1m} {e = 1⇒} {e' = 1⇒} {D = forget (trunit' id (wlog D))} {D' = D}
               runit adjeq2 (transport⊢≈ runit (forget-wlog D) ∘≈ forget-trunit' id (wlog D)) 
  forget-wlog (UL .r e D) | id | Inr id | Inr id | Inr id = eq (ap (λ x → UL {α = r} r x D) (! (2-cell-case-loop e))) ∘≈ UL≈ (forget-wlog D)
  -- CASE
  forget-wlog (UR {p = p} {α = α} D) with 0-cell-case {p}
  forget-wlog (UR {α = α₁} D) | id with 1-cell-case α₁ 
  forget-wlog (UR D) | id | Inl id = UR≈ {α = 1m} (forget-wlog D)
  forget-wlog {α = α} (UR D) | id | Inr id with 1-cell-case α
  forget-wlog (UR D) | id | Inr id | Inl id = UR≈ {α = r} {β = 1m} (forget-wlog D)
  forget-wlog (UR D) | id | Inr id | Inr id = UR≈ {α = r} {β = r} (forget-wlog D)
