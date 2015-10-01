
open import adjointlogic.Lib
open import adjointlogic.Rules
open import adjointlogic.Properties
open import adjointlogic.General

module adjointlogic.Idempotent where

  open IdempotentMonad

  postulate
    adjeq1 : _==_ (runit ∘1cong 1⇒{_}{_}{r}) 1⇒
    adjeq2 : _==_ (1⇒ {_} {_} {r} ∘1cong runit) 1⇒

  ♭ : Tp c → Tp c
  ♭ A = F r A

  ♯ : Tp c → Tp c
  ♯ A = U r A

  ♭functor = Ffunctor r
  ♯functor = Ufunctor r

  copy : ∀ {A} → A [ r ]⊢ A
  copy = transport⊢ runit hyp

  ♯R1 : { A B : Tp c} → A [ r ]⊢ B → A [ 1m ]⊢ ♯ B 
  ♯R1 D = UR {α = r} {β = 1m} D

  ♯Rr : { A B : Tp c} → A [ r ]⊢ B → A [ r ]⊢ ♯ B 
  ♯Rr D = UR {α = r} {β = r} D

  ♯L : { A B : Tp c} → A [ r ]⊢ B → ♯ A [ r ]⊢ B
  ♯L {A}{B} D = UL r 1⇒ D 

  ♭R : {A B : Tp c} → A [ r ]⊢ B → A [ r ]⊢ ♭ B
  ♭R D = FR {α = r} {β = r} r 1⇒ D 

  ♭Lr : {A B : Tp c} → A [ r ]⊢ B → ♭ A [ r ]⊢ B
  ♭Lr D = FL {α = r} {β = r} D

  ♭L1 : {A B : Tp c} → A [ r ]⊢ B → ♭ A [ 1m ]⊢ B
  ♭L1 D = FL {α = r} {β = 1m} D

  U1R : { A B : Tp c } {α : c ≥ c} → A [ α ]⊢ B → A [ α ]⊢ U 1m B 
  U1R D = UR {α = 1m} D

  U1L : { A B : Tp c} {α : c ≥ c} → A [ α ]⊢ B → U 1m A [ α ]⊢ B
  U1L {A}{B} {α} D = UL α 1⇒ D 

  F1R : {A B : Tp c} {α : c ≥ c} → A [ α ]⊢ B → A [ α ]⊢ F 1m B
  F1R {α = α} D = FR {α = 1m} α 1⇒ D 

  F1L : {A B : Tp c} {α : c ≥ c} → A [ α ]⊢ B → F 1m A [ α ]⊢ B
  F1L {α = α} D = FL {α = 1m} {β = α} D

  ♯idempotent : NatIso (♯functor ∘Func ♯functor) ♯functor
  ♯idempotent = !natiso (U∘-natiso {α = r} {β = r})

  ♭idempotent : NatIso (♭functor ∘Func ♭functor) ♭functor
  ♭idempotent = !natiso (F∘-natiso {α = r} {β = r})

  -- copy is a natural transformation between Fr and 1, judgementalified
  copy-nat : ∀ {A B} (D : A [ 1m ]⊢ B) → cut copy D ≈ cut D copy
  copy-nat D = (transport⊢cut1 {e2 = runit} D hyp ∘≈ transport⊢≈ runit (!≈ (cut-ident-right D) ∘≈ cut-ident-left D)) ∘≈ !≈ (transport⊢cut2 {e1 = runit} hyp D)

  runit-idemp : (runit ∘1cong runit) == runit
  runit-idemp = (ap2 _·2_ id adjeq2) ∘ interchange {e1 = runit} {e2 = 1⇒} {f1 = 1⇒} {f2 = runit}

  cut-copy-r : ∀ {A B} (D : A [ r ]⊢ B) → cut (copy{A}) D ≈ D
  cut-copy-r D = ((eq (transport⊢1 _) ∘≈ eq (ap (λ x → transport⊢ x D) adjeq1)) ∘≈ transport⊢≈ (runit ∘1cong 1⇒) (cut-ident-left D)) ∘≈ !≈ (transport⊢cut2 {e1 = runit} hyp D) where

  cut-r-copy : ∀ {A B} (D : A [ r ]⊢ B) → cut D (copy{B}) ≈ D
  cut-r-copy D = ((eq (transport⊢1 _) ∘≈ eq (ap (λ x → transport⊢ x D) adjeq2)) ∘≈ transport⊢≈ (1⇒ ∘1cong runit) (cut-ident-right D)) ∘≈ !≈ (transport⊢cut1 {e2 = runit} D hyp) where

  copy-idempotent : ∀ {A} → cut (copy{A}) copy ≈ copy
  copy-idempotent = cut-copy-r copy

  ♭absorbs♯ : NatIso (♭functor ∘Func ♯functor) ♭functor
  ♭absorbs♯ = natiso (\ {A} → 
                      iso (♭L1 (♭R (♯L copy))) 
                          (♭L1 (♭R (♯Rr copy))) 
                          (FL≈ {α = r} {β = 1m ∘1 1m} (FR2 {α = r} {β = _} {γ = r ∘1 r} {γ' = 1m} {e = 1⇒} {e' = 1⇒} {D = _} {D' = hyp} runit adjeq1 (UR≈ {α = r} {β = r ∘1 r} (UL2 {α = r} {β = r ∘1 r} {γ = r ∘1 r} {γ' = 1m} {e = 1⇒} {e' = 1⇒ ·2 (runit ∘1cong 1⇒)} {D = cut copy copy} {D' = ident A} runit (! adjeq1 ∘ adjeq2) copy-idempotent ∘≈ cutUL {α₁ = r} {γ = r} {e = 1⇒} {D = copy} copy))))
                          (FL≈ {α = r} {β = 1m ∘1 1m} (FR2 {α = r} {β = r ∘1 (1m ∘1 1m)} {γ = r ∘1 r} {γ' = 1m} {e = 1⇒} {e' = 1⇒} {D = _} {D' = ident A} runit adjeq1 (copy-idempotent ∘≈ eq (transport⊢1 _)))))
                     (λ D → FL≈ {α = r} {β = 1m ∘1 1m} (FR≈ {α = r} {β = r ∘1 (1m ∘1 1m)} {γ = r} {e = 1⇒} (!≈ (eq (transport⊢1 _)) ∘≈ !≈ (cutUL {α = r} {β = r} {γ = 1m} {e = 1⇒} {D = D} (transport⊢ runit hyp)) ∘≈ UL≈ {α = r} {β = r ∘1 1m} {γ = r} {e = 1⇒} (copy-nat D) ∘≈ cutUL D)))

  ♯absorbs♭ : NatIso (♯functor ∘Func ♭functor) ♯functor
  ♯absorbs♭ = natiso (\ {A} → 
                      iso (♯R1 (♯L (♭Lr copy)))
                          (♯R1 (♭R (♯L copy)))
                          (UR≈ {α = r} {β = 1m} ((UL2 {α = r} {β = r} {γ = r} {γ' = 1m} {e = 1⇒} {e' = 1⇒} {D = _} {D' = ident (Functor.ob ♭functor A)} runit adjeq2 (FL≈ {α = r} {β = r} (FR2 {α = r} {β = r ∘1 r} {γ = r ∘1 r} {γ' = 1m} {e = 1⇒} {e' = 1⇒ ·2 (1⇒ ∘1cong runit)} {D = cut (FR 1m 1⇒ hyp) (cut (♭Lr copy) copy)} {D' = ident A} runit (! adjeq2 ∘ adjeq1) ((copy-idempotent ∘≈ cut≈1 (cut-ident-left copy ∘≈ eq (transport⊢1 _)) copy) ∘≈ cut-assoc (FR 1m 1⇒ (ident A)) (FL {α = r} {β = r} (transport⊢ runit (ident A))) (transport⊢ runit (ident A)))) ∘≈ Fη _) ∘≈ !≈ (commuteULFR {α = r} {β = r} {γ = r} {δ1 = r} {δ2 = r} {δ3 = r} {e1 = 1⇒} {e2 = 1⇒} {e3 = 1⇒} {e4 = 1⇒} (cut (♭Lr copy) copy) id)) ∘≈ FR≈ (cutUL {α₁ = r} {γ = r} {e = 1⇒} copy ∘≈ eq (transport⊢1 _))))
                          (UR≈ {α = r} {β = 1m ∘1 1m} ((UL2 {α = r} {β = (r ∘1 r) ∘1 r} {γ = r} {γ' = 1m} {e = 1⇒} {e' = 1⇒} {D = cut copy copy} runit adjeq2 copy-idempotent ∘≈ cutUL {α₁ = r} {γ = r} {e = 1⇒} {D = copy} copy) ∘≈ eq (transport⊢1 _ ∘ transport⊢1 _))))
                     (λ D → UR≈ {α = r} {β = 1m ∘1 1m} ((UL≈ {α = r} {β = r} {γ = r} {e = 1⇒} (FL≈ {α = r} {β = r ∘1 1m} (!≈ (eq (transport⊢1 _)) ∘≈ copy-nat D)∘≈ cutFL D) ∘≈ cutUL D) ∘≈ eq (transport⊢1 _)))


