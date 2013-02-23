{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open Truncation
open Int

open import lib.PointedTypes


module lib.Spectra where
  
  -- Aha.  But you can change the definition here to be
  -- A space, a point, and and equivalence with the n-th loop space?


  record Ω-Spectrum : Type where
    constructor _⋊_ 
    field
      sp : (n : Nat) → Type₊
      l≃ : (n : Nat) → Equiv₊ (sp n) (Ω (sp (S n)))

  open Ω-Spectrum

  -- Stable Homotopy Groups of an Ω-Spectrum
  πˢ : Int → Ω-Spectrum → Type
  πˢ (Pos n) E = τ₀ (Loop n ∣ sp E Z ∣ (bp (sp E Z)))
  πˢ Zero E = τ₀ ∣ sp E Z ∣
  πˢ (Neg n) E = τ₀ ∣ sp E (pos2nat n) ∣

  record Ω-Map (E F : Ω-Spectrum) : Type where
    
    field
      mp : (n k : Nat) → Map₊ (sp E n) (sp F (NatM._+_ n k))

      -- basically this, but you need to finish composition and
      -- inversion of equivalences

      --mp≃ : (n : Nat) → l≃ ∘ Ω-functor (mp (S n)) ∘ (! l≃) ≃ mp n

  open Ω-Map

  Ω-Hom : Ω-Spectrum → Ω-Spectrum → Ω-Spectrum
  Ω-Hom E F = (λ n → {!mp (Ω-Map E F)!}) ⋊ {!!}

  ∘-equiv₊-post : {A B C : Type₊} → Equiv₊ B C → Equiv₊ (A ₊→ B) (A ₊→ C)
  ∘-equiv₊-post (f , p) = {!!} , {!!}

  ∘-equiv₊-pre : {A B C : Type₊} → Equiv₊ A B → Equiv₊ (B ₊→ C) (A ₊→ C)
  ∘-equiv₊-pre (f , p) = {!!}

  Ω-cotensor : Ω-Spectrum → Type₊ → Ω-Spectrum
  Ω-cotensor E X = (λ n → X ₊→ (sp E n)) ⋊ (λ n → {!∘-equiv₊-post (l≃ E n)!})

  -- E-cohomology
  ⟪_⟫ : Ω-Spectrum → Nat → Type₊ → Type
  ⟪ E ⟫ n X = πˢ (nti- n) (Ω-cotensor E X)



  -- The Integral Eilenberg-MacLane Spectrum
  -- open S using (S^ ; S-rec; S-elim)

  -- Hℤ-sp : Nat → Type₊
  -- Hℤ-sp n = (Trunc (tlp (n +1np)) (S^ (n +1np))) , [ S.base ]
  
  -- Hℤ-l≃ : (n : Nat) → Equiv₊ (Hℤ-sp n) (Ω (Hℤ-sp (S n)))
  -- Hℤ-l≃ n = 
  --   let open TruncPath
  --       E₀ = eqv (tlp (n +1np)) {S^ (n +1np +1)} {S.base} {S.base} 
  --       E₁ = τn[Ω[S^n+1]]-Equiv-τn[S^n]{n +1np} in
  --   (∘-equiv (!-equiv E₁) E₀) , id

  -- Hℤ : Ω-Spectrum
  -- Hℤ = Hℤ-sp ⋊ Hℤ-l≃

  -- -- n-th (reduced) cohomology group!
  -- H^ : Nat → Type₊ → Type
  -- H^ n X = ⟪ Hℤ ⟫ n X
