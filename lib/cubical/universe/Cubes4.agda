{-# OPTIONS --type-in-type --without-K --no-positivity-check --no-termination-check #-}

open import lib.BasicTypes 
open import lib.cubical.PathOver

module lib.cubical.Cubes4 (A : Type) (a : A) where

  -- FIXME use a universe to avoid large indexing

--  data Ctx : Type 
  data Ty (Γ : Type) : Type 
  data Tm : (Γ : Type) → (Γ → Type) → Type 
--  data Ctx : Type 
--  data Telescope (Γ : Type) : Type 
--  data Subst : (Γ : Type) → Type → Type 
--  data TSubst : (Γ : Type) → (Γ → Type) → Type 
--  interpc : Ctx → Type
--  interpt : ∀ {Γ} → Telescope Γ → Γ → Type
  -- 
  interpTy : ∀ {Γ} → Ty Γ → Γ → Type
--  interpTSubst : ∀ {Γ Δ} → TSubst Γ Δ → (x : Γ) → Δ x
--  interpSubst : ∀ {Γ Δ} → Subst Γ Δ → (x : Γ) → Δ 
  interpTm : ∀ {Γ} {A : Γ → Type} → Tm Γ A → (x : Γ) → A x

-- builds in some weakening
  Boundary : (n : Nat) → Ty Unit
  Cube : (n : Nat) → interpTy (Boundary n) <> → Type 

  data CubeS (n : Nat) : interpTy (Boundary (S n)) <> → Type 
  idb : (n : Nat) → interpTy (Boundary n) <>
  idc : (n : Nat) → Cube n (idb n)
  
  TmPath : {Γ Γ' : Type} (A : Ty Γ') → (c1 c2 : Γ → Γ') → c1 == c2 → (M1 : Tm Γ (interpTy A o c1)) (M2 : Tm Γ (interpTy A o c2)) → Ty Γ
--  idp : (n : Nat) (b : interpc(Boundary n)) → interpc (CtxPath (Boundary n) b b)
  -- CtxPathOver : {Γ : Ctx} {b1 : interpc Γ} (Γ' : interpc Γ → Ctx)
  --              {b2 : interpc Γ} 
  --               → interpc (CtxPath Γ b1 b2) →
  --               interpc (Γ' b1) → interpc (Γ' b2) → Ctx

  -- data Ctx where
  --   · : Ctx
  --   _,_ : (Γ : Ctx) (A : Ty (interpc Γ)) → Ctx

  -- interpc · = Unit
  -- interpc (Γ , A) = Σ (λ (x : interpc Γ) → interpTy A x)

  -- data Subst  where
  --   · : ∀ {Γ} → Subst Γ (interpc ·)
  --   _,_ : ∀ {Γ Γ' A} → (θ : Subst Γ Γ') → Tm Γ (A o interpSubst θ) → Subst Γ (Σ A)

  data Ty Γ where
    cube : (n : Nat) → Tm Γ (\ _ -> interpTy (Boundary n) <>) → Ty Γ
    · : Ty Γ
    _,nd_ : Ty Γ → Ty Γ → Ty Γ
    _,d_ : (A : Ty Γ) → (B : Ty (Σ (interpTy A))) → Ty Γ

  data Tm where
    i0 : ∀ {Γ} {A : Γ → Type} → Tm (Σ A) (A o fst)
    iS : ∀ {Γ A B} → Tm Γ B → Tm (Σ A) (B o fst) 
    · : ∀ {Γ} → Tm Γ (\ _ -> Unit)
    _,d_ : ∀ {Γ} → {Δ : Γ → Type} 
          {Δ' : Σ Δ → Type} 
        → (θ : Tm Γ Δ) → Tm Γ (λ θ₁ → Δ' (θ₁ , interpTm θ θ₁))  → Tm Γ (λ θ₁ → Σ \ (x : Δ θ₁) → (Δ' (θ₁ , x)))
    fstd : ∀ {Γ} → {Δ : Γ → Type} 
           {Δ' : Σ Δ → Type} 
         → (θ1 : Tm Γ (\ θ → Σ \ x → Δ' (θ , x)))
         → Tm Γ Δ
    sndd : ∀ {Γ} → {Δ : Γ → Type} 
           {Δ' : Σ Δ → Type} 
         → (θ1 : Tm Γ (\ θ → Σ \ x → Δ' (θ , x)))
         → Tm Γ (\ θ → Δ' (θ , fst (interpTm θ1 θ))) 
    substtm : ∀ {Γ Γ' A} → Tm Γ' A → (θ : Γ → Γ') → Tm Γ (A o θ)


  interpTy (cube n b) θ = Cube n (interpTm b θ)
  interpTy · x = Unit
  interpTy (Δ ,d Δ') θ = Σ (λ (x : interpTy Δ θ) → interpTy Δ' (θ , x)) 
  interpTy (Δ ,nd Δ') θ = interpTy Δ θ × interpTy Δ' θ

--  interpTy {Γ} (cube n B) θ = Cube {θ = θ} n (interpTSubst B θ)

  interpTm i0 θ = snd θ
  interpTm (iS M) θ = interpTm M (fst θ)
  interpTm · θ' = <>
  interpTm (θ ,d x) θ' = interpTm θ θ' , interpTm x θ'
  interpTm (fstd x) θ' = fst (interpTm x θ')
  interpTm (sndd x) θ' = snd (interpTm x θ')
  interpTm (substtm M θ) θ' = interpTm M (θ θ')

  Boundary Z = ·
  Boundary (S n) = ((Boundary n ,d (cube n i0)) ,nd 
                    (Boundary n ,d (cube n i0))) ,d 
                    TmPath {Γ' = Unit} (Boundary n) (λ _ → <>) (λ _ → <>) id (fstd (fstd i0)) (fstd (sndd i0))

  -- interpSubst · θ' = <>
  -- interpSubst (θ , x) θ' = interpSubst θ θ' , interpTm x θ'

  Cube 0 _ = A
  Cube (S n) = CubeS n

  data CubeS (n : Nat) where
    id : CubeS n (idb (S n))

  idb Z = <>
  idb (S n) = ((idb n , idc n) , idb n , idc n) , {!!}

  idc Z = a
  idc (S n) = id

  TmPath (cube n B) θ1 θ2 δ M1 M2 = cube (S n) (((substtm B θ1 ,d M1) ,d (substtm B θ2 ,d M2)) ,d {!!})
  TmPath · θ1 θ2 δ M1 M2 = ·
  TmPath (A' ,nd A'') θ1 θ2 δ M1 M2 = TmPath A' _ _ δ (fstd M1) (fstd M2) ,nd TmPath A'' _ _ δ (sndd M1) (sndd M2)
  TmPath (A' ,d A'') θ1 θ2 δ M1 M2 =
         TmPath A' _ _ δ (fstd M1) (fstd M2) ,d
         TmPath A'' (λ { (x , y) → (θ1 x) , (fst (interpTm M1 x)) }) 
                    (λ { (x , y) → θ2 x , fst (interpTm M2 x) })
                    (λ≃ ((λ { (x , y) → pair= (ap≃ δ) {!y!} })))
                    (substtm (sndd M1) fst)
                    (substtm (sndd M2) fst)

{-
  CtxPath · c1 c2 = ·
--  CtxPath (cube n x) c1 c2 = cube (S n) (((x , c1) , (x , c2)) , idp n x)
--  CtxPath (Γ ×c Γ₁) c1 c2 = CtxPath Γ (fst c1) (fst c2) ×c CtxPath Γ₁ (snd c1) (snd c2)
  CtxPath (Σc Γ Γ') c1 c2 = Σc (CtxPath Γ (fst c1) (fst c2)) (λ α → CtxPathOver {Γ} Γ' α (snd c1) (snd c2))

  CtxPathOver n = {!!}
-}

{-    

  idp = {!!}

  test1 : interpc (Boundary 1)
  test1 = ((<> , {!!}) , (<> , {!!})) , <>

  test2 : interpc (Boundary 2)
  test2 = (((((<> , {!!}) , ({!!} , {!!})) , <>) , {!!}) , ((((<> , {!!}) , (<> , {!!})) , <>) , {!!})) ,
          (((<> , {!!}) , (<> , {!!})) , {!!})
-}
