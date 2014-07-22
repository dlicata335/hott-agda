{-# OPTIONS --type-in-type --without-K #-}

open import lib.BasicTypes 

module lib.cubical.Cubes3 (A : Type) (a : A) where

  -- FIXME use a universe to avoid large indexing

--  data Ctx : Type 
  data Ty (Γ : Type) : Type 
  data Tm : (Γ : Type) → (Γ → Type) → Type 
  data Telescope (Γ : Type) : Type 
--  data Subst : (Γ : Type) → Type → Type 
  data TSubst : (Γ : Type) → (Γ → Type) → Type 
--  interpc : Ctx → Type
  interpt : ∀ {Γ} → Telescope Γ → Γ → Type
  -- idb : (n : Nat) → interpc (Boundary n)
  interpTy : ∀ {Γ} → Ty Γ → Γ → Type
  interpTSubst : ∀ {Γ Δ} → TSubst Γ Δ → (x : Γ) → Δ x
--  interpSubst : ∀ {Γ Δ} → Subst Γ Δ → (x : Γ) → Δ 
  interpTm : ∀ {Γ} {A : Γ → Type} → Tm Γ A → (x : Γ) → A x

-- builds in some weakening
  Boundary : (n : Nat) → Telescope Unit
  Cube : (n : Nat) → interpt (Boundary n) <> → Type 

--  data CubeS (n : Nat) : interpc (Boundary (S n)) → Type 
--  CtxPath : (Γ : Ctx) → (c1 c2 : interpc Γ) → Ctx
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
    cube : (n : Nat) → TSubst Γ (interpt (Boundary n)) → Ty Γ

  data Telescope Γ where
    · : Telescope Γ
    _,nd_ : (Δ : Telescope Γ) → Telescope Γ → Telescope Γ
    _,d_ : (Δ : Telescope Γ) → Telescope (Σ (interpt Δ)) → Telescope Γ
    single : (A : Ty Γ) → Telescope Γ
    

  data TSubst where
    · : ∀ {Γ} → TSubst Γ (\ _ -> Unit)
    _,d_ : ∀ {Γ} → {Δ : Γ → Type} 
          {Δ' : Σ Δ → Type} 
        → (θ : TSubst Γ Δ) → Tm Γ (λ θ₁ → Δ' (θ₁ , interpTSubst θ θ₁))  → TSubst Γ (λ θ₁ → Σ \ (x : Δ θ₁) → (Δ' (θ₁ , x)))
    fstd : ∀ {Γ} → {Δ : Γ → Type} 
           {Δ' : Σ Δ → Type} 
         → (θ1 : TSubst Γ (\ θ → Σ \ x → Δ' (θ , x)))
         → TSubst Γ Δ
    sndd : ∀ {Γ} → {Δ : Γ → Type} 
           {Δ' : Σ Δ → Type} 
         → (θ1 : TSubst Γ (\ θ → Σ \ x → Δ' (θ , x)))
         → TSubst Γ (\ θ → Δ' (θ , fst (interpTSubst θ1 θ))) 
    vd : ∀ {Δ : Type} 
           {Δ' : Δ → Type} 
         → TSubst (Σ Δ') (Δ' o fst)

  -- just variables
  data Tm where
    i0 : ∀ {Γ} {A : Γ → Type} → Tm (Σ A) (A o fst)
    iS : ∀ {Γ A B} → Tm Γ B → Tm (Σ A) (B o fst) 

  interpt · x = Unit
  interpt (Δ ,d Δ') θ = Σ (λ (x : interpt Δ θ) → interpt Δ' (θ , x)) 
  interpt (Δ ,nd Δ') θ = interpt Δ θ × interpt Δ' θ
  interpt (single A) θ = interpTy A θ

  interpTy (cube n b) θ = Cube n (interpTSubst b θ)

--  interpTy {Γ} (cube n B) θ = Cube {θ = θ} n (interpTSubst B θ)

  interpTm i0 θ = snd θ
  interpTm (iS M) θ = interpTm M (fst θ)

  interpTSubst · θ' = <>
  interpTSubst (θ ,d x) θ' = interpTSubst θ θ' , interpTm x θ'
  interpTSubst (fstd x) θ' = fst (interpTSubst x θ')
  interpTSubst (sndd x) θ' = snd (interpTSubst x θ')
  interpTSubst vd θ' = snd θ'

  wkn : ∀ {Γ n} →
      TSubst (Σe Γ (interpt (Boundary Γ n))) (λ x → interpt (Boundary Γ n) (fst x)) →
      TSubst (Σe Γ (interpt (Boundary Γ n))) (interpt (Boundary (Σe Γ (interpt (Boundary Γ n))) n))
  wkn = {!!}

  Boundary Γ Z = ·
  Boundary Γ (S n) = ((Boundary Γ n ,d single (cube n (wkn {Γ = Γ}{n = n} (vd {Δ = Γ} {Δ' = interpt (Boundary Γ n)})))) ,nd 
                      (Boundary Γ n ,d single (cube n (wkn {Γ = Γ} {n = n} (vd {Δ = Γ} {Δ' = interpt (Boundary Γ n)})))))
                                  ,d {!!}
    -- Boundary (S n) = ? -- Σc ((Σc (Boundary n) (\ x -> cube n x)) ×c (Σc (Boundary n) (\ x -> cube n x))) (λ { ((b1 , _) , b2 , _) → CtxPath (Boundary n) b1 b2 })


  -- interpSubst · θ' = <>
  -- interpSubst (θ , x) θ' = interpSubst θ θ' , interpTm x θ'

  Cube Γ n = {!!}

{-
  Cube 0 _ = A
  Cube (S n) = {! CubeS n !}
-}

--  data CubeS (n : Nat) where
--    id : CubeS n (idb (S n))

  -- idc : (n : Nat) → Cube n (idb n)
  -- idc Z = a
  -- idc (S n) = id

  -- idb Z = <>
  -- idb (S n) = ((idb n , idc n) , idb n , idc n) , idp n (idb n)

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
