{-# OPTIONS --type-in-type --without-K #-}

open import lib.BasicTypes 

module lib.cubical.Cubes2 (A : Type) (a : A) where

  data Ctx : Type 
  data Ty (Γ : Ctx) : Type 
  data Tm : (Γ : Ctx) → Ty Γ → Type 
  data Telescope (Γ : Ctx) : Type 
  data Subst : (Γ : Ctx) → Ctx → Type 
  data TSubst (Γ : Ctx) : Telescope Γ → Type 
  interpc : Ctx → Type
  interpt : {Γ : Ctx} → Telescope Γ → interpc Γ → Type
  -- idb : (n : Nat) → interpc (Boundary n)
  interpTy : {Γ : Ctx} → Ty Γ → interpc Γ → Type
  interpTSubst : ∀ {Γ Δ} → TSubst Γ Δ → (x : interpc Γ) → interpt Δ x 
  interpTm : {Γ : Ctx} {A : Ty Γ} → Tm Γ A → (x : interpc Γ) → interpTy A x
  Boundary : (Γ : Ctx) (n : Nat) → Telescope Γ 
  Cube : {Γ : Ctx} {θ : interpc Γ} (n : Nat) → interpt (Boundary Γ n) θ → Type 
--  data CubeS (n : Nat) : interpc (Boundary (S n)) → Type 
--  CtxPath : (Γ : Ctx) → (c1 c2 : interpc Γ) → Ctx
--  idp : (n : Nat) (b : interpc(Boundary n)) → interpc (CtxPath (Boundary n) b b)
  -- CtxPathOver : {Γ : Ctx} {b1 : interpc Γ} (Γ' : interpc Γ → Ctx)
  --              {b2 : interpc Γ} 
  --               → interpc (CtxPath Γ b1 b2) →
  --               interpc (Γ' b1) → interpc (Γ' b2) → Ctx

  unwind : {Γ : Ctx} → Telescope Γ → Ctx

  unwindSubst : {Γ : Ctx} {Δ : Telescope Γ} → TSubst Γ Δ → Subst Γ (unwind Δ)

  substTy : {Γ Δ : Ctx} → Subst Γ Δ → Ty Δ → Ty Γ

  pairΓΔ : ∀ {Γ Δ} → (θ1 : interpc Γ) (θ2 : interpt Δ θ1) → interpc (unwind Δ)
  pairΓΔ θ1 θ2 = {!!}
  

  data Ctx where
    · : Ctx
    _,_ : (Γ : Ctx) (A : Ty Γ) → Ctx

  data Subst  where
    · : ∀ {Γ} → Subst Γ ·
    _,_ : ∀ {Γ Δ A} → (θ : Subst Γ Δ) → Tm Γ (substTy θ A) → Subst Γ (Δ , A)
    idsubst : ∀ {Γ} → Subst Γ Γ
    p : ∀ {Γ A} → Subst (Γ , A) Γ

  data Ty (Γ : Ctx) where
    cube : (n : Nat) → TSubst Γ (Boundary Γ n) → Ty Γ

  data Telescope (Γ : Ctx) where
    · : Telescope Γ
    _,_ : (Δ : Telescope Γ) → Ty (unwind Δ) → Telescope Γ

  data TSubst Γ where
    · : TSubst Γ ·
    _,_ : ∀ {Δ A} → (θ : TSubst Γ Δ) → Tm Γ (substTy (unwindSubst θ) A)  → TSubst Γ (Δ , A)

  -- just variables
  data Tm where
    i0 : ∀ {Γ A} → Tm (Γ , A) (substTy p A) 
    iS : ∀ {Γ A B} → Tm Γ B → Tm (Γ , A) (substTy p B) 

  unwind {Γ} · = Γ
  unwind (Δ , A) = (unwind Δ) , A

  unwindSubst · = idsubst
  unwindSubst (δ , x) = unwindSubst δ , x

  substTy θ (cube n x) = cube n {!!}

  interpt · x = Unit
  interpt (Δ , A) θ = Σ (λ (x : interpt Δ θ) → interpTy A (pairΓΔ θ x))

  interpc · = Unit
  interpc (Γ , A) = Σ (λ (x : interpc Γ) → interpTy A x)

  interpTy {Γ} (cube n B) θ = Cube {θ = θ} n (interpTSubst B θ)

  interpTSubst · θ2 = <>
  interpTSubst (θ1 , M) θ2 = interpTSubst θ1 θ2 , {!interp!}

  interpTm i0 θ = {! snd θ !}
  interpTm (iS M) θ = {! interpTm M (fst x) !}

  Boundary n = {!!}

{-

  Boundary (S n) = ? -- Σc ((Σc (Boundary n) (\ x -> cube n x)) ×c (Σc (Boundary n) (\ x -> cube n x))) (λ { ((b1 , _) , b2 , _) → CtxPath (Boundary n) b1 b2 })
-}

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
