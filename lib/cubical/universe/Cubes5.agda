{-# OPTIONS --type-in-type --without-K --no-positivity-check --no-termination-check #-}

open import lib.BasicTypes 
open import lib.cubical.PathOver

module lib.cubical.Cubes5 (A : Type) (a : A) where

  -- FIXME use a universe to avoid large indexing

--  data Ctx : Type 
  data Ty (Γ : Type) : Type 
  data Tm : (Γ : Type) → (Γ → Type) → Type 
  data Ctx : Type 
--  data Telescope (Γ : Type) : Type 
  data Subst : (Γ : Type) → Type → Type 
--  data TSubst : (Γ : Type) → (Γ → Type) → Type 
  interpc : Ctx → Type
--  interpt : ∀ {Γ} → Telescope Γ → Γ → Type
  -- 
  interpTy : ∀ {Γ} → Ty Γ → Γ → Type
--  interpTSubst : ∀ {Γ Δ} → TSubst Γ Δ → (x : Γ) → Δ x
  interpSubst : ∀ {Γ Δ} → Subst Γ Δ → (x : Γ) → Δ 
  interpTm : ∀ {Γ} {A : Γ → Type} → Tm Γ A → (x : Γ) → A x

  Boundary : (n : Nat) → Ty Unit
  Cube : (n : Nat) → interpTy (Boundary n) <> → Type 

  data CubeS (n : Nat) : interpTy (Boundary (S n)) <> → Type 
  idb : (n : Nat) → interpTy (Boundary n) <>
  idc : (n : Nat) → Cube n (idb n)

  CtxPath : {Γ : Type} {Γ' : Ctx} → (θ1 θ2 : Subst Γ (interpc Γ')) → Ty Γ
  TmPath : {Γ : Type} (Γ' : Ctx) (A : Ty (interpc Γ')) → (θ1 θ2 : Subst Γ (interpc Γ'))
         → Tm Γ (interpTy (CtxPath θ1 θ2))
         → (M1 : Tm Γ (interpTy A o interpSubst θ1))
            (M2 : Tm Γ (interpTy A o interpSubst θ2))
         → Ty Γ
  TmPath' : {Γ : Type} (Γ' : Ctx) (A : Ty (interpc Γ')) → (θ1 θ2 : Subst Γ (interpc Γ'))
         → Tm Γ (interpTy (CtxPath θ1 θ2))
         → Ty (Σ (\ (θ : Γ) → (interpTy A (interpSubst θ1 θ)) × (interpTy A (interpSubst θ2 θ))))

  idcp : {Γ : Type} (Γ' : Ctx) (θ1 : Subst Γ (interpc Γ')) {θ' : Γ}
       → interpTy (CtxPath θ1 θ1) θ'
  idcp = {!!}

  idp : {Γ : Type} (Γ' : Ctx) (A : Ty (interpc Γ')) → (θ1 : Subst Γ (interpc Γ'))
         → (M1 : Tm Γ (interpTy A o interpSubst θ1)) {θ' : Γ}
         → interpTy (TmPath Γ' A θ1 θ1 {!!} M1 M1) θ'
  idp = {!!}



  -- CtxPathOver : {Γ : Ctx} {b1 : interpc Γ} (Γ' : interpc Γ → Ctx)
  --              {b2 : interpc Γ} 
  --               → interpc (CtxPath Γ b1 b2) →
  --               interpc (Γ' b1) → interpc (Γ' b2) → Ctx

  data Ctx where
     · : Ctx
     _,_ : (Γ : Ctx) (A : Ty (interpc Γ)) → Ctx

  interpc · = Unit
  interpc (Γ , A) = Σ (λ (x : interpc Γ) → interpTy A x)

  data Subst  where
     · : ∀ {Γ} → Subst Γ (interpc ·)
     _,_ : ∀ {Γ Γ' A} → (θ : Subst Γ Γ') → Tm Γ (A o interpSubst θ) → Subst Γ (Σ A)
     fsts : ∀ {Γ Γ'} {A : Γ' → Type} → Subst Γ (Σ A) → Subst Γ Γ'
     idsubst : ∀ {Γ} → Subst Γ Γ
     _osubst_ : ∀ {Γ1 Γ2 Γ3} → Subst Γ2 Γ3 → Subst Γ1 Γ2 → Subst Γ1 Γ3
  
  p : ∀ {Γ} {A : Γ → Type} → Subst (Σ A) Γ
  p = fsts idsubst

  data Ty Γ where
    cube : (n : Nat) → Tm Γ (\ _ -> interpTy (Boundary n) <>) → Ty Γ
    · : Ty Γ
    _,nd_ : Ty Γ → Ty Γ → Ty Γ
    _,d_ : (A : Ty Γ) → (B : Ty (Σ (interpTy A))) → Ty Γ
    substty : (Γ' : Type) → Ty ( Γ') → (θ : Subst Γ ( Γ')) → Ty Γ 

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
    sndnd : ∀ {Γ} → {Δ : Γ → Type} 
           {Δ' : Γ → Type} 
         → (θ1 : Tm Γ (\ θ → Δ θ × Δ' θ ))
         → Tm Γ (\ θ → Δ' θ)
    _,nd_ : ∀ {Γ} → {Δ : Γ → Type} 
            {Δ' : Γ → Type} 
          → (θ : Tm Γ Δ) → Tm Γ Δ'  → Tm Γ (λ θ₁ → Δ θ₁ × Δ' θ₁)
    substtm : ∀ {Γ Γ' A} → Tm (interpc Γ') A → (θ : Subst Γ (interpc Γ')) → Tm Γ (A o interpSubst θ)
    idcptm : {Γ : Type} (Γ' : Ctx) (θ1 : Subst Γ (interpc Γ')) 
           → Tm Γ (interpTy (CtxPath θ1 θ1))
    idptm : {Γ : Type} (Γ' : Ctx) (A : Ty (interpc Γ')) → (θ1 : Subst Γ (interpc Γ'))
         → (M1 : Tm Γ (interpTy A o interpSubst θ1)) 
         → Tm Γ (interpTy (TmPath Γ' A θ1 θ1 (idcptm Γ' θ1) M1 M1))
    idbtm : ∀ {Γ} → (n : Nat) → Tm Γ (interpTy (Boundary n) o (\ _ -> <>))


  interpTy (cube n b) θ = Cube n (interpTm b θ)
  interpTy · x = Unit
  interpTy (Δ ,d Δ') θ = Σ (λ (x : interpTy Δ θ) → interpTy Δ' (θ , x)) 
  interpTy (Δ ,nd Δ') θ = interpTy Δ θ × interpTy Δ' θ
  interpTy (substty _ A θ) θ' = interpTy A (interpSubst θ θ')

--  interpTy {Γ} (cube n B) θ = Cube {θ = θ} n (interpTSubst B θ)

  interpTm i0 θ = snd θ
  interpTm (iS M) θ = interpTm M (fst θ)
  interpTm · θ' = <>
  interpTm (θ ,d x) θ' = interpTm θ θ' , interpTm x θ'
  interpTm (fstd x) θ' = fst (interpTm x θ')
  interpTm (sndd x) θ' = snd (interpTm x θ')
  interpTm (substtm M θ) θ' = interpTm M (interpSubst θ θ')
  interpTm (M1 ,nd M2) θ' = interpTm M1 θ' , interpTm M2 θ'
  interpTm (sndnd M) θ' = snd (interpTm M θ')
  interpTm (idcptm Γ' θ1) θ' = idcp Γ' θ1 
  interpTm (idptm Γ' A θ1 M1) θ' = idp Γ' A θ1 M1
  interpTm (idbtm n) _ = idb n

  CtxPath {Γ' = ·} θ1 θ2 = ·
  CtxPath {Γ' = Γ' , A₁} θ1 θ2 = 
    CtxPath {Γ' = Γ'} (fsts θ1) (fsts θ2) ,d TmPath {!!} A₁ {!!} {!!} {!!} {!sndd ?!} {!!} 

  Boundary Z = ·
  Boundary (S n) = ((Boundary n ,d (cube n i0)) ,nd 
                    (Boundary n ,d (cube n i0))) ,d 
                    TmPath · (Boundary n) · · · (fstd (fstd i0)) (fstd (sndd i0))

  interpSubst · θ' = <>
  interpSubst (θ , x) θ' = interpSubst θ θ' , interpTm x θ'
  interpSubst (fsts θ) θ' = fst (interpSubst θ θ')
  interpSubst idsubst θ' = θ'
  interpSubst (θ1 osubst θ2) θ' = interpSubst θ1 (interpSubst θ2 θ')

  Cube 0 _ = A
  Cube (S n) = CubeS n

  data CubeS (n : Nat) where
    id : CubeS n (idb (S n))

{-
  TmPath (cube n B) θ1 θ2 δ M1 M2 = cube (S n) (((substtm B θ1 ,d M1) ,d (substtm B θ2 ,d M2)) ,d {!!})
  TmPath · θ1 θ2 δ M1 M2 = ·
  TmPath (A' ,nd A'') θ1 θ2 δ M1 M2 = TmPath A' _ _ δ (fstd M1) (fstd M2) ,nd TmPath A'' _ _ δ (sndd M1) (sndd M2)
  TmPath (A' ,d A'') θ1 θ2 δ M1 M2 =
         TmPath A' _ _ δ (fstd M1) (fstd M2) ,d 
         TmPath A'' ((θ1 osubst p) , substtm (sndd M1) p) -- (λ { (x , y) → θ2 x , fst (interpTm M2 x) })
                    (θ2 osubst p , substtm (sndd M2) p)
                    {!!}
                    (substtm (sndd M1) {!!})
                    (substtm (sndd M2) {!!})
-}
  TmPath {Γ} Γ' AA θ1 θ2 δ M1 M2 = substty _ (TmPath' Γ' AA θ1 θ2 δ) (idsubst {Γ} , (M1 ,nd  M2))

  TmPath' Γ' (cube n B) θ1 θ2 δ = cube (S n) (((substtm B (θ1 osubst p) ,d fstd i0) ,nd (substtm B (θ2 osubst p) ,d sndd i0))
                                             ,d {!!}) 
  TmPath' Γ' · θ1 θ2 δ = ·
  TmPath' Γ' (A' ,nd A'') θ1 θ2 δ = substty _ (TmPath' Γ' A' θ1 θ2 δ) (p , (fstd (fstd i0) ,nd fstd (sndd i0)))
                                  ,nd substty _ (TmPath' Γ' A'' θ1 θ2 δ) (p , (sndd (fstd i0) ,nd sndd (sndd i0)))
  TmPath' Γ' (A' ,d A'') θ1 θ2 δ = {!!} 
  TmPath' Γ' (substty Γ'' A θ) θ1 θ2 δ = {!!}

  idb Z = <>
  idb (S n) = ((idb n , idc n) , idb n , idc n) , {!(idp · (Boundary n) · (idbtm n)){<>}!}
  -- grrrrr 

  idc Z = a
  idc (S n) = id


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
