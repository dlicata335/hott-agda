{-# OPTIONS --type-in-type --without-K #-}

open import lib.BasicTypes 

module lib.cubical.Cubes (A : Type) (a : A) where

  data Ctx : Type 
  interpc : Ctx → Type
  Boundary : Nat → Ctx 
  idb : (n : Nat) → interpc (Boundary n)
  Cube : (n : Nat) → interpc (Boundary n) → Type 
  data CubeS (n : Nat) : interpc (Boundary (S n)) → Type 
  CtxPath : (Γ : Ctx) → (c1 c2 : interpc Γ) → Ctx
  idp : (n : Nat) (b : interpc(Boundary n)) → interpc (CtxPath (Boundary n) b b)
  CtxPathOver : {Γ : Ctx} {b1 : interpc Γ} (Γ' : interpc Γ → Ctx)
               {b2 : interpc Γ} 
                → interpc (CtxPath Γ b1 b2) →
                interpc (Γ' b1) → interpc (Γ' b2) → Ctx

  data Ctx where
    · : Ctx
    cube : (n : Nat) → interpc (Boundary n) → Ctx
    _×c_ : Ctx → Ctx → Ctx
    Σc : (Γ : Ctx) (b : interpc Γ → Ctx) → Ctx

  interpc · = Unit
  interpc (Γ ×c Γ₁) = interpc Γ × interpc Γ₁
  interpc (Σc Γ Γ') = Σ (λ (x : interpc Γ) → interpc (Γ' x))
  interpc (cube n b) = Cube n b

  Boundary Z = ·
  Boundary (S n) = Σc ((Σc (Boundary n) (\ x -> cube n x)) ×c (Σc (Boundary n) (\ x -> cube n x))) (λ { ((b1 , _) , b2 , _) → CtxPath (Boundary n) b1 b2 })

  Cube 0 _ = A
  Cube (S n) = CubeS n

  data CubeS (n : Nat) where
    id : CubeS n (idb (S n))

  idc : (n : Nat) → Cube n (idb n)
  idc Z = a
  idc (S n) = id

  idb Z = <>
  idb (S n) = ((idb n , idc n) , idb n , idc n) , idp n (idb n)

  CtxPath · c1 c2 = ·
  CtxPath (cube n x) c1 c2 = cube (S n) (((x , c1) , (x , c2)) , idp n x)
  CtxPath (Γ ×c Γ₁) c1 c2 = CtxPath Γ (fst c1) (fst c2) ×c CtxPath Γ₁ (snd c1) (snd c2)
  CtxPath (Σc Γ Γ') c1 c2 = Σc (CtxPath Γ (fst c1) (fst c2)) (λ α → CtxPathOver {Γ} Γ' α (snd c1) (snd c2))

  -- need to look at Γ'
  CtxPathOver = {!!}
    

  idp = {!!}

  test1 : interpc (Boundary 1)
  test1 = ((<> , {!!}) , (<> , {!!})) , <>

  test2 : interpc (Boundary 2)
  test2 = (((((<> , {!!}) , ({!!} , {!!})) , <>) , {!!}) , ((((<> , {!!}) , (<> , {!!})) , <>) , {!!})) ,
          (((<> , {!!}) , (<> , {!!})) , {!!})
