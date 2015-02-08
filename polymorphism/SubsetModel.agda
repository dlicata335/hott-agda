
-- FIXME: something went wrong in the library update---runs out of memory now

{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude


module polymorphism.SubsetModel where

  record Ctx : Type where
    constructor ctx
    field
     Ob   : Type
     Good : Ob -> Type
  open Ctx

  record Subst (Γ Δ : Ctx) : Type where
    constructor sub
    field
      sob   : Ob Γ -> Ob Δ
      sresp : (x0 : Ob Γ) (x1 : Good Γ x0) → Good Δ (sob x0)

  record Ty (Γ : Ctx) : Type where
    constructor ty
    field
      TOb : Ob Γ -> Type
      TGood : (x0 : Ob Γ) (x1 : Good Γ x0) → (TOb x0 → Type)
  open Ty

  record Tm {Γ : Ctx} (A : Ty Γ) : Type where
    constructor tm 
    field
      mob   : (g0 : Ob Γ) -> TOb A g0
      mresp : (g0 : Ob Γ) (g1 : Good Γ g0) → TGood A g0 g1 (mob g0)

  tysubst : {Γ Δ : Ctx} (A : Ty Δ) -> Subst Γ Δ -> Ty Γ
  tysubst (ty A0 A1) (sub θ0 θ1) = ty (λ g0 → A0 (θ0 g0)) (λ g0 g1 a0 → A1 (θ0 g0) (θ1 g0 g1) a0)

  tmsubst : {Γ Δ : Ctx} {A : Ty Δ} (M : Tm A) -> (θ : Subst Γ Δ) -> Tm (tysubst A θ)
  tmsubst (tm M0 M1) (sub θ0 θ1) = tm (λ g0 → M0 (θ0 g0)) (λ g0 g1 → M1 (θ0 g0) (θ1 g0 g1))

  1c : Ctx
  1c = ctx Unit (\ _ -> Unit)

  ∫ : {Γ : Ctx} (A : Ty Γ) -> Ctx
  ∫ {(ctx Γ0 Γ1)} (ty A0 A1) = ctx (Σ A0) (λ p → Σ (λ (p0 : Γ1 (fst p)) → A1 (fst p) p0 (snd p)))

  ids : {Γ : Ctx} -> Subst Γ Γ
  ids = sub (λ x → x) (λ x y → y)

  p : {Γ : Ctx} (A : Ty Γ) -> Subst (∫ A) Γ
  p _ = sub fst (λ x0 x1 → fst x1)

  v : {Γ : Ctx} (A : Ty Γ) -> Tm (tysubst A (p A))
  v A = tm snd (λ x0 x1 → snd x1)

  _,,_ : {Γ Δ : Ctx} {A : Ty Δ} (θ : Subst Γ Δ) -> Tm (tysubst A θ) -> Subst Γ (∫ A)
  _,,_ (sub θ0 θ1) (tm M0 M1) = sub (λ x → θ0 x , M0 x) (λ x0 x1 → θ1 x0 x1 , M1 x0 x1)

  -- Pi types --

  Π : {Γ : Ctx} -> (A : Ty Γ) (B : Ty (∫ A)) -> Ty Γ 
  Π (ty A0 A1) (ty B0 B1) = ty (λ g → (x : A0 g) → B0 (g , x)) 
                               (λ g0 g1 f → (a0 : A0 g0) (a1 : A1 g0 g1 a0) → B1 (g0 , a0) (g1 , a1) (f a0))

  _⇒_ : {Γ : Ctx} -> (A : Ty Γ) (B : Ty Γ) -> Ty Γ 
  _⇒_ A B = Π A (tysubst B (p A))

  lam : {Γ : Ctx} -> (A : Ty Γ) (B : Ty (∫ A)) -> Tm B -> Tm (Π A B)
  lam A B (tm M0 M1) = tm (λ g0 a0 → M0 (g0 , a0)) (λ g0 g1 a0 a1 → M1 (g0 , a0) (g1 , a1))

  unlam : {Γ : Ctx} -> (A : Ty Γ) (B : Ty (∫ A)) -> Tm (Π A B) -> Tm B
  unlam A B (tm M0 M1) = tm (λ p → M0 (fst p) (snd p)) (λ p0 p1 → M1 (fst p0) (fst p1) (snd p0) (snd p1))

  -- should check these, but they're really definitional! 
  Πη : {Γ : Ctx} -> (A : Ty Γ) (B : Ty (∫ A)) -> (f : Tm (Π A B)) -> f ≃ lam A B (unlam A B f)
  Πη (ty A0 A1) (ty B0 B1) (tm f0 f1) = id

  Πβ : {Γ : Ctx} -> (A : Ty Γ) (B : Ty (∫ A)) -> (M : Tm B) -> M ≃ unlam A B (lam A B M)
  Πβ (ty A0 A1) (ty B0 B1) (tm f0 f1) = id

  -- can derive application
  app : {Γ : Ctx} -> (A : Ty Γ) (B : Ty (∫ A)) -> Tm (Π A B) -> (M : Tm A)
      -> Tm (tysubst B (ids ,, M))
  app A B f a = tmsubst (unlam A B f) (ids ,, a)


  -- Sigma types --

  Σt : {Γ : Ctx} -> (A : Ty Γ) (B : Ty (∫ A)) -> Ty Γ 
  Σt (ty A0 A1) (ty B0 B1) = ty (λ g0 → Σ (λ x → B0 (g0 , x))) (λ g0 g1 p → Σ (λ (a1 : A1 g0 g1 (fst p)) → B1 (g0 , fst p) (g1 , a1) (snd p)))

  pair : {Γ : Ctx} -> (A : Ty Γ) (B : Ty (∫ A)) -> (M : Tm A) -> Tm (tysubst B (ids ,, M)) -> Tm (Σt A B)
  pair _ _ (tm M0 M1) (tm N0 N1) = tm (λ g0 → M0 g0 , N0 g0) (λ g0 g1 → M1 g0 g1 , N1 g0 g1)

  -- FIXME projections and beta/eta

  -- identity types --

  ID : {Γ : Ctx} (A : Ty Γ) (M N : Tm A) -> Ty Γ
  ID (ty A0 A1) (tm M0 M1) (tm N0 N1) =
    ty (λ g0 → Id (M0 g0) (N0 g0)) (λ g0 g1 α → Id (transport (A1 g0 g1) α (M1 g0 g1)) (N1 g0 g1))

  refl : {Γ : Ctx} {A : Ty Γ} (M : Tm A) -> Tm (ID A M M)
  refl M = tm (λ _ → id) (λ _ _ → id)

  sbst :  {Γ : Ctx} {A : Ty Γ} (B : Ty (∫ A)) {M1 M2 : Tm A} (α : Tm (ID A M1 M2))
       -> Tm (tysubst B (ids ,, M1))
       -> Tm (tysubst B (ids ,, M2))
  sbst {ctx Γ0 Γ1} {(ty A0 A1)} (ty B0 B1) (tm α0 α1) (tm s0 s1) = 
       tm (λ g0 → transport (λ x → B0 (g0 , x)) (α0 g0) (s0 g0))
          (λ g0 g1 → transport (λ (p' : Σ \ (x0 : Σ A0) → Σ (λ p0 → A1 (fst x0) p0 (snd x0)) × B0 x0) -> B1 (fst p') (fst (snd p')) (snd (snd p'))) 
                        (pair≃ (pair≃ id (α0 g0)) {!!})
                        (s1 g0 g1))

  contract' : {Γ : Ctx} {A : Ty Γ} (M N : Tm A) (P : Tm (ID A M N)) 
           -> Tm (ID (Σt A (ID (tysubst A (p A)) (tmsubst M (p A)) (v A))) (pair A (ID (tysubst A (p A)) (tmsubst M (p A)) (v A)) M (refl M)) (pair A (ID (tysubst A (p A)) (tmsubst M (p A)) (v A)) N P))
  contract' (tm M0 M1) (tm N0 N1) (tm P0 P1) = tm (λ g0 → pair≃ (P0 g0) (transport-Path-right (P0 g0) id)) 
                                                  (λ g0 g1 → {!!})

  -- FIXME: finish and check computation rules
  
  
  -- universe --

  U : ∀ {Γ} -> Ty Γ
  U = ty (λ _ → Type) (λ _ _ A → A → Type)

  El : ∀ {Γ} -> Tm (U{Γ}) -> Ty Γ
  El (tm A0 A1) = ty A0 A1

  Equivt : ∀ {Γ} -> (A B : Tm {Γ} U) -> Type
  Equivt {Γ} A B = Σ \ (l : Tm {∫ (El A)} (El (tmsubst B (p (El A))))) -> 
            Σ \ (r : Tm {∫ (El B)} (El (tmsubst A (p (El B))))) -> 
            Tm {∫ (El B)} (ID (El (tmsubst B (p (El B)))) (tmsubst l (_,,_ {∫ (El B)} {Γ} {El A} (p (El B)) r)) (v (El B)))
          × Tm {∫ (El A)} (ID (El (tmsubst A (p (El A)))) (tmsubst r (_,,_ {∫ (El A)} {Γ} {El B} (p (El A)) l)) (v (El A)))

{- FIXME used to typecheck
  univalencet : ∀ {Γ} {A B : Tm (U{Γ})} -> Equivt A B -> Tm (ID U A B)
  univalencet {Γ}{tm A0 A1}{tm B0 B1} (tm l0 l1 , tm r0 r1 , tm α0 α1 , tm β0 β1) =
              tm (\ g0 -> (ua (equiv1 g0)))
                 (λ g0 g1 → λ≃ (λ b0 → ua (improve (hequiv 
                                                  (λ a1 → transport (B1 g0 g1) (α0 (g0 , b0))
                                                                (l1 (g0 , r0 (g0 , b0)) 
                                                                (g1 , transport (A1 g0 g1) (ap≃ type≃β!) a1)))
                                                  (λ b1 → transport (A1 g0 g1) (! (ap≃ type≃β!))
                                                                (r1 (g0 , b0) (g1 , b1)))
                                                  (λ a1 → ap≃
                                                            (transport-inv-1 (A1 g0 g1) (ap≃ (type≃β! {_} {_}))) ∘
                                                            ap (transport (A1 g0 g1) (! (ap≃ type≃β!)))
                                                            (β1 (g0 , r0 (g0 , b0))
                                                             (g1 , transport (A1 g0 g1) (ap≃ type≃β!) a1))
                                                            ∘ ap (transport (A1 g0 g1) (! (ap≃ type≃β!))) 
                                                                   ({! (! (respd r1 (pair≃ id (α0 (g0 , b0))))) !})) 
                                                  (λ b1 → α1 (g0 , b0) (g1 , b1) 
                                                          ∘ ap (λ x → transport (B1 g0 g1) (α0 (g0 , b0)) (l1 (g0 , r0 (g0 , b0)) (g1 , x)))
                                                              (ap≃ (transport-inv-2 (A1 g0 g1) (ap≃ (type≃β! {_} {_} {(equiv1 g0)}))))))))
                            -- ENH avoid copying and pasting the whole above term
                            ∘ transport-→-pre (ua (equiv1 g0)) _)
              where equiv1 : (g0 : Ob Γ) -> Equiv (A0 g0) (B0 g0)
                    equiv1 g0 =  (improve (hequiv (λ a0 → l0 (g0 , a0)) 
                                                  (λ b0 → r0 (g0 , b0))
                                                  (λ a0 → β0 (g0 , a0))
                                                  (λ b0 → α0 (g0 , b0))))
-}

  -- universe of with h-prop valued relations

  -- FIXME: what do you get if you say this internally?  
  -- this is probably wrong

  HSets  = NTypes (tl 0)
  HProps = NTypes (S -2)

  hset : ∀ {Γ} -> Ty Γ
  hset = ty (λ _ → HSets) (λ _ _ A → fst A → HProps)

  El-hset : ∀ {Γ} -> Tm hset -> Ty Γ
  El-hset (tm A0 A1) = ty (\ g0 -> fst (A0 g0)) (\ g0 g1 a0 -> fst (A1 g0 g1 a0))


  -- proof irrelevant universe --

  Propo : ∀ {Γ} -> Ty Γ
  Propo = ty (λ _ → Type) (λ _ _ _ → Unit)

  Prf : ∀ {Γ} -> Tm {Γ} Propo -> Ty Γ
  Prf (tm P0 P1) = ty (λ _ → Unit) (λ x0 _ _ → P0 x0)

  -- irrel : ∀ {Γ} {P : Tm {Γ} Propo} -> (M N : Tm (Prf P)) -> Tm (ID (Prf P) M N)
  -- irrel {Γ} {tm P0 P1} (tm M0 M1) (tm N0 N1) = tm (λ _ → id) (λ g0 g1 → {!!}) -- would need Propo to be hprops

  -- could define irrel for leibniz equality, following hofmann


  -- codisceteness 
  # : ∀ {Γ} -> Ty Γ -> Ty Γ
  # (ty A0 A1) = ty (\ _ -> Unit) (λ g0 g1 _ → Σ (A1 g0 g1))


  module Example where
    -- example
    idty : ∀ {Γ} -> Ty Γ
    idty {Γ} = Π U (Π (El (v{Γ} U)) (El (tmsubst (v {Γ} U) (p (El (v {Γ} U)))))) 
  
    idfun : ∀ {Γ} -> Tm (idty{Γ})
    idfun {Γ} = lam U
                    (Π (El (v {Γ} U)) (El (tmsubst (v {Γ} U) (p (El (v {Γ} U)))))) 
                    (lam (El (v {Γ} U)) (El (tmsubst (v {Γ} U) (p (El (v {Γ} U))))) 
                     (v (El (v {Γ} U))))
  
    {-
    eta-doesntwork : Tm{1c} (Π (idty{1c}) (ID idty (v (idty{1c})) idfun))
    eta-doesntwork = tm (λ _ f → {!!}) {!!}
      -- need Id f (λ a0 a1 → a1)
    -}

    eta : ∀ {Γ} 
        -> Tm{Γ} (Π (idty{Γ}) (# (ID idty (v (idty{Γ})) idfun)))
    eta {Γ} = tm _ (λ g0 g1 f0 f1 → (λ≃ (λ A → λ≃ (λ x → f1 A (λ y → Id y x) x id))) , 
                                    {!f1!}) -- FIXME need some higher-dimensional naturality?  


  -- if you restrict to hsets it goes through
  module ExampleHSet where

    idty : ∀ {Γ} -> Ty Γ
    idty {Γ} = Π hset (Π (El-hset (v{Γ} hset)) (El-hset (tmsubst (v {Γ} hset) (p (El-hset (v {Γ} hset)))))) 
  
    idfun : ∀ {Γ} -> Tm (idty{Γ})
    idfun {Γ} = lam hset
                    (Π (El-hset (v {Γ} hset)) (El-hset (tmsubst (v {Γ} hset) (p (El-hset (v {Γ} hset)))))) 
                    (lam (El-hset (v {Γ} hset)) (El-hset (tmsubst (v {Γ} hset) (p (El-hset (v {Γ} hset))))) 
                     (v (El-hset (v {Γ} hset))))


    {- FIXME used to typecheck
    eta : ∀ {Γ} 
        -> Tm{Γ} (Π (idty{Γ}) (# (ID idty (v (idty{Γ})) idfun)))
    eta {Γ} = tm _ (λ g0 g1 f0 f1 → (λ≃ (λ A → λ≃ (λ x → f1 A (λ y → Id y x , (snd A _ _)) x id))) , 
                                        λ≃ (λ a0 → λ≃ (λ a1 → λ≃ (λ a2 → λ≃ (λ a23 → snd (a1 a2) _ _)))))
    -} 
