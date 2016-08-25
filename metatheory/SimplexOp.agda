{-# OPTIONS --type-in-type #-}

open import lib.Prelude
open ListM
open Index

module metatheory.SimplexOp where

  split-∈++-≤ : ∀ {A} {xs ys : List A} (i j : Pos (xs ++ ys))
                 → i ≤ j
                 → Either (Σ \ i' → Σ \ j' → (split-∈++ {xs = xs} (snd i) == Inl i') × (split-∈++ {xs = xs} (snd j) == Inl j') × (_ , i') ≤ (_ , j') )
                          (Either (Σ (λ i' → Σ (λ j' → (split-∈++ {xs = xs} (snd i) == Inl i') × (split-∈++ {xs = xs} (snd j) == Inr j')))) 
                                  (Σ (λ i' → Σ (λ j' → (split-∈++ {xs = xs} (snd i) == Inr i') × (split-∈++ {xs = xs} (snd j) == Inr j') × (_ , i') ≤ (_ , j')))))
  split-∈++-≤ {xs = []} i j lt = Inr (Inr (_ , _ , id , id , lt))
  split-∈++-≤ {xs = .x :: xs} (x , i0) (.x , i0) lt = Inl (_ , _ , id , id , ≤-refl _)
  split-∈++-≤ {xs = .x :: xs} (x , i0) .(js , iS j) (LtZ (js , iS j)) with split-∈++ {xs = xs} j 
  ... | Inl i' = Inl (i0 , iS i' , id , id , LtZ _)
  ... | Inr j' = Inr (Inl (i0 , j' , id , id))
  split-∈++-≤ {xs = .x :: xs} (is , iS i) (x , i0) ()
  split-∈++-≤ {xs = x :: xs} (._ , iS ._) (._ , iS ._) (LtS {i = is , i} {i' = js , j} lt) with split-∈++-≤ {xs = xs} _ _ lt 
  ... | Inl (i' , j' , eqi , eqj , l) with split-∈++ {xs = xs} i | eqi | split-∈++ {xs = xs} j | eqj
  ...                                    | ._ | id | ._ | id  = Inl (iS i' , iS j' , id , id , LtS l)
  split-∈++-≤ {xs = x :: xs} (._ , iS ._) (._ , iS ._) (LtS {i = is , i} {i' = js , j} lt) | Inr (Inl (i' , j' , eqi , eqj)) with split-∈++ {xs = xs} i | eqi | split-∈++ {xs = xs} j | eqj
  ...                                                                                                                              | ._ | id | ._ | id = Inr (Inl (iS i' , j' , id , id))
  split-∈++-≤ {xs = x :: xs} (._ , iS ._) (._ , iS ._) (LtS {i = is , i} {i' = js , j} lt) | Inr (Inr (i' , j' , eqi , eqj , l)) with split-∈++ {xs = xs} i | eqi | split-∈++ {xs = xs} j | eqj
  ...                                                                                                                              | ._ | id | ._ | id = Inr (Inr (i' , j' , id , id , l))

  ----------------------------------------------------------------------

  _⊩_ : List String → List String → Set 
  Ψ ⊩ Ψ' = Σ \ (f : Pos Ψ' → Pos Ψ) 
           → {y y' : Pos Ψ'} → y ≤ y' → f y ≤ f y'

  reflect : ∀ {Ψ Ψ'} → Ψ ⊩ Ψ' → rev Ψ ⊩ rev Ψ'
  reflect {Ψ}{Ψ'} (f , mf) = (λ i → same-index-in-rev (f (transport Pos (rev-rev Ψ') (same-index-in-rev i)))) , 
                              (λ lt → same-index-in-rev≤ (mf (transport≤ (rev-rev Ψ') (same-index-in-rev≤ lt))))

  ident⊩ : ∀ {Ψ} → Ψ ⊩ Ψ 
  ident⊩ = (λ x → x) , (λ lt → lt)

  compose⊩ : ∀ {Ψ Ψ' Ψ''} 
           → Ψ ⊩ Ψ'
           → Ψ' ⊩ Ψ''
           → Ψ ⊩ Ψ''
  compose⊩ (ρf , ρm) (ρf' , ρm') = (λ x → ρf (ρf' x)) , (λ lt → ρm (ρm' lt))

  Nil  : ∀ {Ψ} → Ψ ⊩ []
  Nil = noPos[] , (λ {i} → noPos[] i)

  Cons : ∀ {Ψ Ψ'} Ψ1 x {Ψ2} y 
        → Ψ == (Ψ1 ++ (x :: Ψ2)) 
        → (x :: Ψ2) ⊩ Ψ'
        → Ψ ⊩ (y :: Ψ')
  Cons {Ψ' = Ψ'} Ψ1 x {Ψ2} y id (ρf , ρm) = consf , consm where
    consf : Pos (y :: Ψ') → Pos (Ψ1 ++ (x :: Ψ2))
    consf (._ , i0) = x , index {_} {Ψ1} {x}
    consf (_ , iS i) = _ , iSMany Ψ1 (snd (ρf (_ , i)))

    consm : ∀ {i j : Pos (y :: Ψ')} → i ≤ j → consf i ≤ consf j
    consm (LtZ (._ , i0)) = ≤-refl _ 
    consm (LtZ (_ , iS i)) = iSMany≤ Ψ1 (LtZ _) 
    consm (LtS lt) = iSMany≤ Ψ1 (ρm lt) 
  lweaken : ∀ {Ψ Ψ' Ψ0} → Ψ ⊩ Ψ' → (Ψ0 ++ Ψ ⊩ Ψ')
  lweaken {Ψ0 = Ψ0} (ρf , ρm) = (λ i → _ , iSMany Ψ0 (snd (ρf i))) , (λ lt → iSMany≤ Ψ0 (ρm lt))

  rweaken : ∀ {Ψ Ψ2' Ψ'} → Ψ ⊩ Ψ' → (Ψ ++ Ψ2') ⊩ Ψ'
  rweaken (ρf , ρm) = (λ i → _ , iSManyRight (snd (ρf i))) , (λ lt → iSManyRight≤ (ρm lt)) 

  ConsR' : ∀ Ψ1 x y Ψ'
         → (Ψ1 ++ [ x ]) ⊩ Ψ'
         → (Ψ1 ++ [ x ]) ⊩ (Ψ' ++ [ y ])
  ConsR' Ψ1 x y Ψ' (ρ , ρm) = cf , cm where
    cf : Pos (append Ψ' (y :: [])) → Pos (append Ψ1 (x :: []))
    cf i with split-∈++ {xs = Ψ'} (snd i) 
    ... | Inl i' = ρ (_ , i')
    cf (._ , _) | Inr i0 = _ , iSMany Ψ1 i0
    ... | Inr (iS ()) 
  
    cm : {i : Pos (Ψ' ++ [ y ])} {j : Pos (Ψ' ++ [ y ])} → i ≤ j → cf i ≤ cf j
    cm {i} {j} lt with split-∈++ {xs = Ψ'} (snd i) | split-∈++ {xs = Ψ'} (snd j) | split-∈++-≤ {xs = Ψ'} i j lt 
    cm lt | .(Inl i') | .(Inl j') | Inl (i' , j' , id , id , l) = ρm l
    cm lt | .(Inl i') | .(Inr i0) | Inr (Inl (i' , i0 , id , id)) = ≤-last {xs = Ψ1} (ρ (_ , i'))
    cm lt | .(Inl i') | .(Inr (iS _)) | Inr (Inl (i' , iS () , id , id))
    cm lt | .(Inr i0) | .(Inr i0) | Inr (Inr (i0 , i0 , id , id , l)) = ≤-refl _
    cm lt | .(Inr i0) | ._ | Inr (Inr (i0 , iS () , id , id , l))
    cm lt | .(Inr (iS _)) | .(Inr i0) | Inr (Inr (iS () , i0 , id , id , l)) 
    cm lt | .(Inr (iS _)) | .(Inr (iS j')) | Inr (Inr (iS () , iS j' , id , id , l)) 

  ConsR : ∀ {Ψ Ψ'} Ψ1 x {Ψ2} y 
         → Ψ == (Ψ1 ++ (x :: Ψ2)) 
         → (Ψ1 ++ [ x ]) ⊩ Ψ'
         → Ψ ⊩ (Ψ' ++ [ y ])
  ConsR Ψ1 x {Ψ2} y id ρ = transport (λ h → h ⊩ _) (! (append-assoc Ψ1 [ x ] Ψ2)) (rweaken {Ψ2' = Ψ2} (ConsR' Ψ1 x y _ ρ))

  extend : ∀ {Ψ Ψ' x y x' y'} 
           → (x :: (Ψ ++ [ y ])) ⊩ Ψ'
           → (x :: (Ψ ++ [ y ])) ⊩ (x' :: (Ψ' ++ [ y' ]))
  extend {Ψ}{Ψ'}{x}{y}{x'}{y'} ρ = Cons [] x {Ψ ++ [ y ]} x' id (ConsR (x :: Ψ) y y' id ρ)

  compose' : ∀ {Ψ Ψ' Ψ'' x y x' y'} 
           → (x :: (Ψ ++ [ y ])) ⊩ Ψ'
           → (x' :: (Ψ' ++ [ y' ])) ⊩ Ψ''
           → (x :: (Ψ ++ [ y ])) ⊩ Ψ''
  compose' {Ψ} {Ψ'} {Ψ''} {x} {y} {x'} {y'} ρ ρ' =
    compose⊩ {Ψ = x :: (Ψ ++ [ y ])} {Ψ' = x' :: (Ψ' ++ [ y' ])} {Ψ'' = Ψ''} 
              (extend {Ψ} {Ψ'} {x} {y} {x'} {y'} ρ)
              ρ'

  ----------------------------------------------------------------------

  data _⊩'_ : List String → List String → Set where
    Nil'  : ∀ {Ψ} → Ψ ⊩' []
    Cons' : ∀ {Ψ Ψ'} Ψ1 x {Ψ2} y 
         → Ψ == (Ψ1 ++ (x :: Ψ2)) 
         → (x :: Ψ2) ⊩' Ψ'
         → Ψ ⊩' (y :: Ψ')

  reify : ∀ {Ψ Ψ'} → Ψ ⊩ Ψ' → Ψ ⊩' Ψ'
  reify {Ψ' = []} ρ = Nil'
  reify {Ψ' = y :: Ψ'} ρ with splitat (snd (fst ρ (y , i0)))
  ... | (Ψ1 , Ψ2 , eq) = Cons' Ψ1 (fst (fst ρ (y , i0))) y eq (reify {Ψ' = Ψ'} (ρ'f , {!monotonicity!})) where
    ρ'f : Pos Ψ' → Pos (fst (fst ρ (y , i0)) :: Ψ2)
    ρ'f i with split-∈++ {xs = Ψ1} (transport (\ x → _ ∈ x) eq (snd (fst ρ (_ , iS (snd i)))))
    ...      | Inl p = {!!} -- get a contraction from monotonicity of ρ
    ...      | Inr q = _ , q

  ----------------------------------------------------------------------

  data Variance : Set where
    + - : Variance

  Ctx : Set 
  Ctx = List String × Variance

  ⊥ : Variance → String
  ⊥ + = "0"
  ⊥ - = "1"

  ⊤ : Variance → String
  ⊤ + = "1"
  ⊤ - = "0"

  _opv : Variance → Variance
  + opv = -
  - opv = +

  data _⊢_ : Ctx → Ctx → Set where
    co  : ∀ {Ψ1 Ψ2 v} → (⊥ v :: (Ψ1 ++ [ ⊤ v ])) ⊩ Ψ2 → (Ψ1 , v) ⊢ (Ψ2 , v) 
    con : ∀ {Ψ1 Ψ2 v} → (⊥ v :: (rev Ψ1 ++ [ ⊤ v ])) ⊩ Ψ2 → (Ψ1 , v opv) ⊢ (Ψ2 , v) 

  ident' : ∀ {x y} Ψ → (x :: (Ψ ++ [ y ])) ⊩ Ψ
  ident' {x} Ψ = rweaken (lweaken {Ψ0 = [ x ]} ident⊩ )

  ident : ∀ Ψ → Ψ ⊢ Ψ
  ident (Ψ , v) = co (ident' Ψ)

  opv-invol : ∀ {v} → (v opv) opv == v
  opv-invol {+} = id
  opv-invol { - } = id

  opv-flip : ∀ {v} → ⊤ (v opv) == ⊥ v
  opv-flip {+} = id
  opv-flip { - } = id

  opv-flip' : ∀ {v} → ⊥ (v opv) == ⊤ v
  opv-flip' {+} = id
  opv-flip' { - } = id

  compose : ∀ {Ψ Ψ' Ψ''} → Ψ ⊢ Ψ' → Ψ' ⊢ Ψ'' → Ψ ⊢ Ψ''
  compose {Ψ , v} {Ψ' , .v} {Ψ'' , .v} (co ρ) (co ρ') = co (compose' {Ψ = Ψ} {Ψ' = Ψ'} {Ψ'' = Ψ''} ρ ρ')
  compose {Ψ , .(v opv)} {Ψ' , v} {Ψ'' , .v} (con ρ) (co ρ') = con (compose' {Ψ = rev Ψ} {Ψ' = Ψ'} {Ψ'' = Ψ''} ρ ρ')
  compose {Ψ , .(v opv)} {Ψ' , .(v opv)} {Ψ'' , v} (co ρ) (con ρ') = 
    con (transport (λ h → h :: (rev Ψ ++ [ ⊤ v ]) ⊩ Ψ'') 
                   (opv-flip {v})
           (transport (λ h → (⊤ (v opv)) :: (rev Ψ ++ [ h ]) ⊩ Ψ'') 
                      (opv-flip' {v}) 
             (compose' {Ψ = rev Ψ} {x = ⊤ (v opv)} {y = ⊥ (v opv)} {x' = ⊥ v} {y' = ⊤ v}
               (transport (λ h → h ⊩ _) (ap (λ h → h ++ [ ⊥ (v opv) ]) (rev-append Ψ [ ⊤ (v opv) ]))
                          (reflect ρ))
               ρ')))
  compose {Ψ , .((v opv) opv)} {Ψ' , .(v opv)} {Ψ'' , v} (con ρ) (con ρ') = 
    transport (λ h → (Ψ , h) ⊢ (Ψ'' , v)) (! (opv-invol {v})) 
              (co (compose' {Ψ = Ψ}
                     (transport (λ h → h ⊩ _)
                      (ap2 _::_ (opv-flip {v}) (ap2 _++_ (rev-rev Ψ) (ap [_] (opv-flip' {v}))) ∘
                       ap (λ h → h ++ [ ⊥ (v opv) ]) (rev-append (rev Ψ) [ ⊤ (v opv) ]))
                      (reflect ρ))
                     ρ'))
  
  _op : Ctx → Ctx
  (Ψ , v) op = (rev Ψ , v opv)

  op-invol : ∀ {Ψ} → (Ψ op) op == Ψ
  op-invol {Ψ , v} = ap2 _,_ (rev-rev Ψ) (opv-invol {v})

  r : ∀ {Ψ} → Ψ ⊢ Ψ op
  r {Ψ , + } = con (ident' _) 
  r {Ψ , - } = con (ident' _) 

  ----------------------------------------------------------------------
  -- 0 and 1 simplices

  ·co : ∀ {v} → ([ "x" ] , v) ⊢ ([] , v)
  ·co = co Nil

  ·con : ∀ {v} → ([ "x" ] , v opv) ⊢ ([] , v)
  ·con = con Nil

  0/x+1 : ([] , +) ⊢ ([ "x" ] , +)
  0/x+1 = co (Cons [] "0" "x" id Nil)

  1/x+1 : ([] , +) ⊢ ([ "x" ] , +)
  1/x+1 = co (Cons ["0"] "1" "x" id Nil)

  0/x-1 : ([] , -) ⊢ ([ "x" ] , -)
  0/x-1 = co (Cons [ "1" ] "0" "x" id Nil) 

  1/x-1 : ([] , -) ⊢ ([ "x" ] , -)
  1/x-1 = co (Cons [] "1" "x" id Nil) 

  r1+ : ("x" :: [] , +) ⊢ ("x" :: [] , -)
  r1+ = r {"x" :: [] , + }

  r1- : ("x" :: [] , -) ⊢ ("x" :: [] , +)
  r1- = r {"x" :: [] , - }

  test0 : ([] , +) ⊢ ("x" :: [] , -)
  test0 = (compose 0/x+1 r1+)

  ----------------------------------------------------------------------

  r2+ = r {"x" :: "y" :: [] , + }
  r2- = r {"y" :: "x" :: [] , - }

  0/x+2 : ([ "y" ] , +) ⊢ ("x" :: "y" :: [] , +)
  0/x+2 = co (Cons [] "0" "x" id (Cons [ "0" ] "y" "y" id Nil))

  0/y+1 : ([] , +) ⊢ ([ "y" ] , +)
  0/y+1 = co (Cons [] "0" "y" id Nil)

  1/y+1 : ([] , +) ⊢ ([ "y" ] , +)
  1/y+1 = co (Cons [ "0" ] "1" "y" id Nil)

  test1 : ([ "y" ] , +) ⊢ ("y" :: "x" :: [] , -)
  test1 = compose 0/x+2 r2+

  test2 : ([] , +) ⊢ ("x" :: "y" :: [] , +)
  test2 = compose 1/y+1 0/x+2

  test3 : ([ "y" ] , -) ⊢ ("y" :: "x" :: [] , -)
  test3 = compose r (compose 0/x+2 r2+)

  ----------------------------------------------------------------------

  run : ∀ {Ψ} {Ψ'} {x} → Ψ ⊢ Ψ' → x ∈ fst Ψ' → String
  run (co ρ) i = fst (fst ρ (_ , i))
  run (con ρ) i = fst (fst ρ (_ , i))

  run2 : ∀ {Ψ} {Ψ'}→ Ψ ⊢ Ψ' → Σ \ Ψ'' → Ψ'' ⊩' fst Ψ'
  run2 (co ρ) = _ , reify ρ
  run2 (con ρ) = _ , reify ρ

  
