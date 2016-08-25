{-# OPTIONS --type-in-type #-}

open import lib.Prelude
open ListM

module misc.SimplexOp6 where

  append-rh-[] : ∀ {A} (xs : List A) → (append xs []) == xs
  append-rh-[] [] = id
  append-rh-[] (x :: xs) = ap2 _::_ id (append-rh-[] xs)

  append-assoc : ∀ {A} (xs ys zs : List A) → (append xs (append ys zs)) == (append (append xs ys) zs)
  append-assoc [] ys zs = id
  append-assoc (x :: xs) ys zs = ap2 _::_ id (append-assoc xs ys zs)

  rev-append : ∀ {A} (xs ys : List A) → rev (xs ++ ys) == rev ys ++ rev xs
  rev-append [] ys = ! (append-rh-[] (rev ys))
  rev-append (x :: xs) ys = ! (append-assoc (rev ys) (rev xs) [ x ]) ∘ ap (λ h → h ++ [ x ]) (rev-append xs ys)

  rev-rev : ∀ {A} (xs : List A) → rev (rev xs) == xs
  rev-rev [] = id
  rev-rev (x :: xs) = ap (_::_ x) (rev-rev xs) ∘ rev-append (rev xs) [ x ]


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

  data _⊩_ : List String → List String → Set where
    Nil  : ∀ {Ψ} → Ψ ⊩ []
    Cons : ∀ {Ψ Ψ'} Ψ1 x {Ψ2} y 
         → Ψ == (Ψ1 ++ (x :: Ψ2)) 
         → (x :: Ψ2) ⊩ Ψ'
         → Ψ ⊩ (y :: Ψ')

  _opv : Variance → Variance
  + opv = -
  - opv = +

  data _⊢_ : Ctx → Ctx → Set where
    co  : ∀ {Ψ1 Ψ2 v} → (⊥ v :: (Ψ1 ++ [ ⊤ v ])) ⊩ Ψ2 → (Ψ1 , v) ⊢ (Ψ2 , v) 
    con : ∀ {Ψ1 Ψ2 v} → (⊥ (v opv) :: (Ψ1 ++ [ ⊤ (v opv) ])) ⊩ Ψ2 → (Ψ1 , v opv) ⊢ (Ψ2 , v) 

  lweaken : ∀ {Ψ Ψ' Ψ0} → Ψ ⊩ Ψ' → (Ψ0 ++ Ψ ⊩ Ψ')
  lweaken Nil = Nil
  lweaken {Ψ0 = Ψ0} (Cons Ψ1 x y s ρ) = Cons (Ψ0 ++ Ψ1) x y (append-assoc Ψ0 Ψ1 _ ∘ (ap (_++_ Ψ0) s)) ρ

  ident'' : ∀ Ψ → Ψ ⊩ Ψ
  ident'' [] = Nil
  ident'' (a :: Ψ) = Cons [] a a id (lweaken {Ψ0 = [ a ]} (ident'' Ψ))

  rweaken : ∀ {Ψ Ψ2' Ψ'} → Ψ ⊩ Ψ' → (Ψ ++ Ψ2') ⊩ Ψ'
  rweaken Nil = Nil
  rweaken {Ψ2' = Ψ2'} (Cons Ψ1 x {Ψ2} y s ρ) = 
    Cons Ψ1 x {Ψ2 = Ψ2 ++ Ψ2'} y (! (append-assoc Ψ1 (x :: Ψ2) Ψ2') ∘ ap (λ h → h ++ Ψ2') s) (rweaken ρ)

  ident' : ∀ {x y} Ψ → (x :: (Ψ ++ [ y ])) ⊩ Ψ
  ident' {x} Ψ = rweaken (lweaken {Ψ0 = [ x ]} (ident'' Ψ))

  ident : ∀ Ψ → Ψ ⊢ Ψ
  ident (Ψ , v) = co (ident' Ψ)

  uncons= : ∀ {A} {x y : A} {xs ys} → (x :: xs) == (y :: ys) → (x == y) × (xs == ys) 
  uncons= id = id , id
  
  unsnoc= : ∀ {A} {x y : A} xs ys → (xs ++ [ x ]) == (ys ++ [ y ]) → (xs == ys) × (x == y)
  unsnoc= [] [] id = id , id
  unsnoc= [] (y :: ys) eq = {!contra!}
  unsnoc= (x₁ :: xs) [] eq = {!contra!}
  unsnoc= (x₁ :: xs) (x₂ :: ys) eq with unsnoc= xs ys (snd (uncons= eq)) 
  ... | (a , b) = (ap2 _::_ (fst (uncons= eq)) a) , b

  -- match : ∀ {Ψ : List String} {x Ψ' x' Ψ''} 
  --       → (Ψ ++ [ x ]) == Ψ' ++ (x' :: Ψ'')
  --       → Either ((Ψ == Ψ') × (x == x') × (Ψ'' == []) )
  --                 (Σ (λ Ψ''' → Ψ'' == Ψ''' ++ [ x ]))
  -- match {Ψ} {x} {Ψ'} {x'} {Ψ'' = []} eq = Inl (fst (unsnoc= Ψ Ψ' eq) , (snd (unsnoc= Ψ Ψ' eq) , id))
  -- match {Ψ} {x} {Ψ'} {x'} {Ψ'' = x₁ :: Ψ''} eq = Inr ({!!} , {!!})

  match' : ∀ {Ψ : List String} {x Ψ' x' Ψ''} 
        → (Ψ ++ [ x ]) == Ψ' ++ (x' :: Ψ'')
        → (Σ \ Ψ2' → ((Ψ2' ++ [ x ]) == (x' :: Ψ'')))
  match' {Ψ} {x} {[]} {x'} {Ψ''} eq = Ψ , eq
  match' {[]} {x} {y :: Ψ'} {x'} {Ψ''} eq = {!contra!}
  match' {y1 :: Ψ} {x} {y :: Ψ'} {x'} {Ψ''} eq with fst (uncons= eq) 
  match' {y1 :: Ψ} {x} {.y1 :: Ψ'} {x'} {Ψ''} eq | id = match' {Ψ} {x} {Ψ'} {x'} {Ψ''} (snd (uncons= {xs = Ψ ++ [ x ]} {ys = Ψ' ++ x' :: Ψ''} eq) )

  ConsR' : ∀ Ψ1 x y Ψ'
         → (Ψ1 ++ [ x ]) ⊩ Ψ'
         → (Ψ1 ++ [ x ]) ⊩ (Ψ' ++ [ y ])
  ConsR' Ψ1 x y [] ρ = Cons Ψ1 x y id Nil
  ConsR' Ψ1 x y (y1 :: Ψ') (Cons Ψ1' x1 {Ψ2'} .y1 s ρ) with match' {Ψ1} {x} {Ψ1'} {x1} {Ψ2'} s 
  ... | (Ψ2'' , eq ) = Cons Ψ1' x1 {Ψ2'} y1 s (transport (λ h → h ⊩ _) eq (ConsR' Ψ2'' x y Ψ' (transport (λ h → h ⊩ _) (! eq) ρ)))

  ConsR : ∀ {Ψ Ψ'} Ψ1 x {Ψ2} y 
         → Ψ == (Ψ1 ++ (x :: Ψ2)) 
         → (Ψ1 ++ [ x ]) ⊩ Ψ'
         → Ψ ⊩ (Ψ' ++ [ y ])
  ConsR Ψ1 x {Ψ2} y id ρ = transport (λ h → h ⊩ _) (! (append-assoc Ψ1 [ x ] Ψ2)) (rweaken {Ψ2' = Ψ2} (ConsR' Ψ1 x y _ ρ))

  extend : ∀ {Ψ Ψ' x y x' y'} 
           → (x :: (Ψ ++ [ y ])) ⊩ Ψ'
           → (x :: (Ψ ++ [ y ])) ⊩ (x' :: (Ψ' ++ [ y' ]))
  extend {Ψ} {x = x} {y} {x'} {y'} ρ = Cons [] x {Ψ ++ [ y ]} x' id (ConsR (x :: Ψ) y y' id ρ)

  divide : ∀ {Ψ} Ψl {Ψr} 
         → Ψ ⊩ (Ψl ++ Ψr) 
         → Σ \ Ψl' → Σ \ Ψr' → (Ψ == (Ψl' ++ Ψr')) × Ψr' ⊩ Ψr
  divide [] ρ = [] , (_ , (id , ρ))
  divide (x :: Ψl) (Cons Ψ1 x₁ .x id ρ) with divide Ψl ρ 
  ... | (Ψl' , Ψr' , eq , ρ') = (Ψ1 ++ Ψl') , (Ψr' , (append-assoc Ψ1 Ψl' Ψr' ∘ ap (append Ψ1) eq , ρ'))

  compose'' : ∀ {Ψ Ψ' Ψ''} 
           → Ψ ⊩ Ψ'
           → Ψ' ⊩ Ψ''
           → Ψ ⊩ Ψ''
  compose'' ρ Nil = Nil
  compose'' {Ψ} {._} {.y :: Ψ''} ρ (Cons Ψ1 x {Ψ2} y id ρ') with divide Ψ1 ρ 
  compose'' {._} {._} {.y :: Ψ''} ρ (Cons Ψ1 x y id ρ') | Ψl' , ._ , id , Cons Ψrskip z .x id ρr = 
    Cons (Ψl' ++ Ψrskip) z y (append-assoc Ψl' Ψrskip _) (compose'' (Cons [] z x id ρr) ρ')

  compose' : ∀ {Ψ Ψ' Ψ'' x y x' y'} 
           → (x :: (Ψ ++ [ y ])) ⊩ Ψ'
           → (x' :: (Ψ' ++ [ y' ])) ⊩ Ψ''
           → (x :: (Ψ ++ [ y ])) ⊩ Ψ''
  compose' {Ψ} {Ψ'} {Ψ''} {x} {y} {x'} {y'} ρ ρ' =
    compose'' {Ψ = x :: (Ψ ++ [ y ])} {Ψ' = x' :: (Ψ' ++ [ y' ])} {Ψ'' = Ψ''} (extend {Ψ}{Ψ'}{x}{y}{x'}{y'} ρ) ρ'

  flip : ∀ {Ψ Ψ'} 
           → Ψ ⊩ Ψ'
           → rev Ψ ⊩ rev Ψ'
  flip Nil = Nil
  flip (Cons Ψ1 x {Ψ2} y s ρ) = ConsR (rev Ψ2) x {rev Ψ1} y ((! (append-assoc (rev Ψ2) [ x ] (rev Ψ1)) ∘ rev-append Ψ1 (x :: Ψ2)) ∘ ap rev s) (flip ρ)

  first : ∀ {A} {xs : List A} {x} → Σ \ y → y ∈ xs ++ [ x ]
  first {xs = []} = _ , i0
  first {xs = x :: xs} = _ , i0

  -- put an iS at the tail
  shiftright : ∀ {A} {xs : List A} {x0 y} → y ∈ xs → Σ \ y' → y' ∈ (xs ++ [ x0 ])
  shiftright {xs = []} ()
  shiftright {xs = x :: []} {x0} i0 = x0 , iS i0
  shiftright {xs = x :: []} (iS ())
  shiftright {xs = x :: x' :: xs} i0 = x' , iS i0
  shiftright {xs = x :: x' :: xs} (iS i) with shiftright {xs = x' :: xs} i
  ...                             | y' , i' = y' , iS i'

  1- : ∀ { Ψ : List String } {x} → x ∈ Ψ → Σ \ y → y ∈ rev Ψ
  1- {x :: Ψ} i0 = first {xs = rev Ψ}
  1- (iS i) with 1- i 
  ...          | y , i' = shiftright i'

  -- length(xs1)
  index : ∀ {A} {xs1 : List A} {x xs2} → x ∈ (xs1 ++ (x :: xs2)) 
  index {xs1 = []} = i0
  index {xs1 = _ :: xs1} = iS (index {xs1 = xs1})

  splitat : ∀ {A} {xs : List A} {x} → x ∈ xs → Σ \ xs1 → Σ \ xs2 → xs == xs1 ++ (x :: xs2)
  splitat i0 = [] , _ , id
  splitat (iS i) with splitat i 
  splitat (iS i) | xs1 , xs2 , id = _ :: xs1 , xs2 , id

  splitfirst : ∀ {A} {xs : List A} {x} → Σ \ ys → (xs ++ [ x ]) == (fst (first {xs = xs} {x})) :: ys
  splitfirst {xs = []} = _ , id
  splitfirst {xs = x :: xs} = _ , id

  reflect : ∀ {Ψ Ψ'} 
           → Ψ ⊩ Ψ'
           → rev Ψ ⊩ rev Ψ'
  reflect Nil = Nil
  reflect {Ψ' = .y :: Ψ'} (Cons Ψ1 x {Ψ2} y id ρ) with splitat (snd (1- (index {xs1 = Ψ1} {x} {Ψ2}))) | splitfirst {xs = rev Ψ'} {y}
  ... | (Ψ1new , Ψ2new , eqnew) | Ψ'new , eq' = 
      coe (ap2 _⊩_ (! eqnew) (! eq')) 
          (Cons Ψ1new _ {Ψ2new} _ id {!reflect ρ!})

  opv-invol : ∀ {v} → (v opv) opv == v
  opv-invol {+} = id
  opv-invol { - } = id

  opv-flip : ∀ {v} → ⊤ (v opv) == ⊥ v
  opv-flip {+} = id
  opv-flip { - } = id

  opv-flip' : ∀ {v} → ⊥ (v opv) == ⊤ v
  opv-flip' {+} = id
  opv-flip' { - } = id

{-
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
                          (flip ρ))
               ρ')))
  compose {Ψ , .((v opv) opv)} {Ψ' , .(v opv)} {Ψ'' , v} (con ρ) (con ρ') = 
    transport (λ h → (Ψ , h) ⊢ (Ψ'' , v)) (! (opv-invol {v})) 
              (co (compose' {Ψ = Ψ}
                     (transport (λ h → h ⊩ _)
                      (ap2 _::_ (opv-flip {v}) (ap2 _++_ (rev-rev Ψ) (ap [_] (opv-flip' {v}))) ∘
                       ap (λ h → h ++ [ ⊥ (v opv) ]) (rev-append (rev Ψ) [ ⊤ (v opv) ]))
                      (flip ρ))
                     ρ'))
-}
  
  _op : Ctx → Ctx
  (Ψ , v) op = (rev Ψ , v opv)

  op-invol : ∀ {Ψ} → (Ψ op) op == Ψ
  op-invol {Ψ , v} = ap2 _,_ (rev-rev Ψ) (opv-invol {v})

{-
  r : ∀ {Ψ} → Ψ ⊢ Ψ op
  r {Ψ , + } = con (ident' _) 
  r {Ψ , - } = con (ident' _) 
-}

  -- r-invol : ∀ {Ψ} → (compose (r {Ψ}) (r {Ψ op})) == transport (λ x → Ψ ⊢ x) (! (op-invol {Ψ})) (ident Ψ)
  -- r-invol = {!!}

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

  -- r1+ : ("x" :: [] , +) ⊢ ("x" :: [] , -)
  -- r1+ = r {"x" :: [] , + }

  -- r1- : ("x" :: [] , -) ⊢ ("x" :: [] , +)
  -- r1- = r {"x" :: [] , - }

  -- rinvol-11 : compose r1+ r1- == ident ([ "x" ] , +)
  -- rinvol-11 = id

  -- rinvol-12 : compose r1- r1+ == ident ([ "x" ] , -)
  -- rinvol-12 = id

  -- test : ([] , +) ⊢ ("x" :: [] , -)
  -- test = (compose 0/x+1 r1+)

  backwards : ("x" :: "y" :: [] , +) ⊢ ("y" :: "x" :: [] , -)
  backwards = con {!!}

  ----------------------------------------------------------------------

  -- r2+ = r {"x" :: "y" :: [] , + }
  -- r2- = r {"y" :: "x" :: [] , - }



