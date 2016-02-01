
-- FIXME: does this make sense?

open import functorlogic.Lib
open import functorlogic.ModesProduct1

module functorlogic.NDHypOnly-Derivable where

  data Tp : Mode → Set where
    P    : ∀ {m} → Tp m
    Q    : ∀ {m} → Tp m
    F    : ∀ {p q} (α : p ≤ q) → Tp p → Tp q
    ·    : Tp ⊤m
    _,_  : ∀ {p q} → Tp p → Tp q → Tp (p ×m q)

  data Ctx : (p : Mode) → Set where
    ·    : Ctx ⊤m
    _,_  : ∀ {p q} → Ctx p → Ctx q → Ctx (p ×m q)
    ▸    : ∀ {p} → Tp p → Ctx p
    _[_] : ∀ {p q} → Ctx p → (α : p ≤ q) → Ctx q

  data Ctx' : (q : Mode) (p : Mode) → Set where
    hole : ∀ {p} → Ctx' p p
    const : ∀ {p q} → Ctx q → Ctx' p q
    _,1_  : ∀ {p q r} → Ctx' r p → Ctx q → Ctx' r (p ×m q)
    _,2_  : ∀ {p q r} → Ctx p → Ctx' r q → Ctx' r (p ×m q)
    _[_] : ∀ {p q r} → Ctx' r p → (α : p ≤ q) → Ctx' r q

  fill : ∀ { p q} → Ctx' q p → Ctx q → Ctx p
  fill hole Δ = Δ
  fill (const Γ) Δ = Γ
  fill (Γ' ,1 Γ'') Δ = fill Γ' Δ , Γ''
  fill (Γ' ,2 Γ'') Δ = Γ' , fill Γ'' Δ
  fill (Γ' [ α ]) Δ = fill Γ' Δ [ α ]

  data _⇒c_ : ∀ {p} → Ctx p → Ctx p → Set where
    idc  : ∀ {p} {Γ : Ctx p} → Γ ⇒c Γ
    _·c_ : ∀ {p} {Γ1 Γ2 Γ3 : Ctx p} → Γ1 ⇒c Γ2 → Γ2 ⇒c Γ3 → Γ1 ⇒c Γ3
    [·] : ∀ {p q r} {Γ : Ctx r} {α : r ≤ q} {β : q ≤ p}
          → (Γ [ α ]) [ β ] ⇒c Γ [ α ·1 β ]
    ![·] : ∀ {p q r} {Γ : Ctx r} {α : r ≤ q} {β : q ≤ p}
          → Γ [ α ·1 β ] ⇒c (Γ [ α ]) [ β ]
    [1] : ∀ {p} {Γ : Ctx p} → Γ [ 1m ] ⇒c Γ
    ![1] : ∀ {p} {Γ : Ctx p} → Γ ⇒c Γ [ 1m ]
    [fst] : ∀ {p q} {Γ : Ctx p} {Δ : Ctx q} → (Γ , Δ) [ fstm ] ⇒c Γ
    ![fst] : ∀ {p q} {Γ : Ctx p} {Δ : Ctx q} → Γ ⇒c (Γ , Δ) [ fstm ]
    [snd] : ∀ {p q} {Γ : Ctx p} {Δ : Ctx q} → (Γ , Δ) [ sndm ] ⇒c Δ
    ![snd] : ∀ {p q} {Γ : Ctx p} {Δ : Ctx q} → Δ ⇒c (Γ , Δ) [ sndm ]
    [<>] : ∀ {p} {Γ : Ctx p} → Γ [ <>m ] ⇒c ·
    ![<>] : ∀ {p} {Γ : Ctx p} → · ⇒c Γ [ <>m ] 
    [,] : ∀ {p q r} {α : p ≤ q} {β : p ≤ r}{Γ : Ctx p} → Γ [ (α ,m β) ] ⇒c (Γ [ α ] , Γ [ β ]) 
    ![,] : ∀ {p q r} {α : p ≤ q} {β : p ≤ r}{Γ : Ctx p} → (Γ [ α ] , Γ [ β ]) ⇒c Γ [ (α ,m β) ] 
    nt : ∀ {p q} {Γ Δ : Ctx q} {α β : q ≤ p} (e : α ⇒ β) 
       → Γ ⇒c Δ
       → Γ [ α ] ⇒c Δ [ β ]
    _,c_ : ∀ {p q} {Γ1 Δ1 : Ctx p} {Γ2 Δ2 : Ctx q} 
           → Γ1 ⇒c Δ1
           → Γ2 ⇒c Δ2 
           → (Γ1 , Γ2) ⇒c (Δ1 , Δ2)

  fillcong : ∀ {p q} (Γ' : Ctx' p q) {Δ Δ'} → Δ ⇒c Δ' → fill Γ' Δ ⇒c fill Γ' Δ'
  fillcong hole ρ = ρ
  fillcong (const Γ) _ = idc
  fillcong (Γ' ,1 Γ) ρ = fillcong Γ' ρ ,c idc
  fillcong (Γ ,2 Γ') ρ = idc ,c fillcong Γ' ρ
  fillcong (Γ' [ α ]) ρ = nt 1⇒ (fillcong Γ' ρ)

  mutual
    data _⊢_ : {p : Mode} → Ctx p → Tp p -> Set where
      var : ∀ {p} {Γ : Ctx p} {A : Tp p} → Γ ⇒c (▸ A) → Γ ⊢ A
      FE  : ∀ {p q r} {Γ : Ctx p} {Δ : Ctx q} {α : r ≤ q} {A : Tp r} {C : Tp p}
         → (Γ' : Ctx' q p) 
         → Γ ⇒c fill Γ' Δ
         → Δ ⊢ F α A 
         → (fill Γ' ((▸ A) [ α ])) ⊢ C
         → Γ ⊢ C
      FI : ∀ {p q} → {Γ : Ctx p} {Δ : Ctx q} {A : Tp q} {α : q ≤ p}
         → Γ ⇒c Δ [ α ] 
         → Δ ⊢ A
         → Γ ⊢ F α A
      pair : ∀ {p q} {Γ : Ctx (p ×m q)} {Γ1 Γ2} {A1 : Tp p} {A2 : Tp q}
          → Γ ⇒c (Γ1 , Γ2)
          → Γ1 ⊢ A1
          → Γ2 ⊢ A2 
          → Γ ⊢ (A1 , A2)
      letpair : ∀ {p q1 q2} {Γ : Ctx p} {Δ : Ctx (q1 ×m q2)} {A : Tp _} {B : Tp _} {C : Tp p}
         → (Γ' : Ctx' (q1 ×m q2) p) 
         → Γ ⇒c fill Γ' Δ
         → Δ ⊢ (A , B) 
         → (fill Γ' (▸ A , ▸ B)) ⊢ C
         → Γ ⊢ C
      -- should be admissible for some mode theories, but not all
      subst : ∀ {p} {C} {Γ Γ' : Ctx p} → Γ' ⊢ C → Γ ⊢s Γ' → Γ ⊢ C

    data _⊢s_ : {p : _} (Γ : Ctx p) → Ctx p → Set where
      ids : ∀ {p} {Γ : Ctx p} → Γ ⊢s Γ
      _·s_ : ∀ {Γ1 Γ2 Γ3 : Ctx ⊤m} → Γ1 ⊢s Γ2 → Γ2 ⊢s Γ3 → Γ1 ⊢s Γ3 
      subst▸ : ∀  {p} {Γ : Ctx p} {A} → Γ ⊢ A → Γ ⊢s (▸ A)
      subst, : ∀ {p q} {Γ1 Δ1 : Ctx p} {Γ2 Δ2 : Ctx q} 
             → Γ1 ⊢s Δ1
             → Γ2 ⊢s Δ2
             → (Γ1 , Γ2) ⊢s (Δ1 , Δ2)
      subst[] : {p q : Mode} {Γ : Ctx p} → {Γ1 Γ2 : Ctx q} {α : q ≤ p}
              → Γ1 ⊢s Γ2 → Γ1 [ α ] ⊢s Γ2 [ α ]
      substnt : ∀ {p} {Γ Δ : Ctx p}
              → Γ ⇒c Δ 
              → Γ ⊢s Δ

  _∘'_ : ∀ { p q r} → Ctx' q p → Ctx' r q → Ctx' r p
  hole ∘' Δ = Δ
  (const Γ) ∘' Δ' = const Γ
  (Γ' ,1 x) ∘' Δ' = (Γ' ∘' Δ') ,1 x
  (x ,2 Γ') ∘' Δ' = x ,2 (Γ' ∘' Δ')
  (Γ' [ α ]) ∘' Δ' = (Γ' ∘' Δ') [ α ]

  fill∘ : ∀ { p q r} {A} → (Γ2' : Ctx' q p) (Γ1' : Ctx' r q) → fill (Γ2' ∘' Γ1') A == fill Γ2' (fill Γ1' A)
  fill∘ hole Γ1' = id
  fill∘ (const x) Γ1' = id
  fill∘ (Γ2' ,1 x) Γ1' = ap2 _,_ (fill∘ Γ2' Γ1') id
  fill∘ (x ,2 Γ2') Γ1' = ap2 _,_ id (fill∘ Γ2' Γ1')
  fill∘ (Γ2' [ α ]) Γ1' = ap (λ x → x [ α ]) (fill∘ Γ2' Γ1')

  eq : ∀ {p} {Γ Δ : Ctx p} → Γ == Δ -> Γ ⇒c Δ
  eq id = idc

  yank : ∀ {p1 p2 q} {α : p1 ≤ q} {β : p2 ≤ q} {Γ Δ} 
       → (Γ [ α ] , Δ [ β ]) ⇒c ((Γ , Δ) [ (fstm ·1 α) ,m (sndm ·1 β) ])
  yank = ((nt 1⇒ ![fst] ·c [·]) ,c (nt 1⇒ ![snd] ·c [·])) ·c ![,]

  unyank : ∀ {p1 p2 q} {α : p1 ≤ q} {β : p2 ≤ q} {Γ Δ} 
       → ((Γ , Δ) [ (fstm ·1 α) ,m (sndm ·1 β) ]) ⇒c (Γ [ α ] , Δ [ β ])
  unyank =  [,] ·c ((![·] ·c nt 1⇒ [fst]) ,c (![·] ·c nt 1⇒ [snd])) 

  F∘1 : ∀ {p q r : Mode} {A : Tp r} {α : r ≤ q} {β : q ≤ p}
      → ▸ (F β (F α A)) ⊢ F (α ·1 β) A
  F∘1 = FE hole idc (var idc) (FE (hole [ _ ]) idc (var idc) (FI [·] (var idc)))

  F∘2 : ∀ {p q r : Mode} {A : Tp r} {α : r ≤ q} {β : q ≤ p}
      → ▸ (F (α ·1 β) A) ⊢ (F β (F α A))
  F∘2 = FE hole idc (var idc) (FI ![·] (FI idc (var idc)))

  Fnt : ∀ {p q : Mode} {A : Tp q} {α β : q ≤ p} (e : α ⇒ β)
      → ▸ (F α A) ⊢ F β A
  Fnt e = FE hole idc (var idc) (FI (nt e idc) (var idc))

  module Bifunctor {p : Mode} (⊗m : (p ×m p) ≤ p) where

    _,,_ : Ctx p → Ctx p → Ctx p
    _,,_ Γ Δ = (Γ , Δ) [ ⊗m ]
  
    _⊗_ : Tp p → Tp p → Tp p
    _⊗_ A B = F ⊗m (A , B)

    pair⊗ : {A B : Tp p} {Γ Γ1 Γ2 : Ctx p}
         → Γ ⇒c (Γ1 ,, Γ2)
         → Γ1 ⊢ A
         → Γ2 ⊢ B
         → Γ ⊢ (A ⊗ B)
    pair⊗ {Γ = Γ} {Γ1} {Γ2} ρ D1 D2 = FI ρ (pair idc D1 D2)

    letpair⊗ : ∀ {q} {Γ : Ctx q} {Δ : Ctx p} {A B : Tp p} {C : Tp q}
         → (Γ' : Ctx' p q) 
         → Γ ⇒c fill Γ' Δ
         → Δ ⊢ (A ⊗ B) 
         → (fill Γ' (▸ A ,, ▸ B)) ⊢ C
         → Γ ⊢ C
    letpair⊗ Γ' ρ D E = FE Γ' ρ D (letpair (Γ' ∘' (hole [ ⊗m ])) (eq (! (fill∘ Γ' (hole [ ⊗m ])))) (var idc) (transport (λ Γ → Γ ⊢ _) (! (fill∘ Γ' (hole [ ⊗m ]))) E))

  module Weakening {q p} (α : p ≤ q) 
                         (1q : ⊤m ≤ q) 
                         (⊗m : (q ×m q) ≤ q)
                         (lunit : ∀ {p} {β : p ≤ q} → ((β ,m (<>m ·1 1q)) ·1 ⊗m) ⇒ β)
                         (runit : ∀ {p} {β : p ≤ q} → (((<>m ·1 1q) ,m β) ·1 ⊗m) ⇒ β)
                         (wkn : α ⇒ (<>m ·1 1q)) where 

    open Bifunctor ⊗m

    1t = F 1q ·
  
    fst⊗ : {A B : Tp p} → (▸ ((F α A) ⊗ (F α B))) ⊢ F α A
    fst⊗ = letpair⊗ hole idc (var idc) (FE ((hole ,1 _) [ _ ]) idc (var idc) (FE ((_ ,2 hole) [ _ ]) idc (var idc) 
                     (FI (nt 1⇒ yank ·c ([·] ·c (nt (((1⇒ ,cong ((1⇒ ·1cong wkn) ·2 ((1⇒' (⊤mη {α = sndm ·1 <>m}) ·1cong 1⇒ {_} {_} {1q})))) ·1cong 1⇒) ·2 lunit) idc ·c (![·] ·c nt 1⇒ [fst])))) (var idc))))

    snd⊗ : {A B : Tp p} → (▸ ((F α A) ⊗ (F α B))) ⊢ F α B
    snd⊗ = letpair⊗ hole idc (var idc) (FE ((hole ,1 _) [ _ ]) idc (var idc) (FE ((_ ,2 hole) [ _ ]) idc (var idc) 
                     (FI (nt 1⇒ yank ·c ([·] ·c (nt (((((1⇒ ·1cong wkn) ·2 (1⇒' (⊤mη {α = fstm ·1 <>m}) ·1cong 1⇒ {_} {_} {1q})) ,cong 1⇒) ·1cong 1⇒) ·2 runit) idc ·c (![·] ·c nt 1⇒ [snd])))) (var idc))))

  module Contraction {q p} (α : p ≤ q) (⊗m : (q ×m q) ≤ q) (contract : α ⇒ ((α ,m α) ·1 ⊗m)) where

     open Bifunctor ⊗m

     contraction : {A : Tp p} → (▸ (F α A)) ⊢ (F α A ⊗ F α A)
     contraction = FE hole idc (var idc) (pair⊗ (nt contract idc ·c (![·] ·c nt 1⇒ [,]))
                                                 (FI idc (var idc))
                                                 (FI idc (var idc)))

  module Exchange {q p} (α : p ≤ q) (⊗m : (q ×m q) ≤ q) (ex : (((fstm ·1 α) ,m (sndm ·1 α)) ·1 ⊗m) ⇒ (((sndm ·1 α) ,m (fstm ·1 α)) ·1 ⊗m)) where

     open Bifunctor ⊗m

     exchange : {A B : Tp p} → (▸ ((F α A) ⊗ (F α B))) ⊢ (F α B ⊗ F α A)
     exchange = letpair⊗ hole idc (var idc) 
                  (FE ((hole ,1 _) [ _ ]) idc (var idc)
                  (FE ((_ ,2 hole) [ _ ]) idc (var idc) 
                      (pair⊗ ((nt 1⇒ yank ·c [·]) ·c (nt ex idc ·c (![·] ·c nt 1⇒ ([,] ·c ((![·] ·c nt 1⇒ [snd]) ,c (![·] ·c nt 1⇒ [fst]))))))
                             (FI idc (var idc))
                             (FI idc (var idc)))))

  module Assoc {q p}
               (α : p ≤ q) (⊗m : (q ×m q) ≤ q)
               (assoc1 : (((fstm ·1 (((fstm ·1 α) ,m (sndm ·1 α)) ·1 ⊗m)) ,m (sndm ·1 α)) ·1 ⊗m)
                         ⇒ (((fstm ·1 (fstm ·1 α)) ,m (((fstm ·1 (sndm ·1 α)) ,m (sndm ·1 α)) ·1 ⊗m)) ·1 ⊗m)) where
    open Bifunctor ⊗m

    assoc : {A B C : Tp p} → (▸ (((F α A) ⊗ (F α B)) ⊗ (F α C))) ⊢ (F α A ⊗ (F α B ⊗ F α C))
    assoc = letpair⊗ hole idc (var idc) 
               (letpair⊗ ((hole ,1 _) [ _ ]) idc (var idc) 
                         (FE ((_ ,2 hole) [ _ ]) idc (var idc) 
                         (FE ((((hole ,1 _) [ _ ]) ,1 _) [ _ ]) idc (var idc)
                             (FE ((((_ ,2 hole) [ _ ]) ,1 _) [ _ ]) idc (var idc) 
                                 (pair⊗ 
                                   (nt 1⇒ (((nt 1⇒ yank ·c [·]) ,c idc)) ·c 
                                    (nt 1⇒ yank ·c 
                                      ([·] ·c (nt assoc1 idc ·c 
                                                (![·] ·c (nt 1⇒ ([,] ·c ((![·] ·c (nt 1⇒ [fst] ·c (![·] ·c nt 1⇒ [fst]))) ,c 
                                                                          (![·] ·c nt 1⇒ ([,] ·c 
                                                                           ((![·] ·c (nt 1⇒ [fst] ·c (![·] ·c nt 1⇒ [snd]))) ,c 
                                                                            (![·] ·c nt 1⇒ [snd])))))))))))) 
                                   (FI idc (var idc)) (pair⊗ idc (FI idc (var idc)) (FI idc (var idc))))))))

  module Pres (p q : Mode) (⊗p : (p ×m p) ≤ p) (⊗q : (q ×m q) ≤ q) (α : p ≤ q) 
              (pres : (⊗p ·1 α) ⇒ (((fstm ·1 α) ,m (sndm ·1 α)) ·1 ⊗q)) where
    module P = Bifunctor ⊗p
    module Q = Bifunctor ⊗q

    Fpres : ∀ {A B} → ▸ (F α (A P.⊗ B)) ⊢ ((F α A) Q.⊗ (F α B))
    Fpres = FE hole idc (var idc) 
               (P.letpair⊗ (hole [ _ ]) idc (var idc)
                  (Q.pair⊗ ([·] ·c (nt pres idc ·c (![·] ·c nt 1⇒ unyank)))
                           (FI idc (var idc))
                           (FI idc (var idc))))
    


