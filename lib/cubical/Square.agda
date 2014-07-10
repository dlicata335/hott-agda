
{-# OPTIONS --type-in-type --without-K #-}

open import lib.BasicTypes
open import lib.cubical.PathOver

module lib.cubical.Square where

  data Square {A : Type} {a00 : A} : 
              {a01 a10 a11 : A} → a00 == a01 -> a00 == a10 -> a01 == a11 -> a10 == a11 -> Type where 
    id : Square id id id id

  hrefl-Square : {A : Type} {a00 a01 : A} {p : a00 == a01} → Square p id id p
  hrefl-Square {p = id} = id

  vrefl-Square : {A : Type} {a00 a01 : A} {p : a00 == a01} → Square id p p id
  vrefl-Square {p = id} = id

  natural : {Γ Δ : Type} → ∀ {θ1 θ2 θ1' θ2'} (δ : (θ : Γ) → θ1 θ == θ2 θ) (δ' : θ1' == θ2') → Square {Δ} (ap θ1 δ') (δ θ1') (δ θ2') (ap θ2 δ')
  natural δ id = vrefl-Square

{-
  transport-PathOver-by-hand : {Δ : Type} (A : Δ → Type) {θ11 θ12 θ21 θ22 : Δ} {δ1- : θ11 == θ12} {δ2- : θ21 == θ22} {δ-1 : θ11 == θ21} {δ-2 : θ12 == θ22}
                             → Square δ1- δ-1 δ-2 δ2-
                             → ∀ {M11 M12 M21 M22}
                             → PathOver A δ1- M11 M12
                             → PathOver A δ2- M21 M22 
                             → PathOver A δ-1 M11 M21
                             → PathOver A δ-2 M12 M22
  transport-PathOver-by-hand A id p q r = {!p!} -- need path induction for PathOver A id M N

  transport-PathOver : {Γ Δ : Type} (A : Δ → Type) → {θ1 θ2 : Γ → Δ} (δ : (θ : Γ) → θ1 θ == θ2 θ) (M1 : (θ : _) → A (θ1 θ)) (M2 : (θ : _) → A (θ2 θ))
                       {θ1' θ2' : _} (δ' : θ1' == θ2')
                     → transport (\ θ → PathOver A (δ θ) (M1 θ) (M2 θ)) δ' == 
                       transport-PathOver-by-hand A (natural δ δ') (over-o-ap A (apdo M1 δ')) (over-o-ap A (apdo M2 δ'))
  transport-PathOver A δ M1 M2 id = {! λ≃ coh !} where
    coh : {θ1 : _} {θ2 : _} {δ : θ1 == θ2} {M1 : _} {M2 : _} → (x : PathOver A δ M1 M2) →
      x ==
      (transport (λ x₁ → x₁) (changeover= A (! (! (∘-unit-l δ)))) (id ∘o x ∘o id))
    coh id = id
-}


  data SquareOver {A : Type} (B : A → Type) {a00 : A} {b00 : B a00} : 
              {a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
              (f   : Square p0- p-0 p-1 p1-)
              {b01 : B a01} {b10 : B a10} {b11 : B a11}  
              (q0- : PathOver B p0- b00 b01)
              (q-0 : PathOver B p-0 b00 b10)
              (q-1 : PathOver B p-1 b01 b11)
              (q1- : PathOver B p1- b10 b11) → Type where
    id : SquareOver B id id id id id

  square-to-disc : {A : Type}
              {a00 a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
              (f   : Square p0- p-0 p-1 p1-)
              → p-1 ∘ p0- == p1- ∘ p-0
  square-to-disc id = id

  disc-to-square : {A : Type}
              {a00 a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
              → p-1 ∘ p0- == p1- ∘ p-0
              → Square p0- p-0 p-1 p1-
  disc-to-square {p0- = id} {p-0 = id} {p-1 = id} {p1- = .id} id = id

  square-disc-square : {A : Type}
              {a00 a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
              (f   : Square p0- p-0 p-1 p1-)
              → disc-to-square (square-to-disc f) == f
  square-disc-square id = id

  disc-square-disc : {A : Type}
              {a00 a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
              (f   : p-1 ∘ p0- == p1- ∘ p-0)
              → square-to-disc (disc-to-square { p0- = p0- }{ p-0 = p-0 } f) == f
  disc-square-disc {p0- = id} {p-0 = id} {p-1 = id} {p1- = .id} id = id

  square-disc-eqv : {A : Type}
              {a00 a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
              → Equiv (Square p0- p-0 p-1 p1-) (p-1 ∘ p0- == p1- ∘ p-0) 
  square-disc-eqv = (improve (hequiv square-to-disc disc-to-square square-disc-square disc-square-disc))


  square-∘-topright-right' : {A : Type}
              {a00 a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
              (f   : Square p0- p-0 p-1 p1-)
              -> Square p0- id p-1 (p1- ∘ p-0)
  square-∘-topright-right' id = id

  square-∘-topright-right : {A : Type}
              {a00 a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
              (f   : Square p0- p-0 p-1 p1-)
              -> Square p0- id p-1 (p1- ∘ p-0)
  square-∘-topright-right id = id

  square-∘-topright-right-triangle : {A : Type} {a' : A} 
             → {a0 a1 : A}
             → {p : a0 == a1}
             → {q0 : a' == a0}
             → {q1 : a' == a1}
             → (s : Square q0 id p q1)
             → square-∘-topright-right s == s
  square-∘-topright-right-triangle {q0 = id} {id} s = elim-along-equiv
                                                         (λ (s₁ : Square id id _ id) → square-∘-topright-right s₁ == s₁)
                                                         (!equiv square-disc-eqv) (λ x → lemma x) s where
     lemma : ∀ {A} {a' : A} {p : a' == a'} (x : Id p id) →
             Id (square-∘-topright-right (disc-to-square  {_}{_}{_}{_}{_} {id}{id}{p}{id} x)) (disc-to-square {_}{_}{_}{_}{_} {id}{id}{p}{id}  x)
     lemma id = id

  in-PathOver-=' : {A : Type} 
              {a00 a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
             → Square p0- p-0 p-1 p1-
             → PathOver (\ x -> a00 == x) p-1 p0- (p1- ∘ p-0)
  in-PathOver-=' id = id

  -- should be an equivalence
  in-PathOver-= : {A : Type} {a' : A} 
             → {a0 a1 : A}
             → {p : a0 == a1}
             → {q0 : a' == a0}
             → {q1 : a' == a1}
             → Square q0 id p q1
             → PathOver (\ x -> a' == x) p q0 q1 
  in-PathOver-= s = in-PathOver-=' s

  out-PathOver-= : {A : Type} {a' : A} 
             → {a0 a1 : A}
             → {p : a0 == a1}
             → {q0 : a' == a0}
             → {q1 : a' == a1}
             → PathOver (\ x -> a' == x) p q0 q1 
             → Square q0 id p q1
  out-PathOver-= {q0} id = hrefl-Square

  PathOver-=-inout : {A : Type} {a' : A} 
             → {a0 a1 : A}
             → {p : a0 == a1}
             → {q0 : a' == a0}
             → {q1 : a' == a1}
             → (p : PathOver (\ x -> a' == x) p q0 q1 )
             → in-PathOver-= (out-PathOver-= p) == p
  PathOver-=-inout {q0 = id} id = id

  PathOver-=-outin' : {A : Type} 
              {a00 a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
             → (s : Square p0- p-0 p-1 p1-)
             → out-PathOver-= (in-PathOver-=' s) == square-∘-topright-right s
  PathOver-=-outin' id = id

  PathOver-=-outin : {A : Type} {a' : A} 
             → {a0 a1 : A}
             → {p : a0 == a1}
             → {q0 : a' == a0}
             → {q1 : a' == a1}
             → (s : Square q0 id p q1)
             → out-PathOver-= (in-PathOver-= s) == s
  PathOver-=-outin s = square-∘-topright-right-triangle s ∘ PathOver-=-outin' s

  PathOver-=-eqv : {A : Type} {a' : A} 
             → {a0 a1 : A}
             → {p : a0 == a1}
             → {q0 : a' == a0}
             → {q1 : a' == a1} 
             → Equiv (PathOver (\ x -> a' == x) p q0 q1) (Square q0 id p q1)
  PathOver-=-eqv = improve (hequiv out-PathOver-= in-PathOver-= PathOver-=-inout PathOver-=-outin)

  extend-triangle : {A : Type} {a00 a01 a11 : A}
              {p0- : a00 == a01}
              {p-1 : a01 == a11}
              {p1- : a00 == a11}
              (f   : Square p0- id p-1 p1-)
              → {a00' : A} (p : a00' == a00) 
              → Square (p0- ∘ p) id p-1 (p1- ∘ p)
  extend-triangle f id = f

  ∘-square-vertical : {A : Type}
    {a000 a100 a110 a001 a101 a111 : A}
    {p-00 : a000 == a100} 
    {p1-0 : a100 == a110} 
    {p-01 : a001 == a101} 
    {p1-1 : a101 == a111} 
    {p00- : a000 == a001}  
    {p10- : a100 == a101}  
    {p11- : a110 == a111}  
    → (Square p-00 p00- p10- p-01)
    → (Square p1-0 p10- p11- p1-1)
    → Square (p1-0 ∘ p-00) p00- p11- (p1-1 ∘ p-01)
  ∘-square-vertical id s = s

  square-symmetry : {A : Type}
              {a00 a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
              (f   : Square p0- p-0 p-1 p1-)
              → Square p-0 p0- p1- p-1
  square-symmetry id = id

  connection : ∀ {A} {a b : A} {p : a == b} → Square id id p p 
  connection {p = id} = id

  connection2 : {A : Type} {a1 a2 a3 : A} {p : a1 == a2} {q : a2 == a3} → Square p p q q
  connection2 {p = id} {q = id} = id

  ∘-square : {A : Type} {a0 a1 a2 : A} {p : a0 == a1} {q : a1 == a2} 
           → Square p id q (q ∘ p)
  ∘-square {p = id} = connection

