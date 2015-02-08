
{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Prods
open import lib.Functions
open import lib.AdjointEquiv
open import lib.Paths

open import lib.cubical.PathOver

module lib.cubical.Square where

  module Derivable where
     Square' : {A : Type} {a00 : A} {a01 a10 a11 : A} → a00 == a01 -> a00 == a10 -> a01 == a11 -> a10 == a11 -> Type 
     Square' p q r s = r ∘ p == s ∘ q
   
     idSquare' : {A : Type} {a00 : A} → Square' {a00 = a00} id id id id
     idSquare' = id
   
     Square'-induction : {A : Type} {a00 : A} 
                         (C : {a01 a10 a11 : A} → {p : a00 == a01} {q : a00 == a10} {r : a01 == a11} {s :  a10 == a11} -> Square' p q r s → Type)
                       → C {p = id} {q = id} {r = id} {s = id} (idSquare' {_}{a00})
                       → {a01 a10 a11 : A} → {p : a00 == a01} {q : a00 == a10} {r : a01 == a11} {s :  a10 == a11} 
                          (sq : Square' p q r s) → C {p = p} {q = q} {r = r} {s = s} sq
     Square'-induction C b {p = id} {q = id} {r = id} {.id} id = b
   
     Square'-induction-β : {A : Type} {a00 : A} 
                         (C : {a01 a10 a11 : A} → {p : a00 == a01} {q : a00 == a10} {r : a01 == a11} {s :  a10 == a11} -> Square' p q r s → Type)
                       → (b : C {p = id} {q = id} {r = id} {s = id} (idSquare' {_}{a00}))
                       → Square'-induction {a00 = a00} 
                                           (\ {a01} {a10} {a11}{p}{q}{r}{s} sq → C {a01}{a10}{a11}{p}{q}{r}{s} sq)
                                           b {a00} {a00} {a00} {p = id} {q = id} {r = id} {s = id} (idSquare' {A}{a00}) 
                          == b
     Square'-induction-β C b = id
                     

  data Square {A : Type} {a00 : A} : 
              {a01 a10 a11 : A} → a00 == a01 -> a00 == a10 -> a01 == a11 -> a10 == a11 -> Type where 
    id : Square id id id id

  hrefl-square : {A : Type} {a00 a01 : A} {p : a00 == a01} → Square p id id p
  hrefl-square {p = id} = id

  vrefl-square : {A : Type} {a00 a01 : A} {p : a00 == a01} → Square id p p id
  vrefl-square {p = id} = id

  natural : {Γ Δ : Type} → ∀ {θ1 θ2 θ1' θ2'} (δ : (θ : Γ) → θ1 θ == θ2 θ) (δ' : θ1' == θ2') → Square {Δ} (ap θ1 δ') (δ θ1') (δ θ2') (ap θ2 δ')
  natural δ id = vrefl-square

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
      (transport (λ x₁ → x₁) (changeover= A (! (! (·-unit-l δ)))) (id ∘o x ∘o id))
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

  square-to-disc' : {A : Type}
              {a00 a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
              (f   : Square p0- p-0 p-1 p1-)
              → p-1 ∘ p0- ∘ ! p-0 == p1-
  square-to-disc' id = id

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

  -- could define lots of these; this particular one came up
  square-to-disc-rearrange : {A : Type}
                {a00 a01 a10 a11 : A} 
                {p0- : a00 == a01}
                {p-0 : a00 == a10}
                {p-1 : a11 == a01}
                {p1- : a11 == a10}
                (f   : Square p0- p-0 (! p-1) (! p1-))
                → p-1 == p0- ∘ ! p-0 ∘ p1-
  square-to-disc-rearrange {p0- = p0- } {p-0 = id} {p-1 = id} {p1- = id} f = ∘-unit-l p0- ∘ ! (square-to-disc f)
  

  horiz-degen-square : {A : Type} {a a' : A} {p q : a == a'} (r : p == q)
                     → Square p id id q
  horiz-degen-square id = hrefl-square
  -- disc-to-square {p0- = p} {id} {id} {q}

  horiz-degen-square-to-path : {A : Type} {a a' : A} {p q : a == a'} 
                     → Square p id id q → p == q
  horiz-degen-square-to-path {p = p} s = square-to-disc s ∘ ! (∘-unit-l p)

  vertical-degen-square : {A : Type} {a a' : A} {p q : a == a'} (r : p == q)
                     → Square id p q id
  vertical-degen-square {p = id}{q = .id} id = id


  horiz-degen-square-induction : {A : Type} {a : A}
                               → (C : {a' : A} {p : a == a'} {q : a == a'} (s : Square p id id q) → Type)
                               → C id 
                               → {a' : A} {p q : a == a'} (s : Square p id id q) → C s
  horiz-degen-square-induction {A}{a} C b {a'}{p}{q} s = transport (λ s₁ → C s₁) (IsEquiv.α (snd square-disc-eqv) s) (coh (square-to-disc s)) where
    coh : ∀ {a'} {p : a == a'} {q : a == a'} → (d : id ∘ p == q) → C (disc-to-square {p0- = p}{id}{id}{q} d)
    coh {p = id} {.id} id = b

  horiz-degen-square-induction1 : {A : Type} {a a' : A} {p : a == a'}
                               → (C : {q : a == a'} (s : Square p id id q) → Type)
                               → C {p} (hrefl-square) 
                               → {q : a == a'} (s : Square p id id q) → C s
  horiz-degen-square-induction1 {A}{a}{.a} {id} C b {q} s = transport (λ s₁ → C s₁) (IsEquiv.α (snd square-disc-eqv) s) (coh (square-to-disc s)) where
     coh : ∀ {q : a == a} → (d : id == q) → C (disc-to-square {p0- = id}{id}{id}{q} d)
     coh id = b

  horiz-degen-square-induction1-β : {A : Type} {a a' : A} {p : a == a'}
                                  → (C : {q : a == a'} (s : Square p id id q) → Type)
                                  → (b : C {p} (hrefl-square))
                                  → horiz-degen-square-induction1 C b (hrefl-square) == b
  horiz-degen-square-induction1-β {p = id} C b = id

  horiz-degen-square-eqv : {A : Type} {a a' : A} {p q : a == a'} 
                         → Equiv (Square p id id q) (p == q)
  horiz-degen-square-eqv {p = id} = improve (hequiv horiz-degen-square-to-path horiz-degen-square
                                           (λ s →
                                                horiz-degen-square-induction
                                                (λ x → Path (horiz-degen-square (horiz-degen-square-to-path x)) x)
                                                id s) (λ y → path-induction (\ _ y → Path (horiz-degen-square-to-path (horiz-degen-square y)) y) id y))


  square-·-topright-right' : {A : Type}
              {a00 a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
              (f   : Square p0- p-0 p-1 p1-)
              -> Square p0- id p-1 (p1- ∘ p-0)
  square-·-topright-right' id = id

  square-·-topright-right : {A : Type}
              {a00 a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
              (f   : Square p0- p-0 p-1 p1-)
              -> Square p0- id p-1 (p1- ∘ p-0)
  square-·-topright-right id = id

  square-·-topright-right-triangle : {A : Type} {a' : A} 
             → {a0 a1 : A}
             → {p : a0 == a1}
             → {q0 : a' == a0}
             → {q1 : a' == a1}
             → (s : Square q0 id p q1)
             → square-·-topright-right s == s
  square-·-topright-right-triangle {q0 = id} {id} s = elim-along-equiv
                                                         (λ (s₁ : Square id id _ id) → square-·-topright-right s₁ == s₁)
                                                         (!equiv square-disc-eqv) (λ x → lemma x) s where
     lemma : ∀ {A} {a' : A} {p : a' == a'} (x : Id p id) →
             Id (square-·-topright-right (disc-to-square  {_}{_}{_}{_}{_} {id}{id}{p}{id} x)) (disc-to-square {_}{_}{_}{_}{_} {id}{id}{p}{id}  x)
     lemma id = id

  module PathOverPathFrom where
    in-PathOver-=' : {A : Type} 
                {a00 a01 a10 a11 : A} 
                {p0- : a00 == a01}
                {p-0 : a00 == a10}
                {p-1 : a01 == a11}
                {p1- : a10 == a11}
               → Square p0- p-0 p-1 p1-
               → PathOver (\ x -> a00 == x) p-1 p0- (p1- ∘ p-0)
    in-PathOver-=' id = id
  
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
    out-PathOver-= {q0} id = hrefl-square
  
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
               → out-PathOver-= (in-PathOver-=' s) == square-·-topright-right s
    PathOver-=-outin' id = id
  
    PathOver-=-outin : {A : Type} {a' : A} 
               → {a0 a1 : A}
               → {p : a0 == a1}
               → {q0 : a' == a0}
               → {q1 : a' == a1}
               → (s : Square q0 id p q1)
               → out-PathOver-= (in-PathOver-= s) == s
    PathOver-=-outin s = square-·-topright-right-triangle s ∘ PathOver-=-outin' s
  
    PathOver-=-eqv : {A : Type} {a' : A} 
               → {a0 a1 : A}
               → {p : a0 == a1}
               → {q0 : a' == a0}
               → {q1 : a' == a1} 
               → Equiv (PathOver (\ x -> a' == x) p q0 q1) (Square q0 id p q1)
    PathOver-=-eqv = improve (hequiv out-PathOver-= in-PathOver-= PathOver-=-inout PathOver-=-outin)

  module PathOver= where

    out-PathOver-= : {A B : Type} {f g : A → B}
                {a a' : A} {p : a == a'}
                {pa : f a == g a}
                {pa' : f a' == g a'}
               → PathOver (\ x -> f x == g x) p pa pa'
               → Square pa (ap f p) (ap g p) pa'
    out-PathOver-= id = hrefl-square

    in-PathOver-= : {A B : Type} {f g : A → B}
                {a a' : A} {p : a == a'}
                {pa : f a == g a}
                {pa' : f a' == g a'}
               → Square pa (ap f p) (ap g p) pa'
               → PathOver (\ x -> f x == g x) p pa pa'
    in-PathOver-= {f = f} {g} {p = id} {pa} s = horiz-degen-square-induction1
                                                  (λ {pa'} s₁ → PathOver (λ x → f x == g x) id pa pa') id s

    in-out : {A B : Type} {f g : A → B}
                {a a' : A} {p : a == a'}
                {pa : f a == g a}
                {pa' : f a' == g a'}
               → (s : Square pa (ap f p) (ap g p) pa')
               → out-PathOver-= (in-PathOver-= s) == s
    in-out {f = f}{g} {p = id} {pa} s = horiz-degen-square-induction1 (λ s₁ → out-PathOver-= (in-PathOver-= s₁) == s₁) (ap out-PathOver-=
                                                                                                                          (horiz-degen-square-induction1-β
                                                                                                                           (λ {pa'} s₁ → PathOver (λ x → f x == g x) id pa pa') id)) s

    out-in : {A B : Type} {f g : A → B}
                {a a' : A} {p : a == a'}
                {pa : f a == g a}
                {pa' : f a' == g a'}
               → (p : PathOver (\ x -> f x == g x) p pa pa')
               → in-PathOver-= (out-PathOver-= p) == p
    out-in {f = f} {g} {p = .id} {pa} id = horiz-degen-square-induction1-β (λ {pa'} s₁ → PathOver (λ x → f x == g x) id pa pa') id
      
    out-PathOver-=-eqv : {A B : Type} {f g : A → B}
                {a a' : A} {p : a == a'}
                {pa : f a == g a}
                {pa' : f a' == g a'}
               → Equiv (PathOver (\ x -> f x == g x) p pa pa')
                        (Square pa (ap f p) (ap g p) pa')
    out-PathOver-=-eqv = improve (hequiv out-PathOver-= in-PathOver-= out-in in-out) 

  module PathOver=D where

    postulate -- used in wedge connectivity
      in-PathOver-= : {A : Type} {B : A → Type} {f g : (x : A) → B x}
                {a a' : A} {p : a == a'}
                {pa : f a == g a}
                {pa' : f a' == g a'}
               → SquareOver B (vrefl-square {p = p}) (hom-to-over pa) (apdo f p) (apdo g p) (hom-to-over pa')
               → PathOver (\ x -> f x == g x) p pa pa'
      
  extend-triangle : {A : Type} {a00 a01 a11 : A}
              {p0- : a00 == a01}
              {p-1 : a01 == a11}
              {p1- : a00 == a11}
              (f   : Square p0- id p-1 p1-)
              → {a00' : A} (p : a00' == a00) 
              → Square (p0- ∘ p) id p-1 (p1- ∘ p)
  extend-triangle f id = f

  ·-square-vertical : {A : Type}
    {a b c d e f : A}
    {l : a == b} 
    {t : a == c} 
    {bt : b == d} 
    {r : c == d} 
    {l' : b == e}  
    {b' : e == f}  
    {r' : d == f}  
    → (Square l t bt r)
    → (Square l' bt b' r')
    → Square (l' ∘ l) t b' (r' ∘ r)
  ·-square-vertical id s = s
  
  _·-square-v_ = ·-square-vertical
  infixr 10 _·-square-v_

  -- FIXME: how do you get this from a Kan filling?
  ·-square-vertical/degen-bot : {A : Type}
    {a b c d : A}
    {l : a == b} 
    {t : a == c} 
    {bt : b == d} 
    {r : c == d} 
    {b' : b == d}  
    → (Square l t bt r)
    → (Square id bt b' id)
    → Square l t b' r
  ·-square-vertical/degen-bot id s = s

  ·-square-vertical/degen-top : {A : Type}
    {a b c d : A}
    {l : a == b} 
    {t : a == c} 
    {bt : a == c} 
    {r : c == d} 
    {b' : b == d}  
    → (Square id t bt id)
    → (Square l bt b' r)
    → Square l t b' r
  ·-square-vertical/degen-top s id = s

  ·-square-horiz : {A : Type}
    {a b c d e f : A}
    {l : a == b} 
    {t : a == c}
    {b : b == d}
    {r : c == d}
    {t' : c == e}
    {b' : d == f}
    {r' : e == f}
    → (Square l t b r)
    → (Square r t' b' r')
    → Square l (t' ∘ t) (b' ∘ b) r'
  ·-square-horiz id s = s

  _·-square-h_ = ·-square-horiz
  infixr 10 _·-square-h_

  !-square-h : {A : Type}
              {a00 a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
              (f   : Square p0- p-0 p-1 p1-)
              → Square p1- (! p-0) (! p-1) p0-
  !-square-h id = id

  !-square-v : {A : Type}
              {a00 a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
              (f   : Square p0- p-0 p-1 p1-)
              → Square (! p0-) (p-1) p-0 (! p1-)
  !-square-v id = id
  
  square-symmetry : {A : Type}
              {a00 a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
              (f   : Square p0- p-0 p-1 p1-)
              → Square p-0 p0- p1- p-1
  square-symmetry id = id

  diag-square : {A : Type}
              {a00 a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
              (f   : Square p0- p-0 p-1 p1-)
              → a00 == a11
  diag-square id = id

  connection : ∀ {A} {a b : A} {p : a == b} → Square id id p p 
  connection {p = id} = id

  connOver : {A : Type} {a a' : A} {p : a == a'} → PathOver (\ x -> a == x) p id p
  connOver = (PathOverPathFrom.in-PathOver-= connection)

  connection2 : {A : Type} {a1 a2 a3 : A} {p : a1 == a2} {q : a2 == a3} → Square p p q q
  connection2 {p = id} {q = id} = id

  inverses-square : {A : Type} {a00 a01 a10 : A} (p : a00 == a01) (q : a00 == a10) → Square p q (! p) (! q)
  inverses-square id id = id

  inverses-connection-coh : {A : Type} {a00 a01 : A} → (p : a00 == a01) → inverses-square p p == connection2
  inverses-connection-coh id = id
  
  ·-square : {A : Type} {a0 a1 a2 : A} {p : a0 == a1} {q : a1 == a2} 
           → Square p id q (q ∘ p)
  ·-square {p = id} = connection

  whisker-square : {A : Type} {a00 : A} 
                   {a01 a10 a11 : A} → {p p' : a00 == a01} -> {q q' : a00 == a10} -> {r r' : a01 == a11} -> {s s' : a10 == a11}
                   → p == p' → q == q' → r == r' -> s == s'
                   → Square p q r s → Square p' q' r' s'
  whisker-square id id id id s = s

  ap-square : {A B : Type} (g : A → B) → 
              {a00 a01 a10 a11 : A} 
              {l : a00 == a01}
              {t : a00 == a10}
              {b : a01 == a11}
              {r : a10 == a11}
              (f   : Square l t b r)
              → Square (ap g l) (ap g t) (ap g b) (ap g r)
  ap-square f id = id

                                 



  pair-square : {A B : Type} 
              {a00 a01 a10 a11 : A} 
              {la : a00 == a01}
              {ta : a00 == a10}
              {ba : a01 == a11}
              {ra : a10 == a11}
              (fa   : Square la ta ba ra)
              {b00 b01 b10 b11 : B} 
              {lb : b00 == b01}
              {tb : b00 == b10}
              {bb : b01 == b11}
              {rb : b10 == b11}
              (fb   : Square lb tb bb rb)
              → Square (pair×≃ la lb) (pair×≃ ta tb) (pair×≃ ba bb) (pair×≃ ra rb) 
  pair-square id id = id


  ap-square-symmetry : {A B : Type} (g : A → B) → 
              {a00 a01 a10 a11 : A} 
              {l : a00 == a01}
              {t : a00 == a10}
              {b : a01 == a11}
              {r : a10 == a11}
              (f   : Square l t b r)
              → ap-square g (square-symmetry f) == square-symmetry (ap-square g f)
  ap-square-symmetry _ id = id

  pair-square-symmetry : {A B : Type} 
              {a00 a01 a10 a11 : A} 
              {la : a00 == a01}
              {ta : a00 == a10}
              {ba : a01 == a11}
              {ra : a10 == a11}
              (fa   : Square la ta ba ra)
              {b00 b01 b10 b11 : B} 
              {lb : b00 == b01}
              {tb : b00 == b10}
              {bb : b01 == b11}
              {rb : b10 == b11}
              (fb   : Square lb tb bb rb)
              → square-symmetry (pair-square fa fb) == pair-square (square-symmetry fa) (square-symmetry fb)
  pair-square-symmetry id id = id

  hrefl-square-symmetry : {A : Type} {a00 a01 : A} {p : a00 == a01} 
                         → square-symmetry (hrefl-square{p = p}) == vrefl-square
  hrefl-square-symmetry {p = id} = id

  vrefl-square-symmetry : {A : Type} {a00 a01 : A} {p : a00 == a01} 
                         → square-symmetry (vrefl-square{p = p}) == hrefl-square
  vrefl-square-symmetry {p = id} = id

  vertical-degen-square-symmetry : {A : Type} {a a' : A} {p q : a == a'} (r : p == q)
                         → square-symmetry (vertical-degen-square r) == horiz-degen-square r
  vertical-degen-square-symmetry {p = id} id = id

  horiz-degen-square-symmetry : {A : Type} {a a' : A} {p q : a == a'} (r : p == q)
                         → square-symmetry (horiz-degen-square r) == vertical-degen-square r
  horiz-degen-square-symmetry {p = id} id = id

  pair-hrefl-vrefl-symmetry : {A : Type} {a00 a01 : A} (p : a00 == a01)
                         {B : Type} {b00 b01 : A} (q : b00 == b01)
                         → square-symmetry (pair-square (hrefl-square{p = p}) (vrefl-square{p = q}))
                         == pair-square vrefl-square hrefl-square
  pair-hrefl-vrefl-symmetry id id = id

  pair-vrefl-hrefl-symmetry : {A : Type} {a00 a01 : A} (p : a00 == a01)
                         {B : Type} {b00 b01 : B} (q : b00 == b01)
                         → square-symmetry (pair-square (vrefl-square{p = p}) (hrefl-square{p = q}))
                         == pair-square hrefl-square vrefl-square
  pair-vrefl-hrefl-symmetry id id = id

  ·-square-h-unit-r' :  {A : Type}
              {a00 a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
              (f   : Square p0- p-0 p-1 p1-)
              → f ·-square-h hrefl-square == whisker-square id (! (∘-unit-l p-0)) (! (∘-unit-l p-1)) id f 
  ·-square-h-unit-r' id = id

  ·-square-h-unit-r :  {A : Type}
              {a00 a11 : A} 
              {p0- : a00 == a11}
              {p1- : a00 == a11}
              (f   : Square p0- id id p1-)
              → f ·-square-h hrefl-square == f
  ·-square-h-unit-r f = ·-square-h-unit-r' f

  square-symmetry-symmetry : {A : Type} {a00 a01 a10 a11 : A} 
              {l : a00 == a01}
              {t : a00 == a10}
              {b : a01 == a11}
              {r : a10 == a11}
              (f   : Square l t b r)
              -> square-symmetry (square-symmetry f) == f
  square-symmetry-symmetry id = id

  ap-square-horiz-degen : {A B : Type} (f : A → B) {a1 a2 : A} {p q : a1 == a2} (r : p == q)
                  → ap-square f (horiz-degen-square r) == horiz-degen-square (ap (ap f) r)
  ap-square-horiz-degen _ {p = id} id = id

  apdo-by-equals :
    {Δ : Type} {A : Δ → Type} (f g : (θ : _) → A θ) {θ1 θ2 : Δ} (δ : θ1 == θ2) 
    (p : f == g)
    → SquareOver A hrefl-square (apdo f δ) (hom-to-over/left id (ap≃ p)) (hom-to-over/left id (ap≃ p)) (apdo g δ) 
  apdo-by-equals f .f id id = id

  apdo-square : 
              {A : Type} {B : A → Type} (f : (x : A) → B x)
              {a00 a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
              (fa   : Square p0- p-0 p-1 p1-)
              → SquareOver B fa (apdo f p0-) (apdo f p-0) (apdo f p-1) (apdo f p1-)
  apdo-square f id = id
                
  -- FIXME better definition?
  sides-same-square : {A : Type} {a : A} (p : a == a) → Square p p p p 
  sides-same-square p = disc-to-square {p0- = p} {p} {p} {p} id

  square-to-over-id : {A : Type} {a00 : A} {B : A → Type}
                      {b00 b01 b10 b11 : B a00} 
                      {p0- : b00 == b01}
                      {p-0 : b00 == b10}
                      {p-1 : b01 == b11}
                      {p1- : b10 == b11}
                      (f   : Square p0- p-0 p-1 p1-)
                   → SquareOver B id (hom-to-over p0-) (hom-to-over p-0) (hom-to-over p-1) (hom-to-over p1-)
  square-to-over-id id = id

  fill-square-right :  {A : Type} {a00 a01 a10 a11 : A}
             (l : a00 == a01) (t : a00 == a10) (b : a01 == a11)
             → Σ \ (r : a10 == a11) -> Square l t b r
  fill-square-right id id id = (id , id)

  ·-fill : {A : Type} {x y z : A} (p : x == y) (q : y == z)
            → (p · q) == fst (fill-square-right p id q)
  ·-fill id id = id

  -- for legacy reasons
  ∘-square : {A : Type} {x y z : A} {p : x == y} {q : y == z}
           → Square p id q (q ∘ p)
  ∘-square {p = id} {q} = connection

  HSet-UIP-Square : {A : Type} → HSet A → {a00 : A} {a01 a10 a11 : A} {l : a00 == a01} {t : a00 == a10} {b : a01 == a11} {r : a10 == a11}
                  → Square l t b r
  HSet-UIP-Square hA = disc-to-square (HSet-UIP hA _ _ _ _)

  out-square-Type : ∀ {A B C D} {l : A == B} {t : A == C} {b : B == D} {r : C == D}
                → (Square {Type} l t b r)
                → ((x : A) → coe (b ∘ l) x == coe (r ∘ t) x)
  out-square-Type id x = id


  -- special case of degenerating line to a square between functions, and then applying that square to the argument
  -- also like apdo-ap, but where the dimensions aren't independent (so a diagonal of a higher apdo-ap?)
  {-
  apply-equals-to-square/lr' : ∀ {A B} {f0 f1 : A → B} (F : f0 == f1) 
                         → {a00 a01 a10 a11 : A} 
                            {p0- : a00 == a01}
                            {p-0 : a00 == a10}
                            {p-1 : a01 == a11}
                            {p1- : a10 == a11}
                            (s   : Square p0- p-0 p-1 p1-)
                         → Square (ap f0 p0-) (ap≃₁→ F p-0) (ap≃₁→ F p-1) (ap f1 p1-)
  apply-equals-to-square/lr' {A}{B} F s = whisker-square {!!} {!!} {!!} {!!}
                                            (ap-square (λ (fx : (A → B) × A) → fst fx (snd fx))
                                             (pair-square (vrefl-square {p = F}) s))
  -}
  apply-line-to-square/tb : ∀ {A B} {f0 f1 : A → B} (F : f0 == f1) 
                         → {a00 a01 a10 a11 : A} 
                            {p0- : a00 == a01}
                            {p-0 : a00 == a10}
                            {p-1 : a01 == a11}
                            {p1- : a10 == a11}
                            (s   : Square p0- p-0 p-1 p1-)
                         → Square (ap f0 p0-) (ap (\ fx → (fst fx) (snd fx)) (pair×≃ F p-0)) (ap (\ fx → (fst fx) (snd fx)) (pair×≃ F p-1)) (ap f1 p1-)
  apply-line-to-square/tb id id = id

  {-
    SquareOver-ap-El : {A : Type} {B : A → Type}
              {a00 : A} {b00 : B a00} 
              {a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
              {f   : Square p0- p-0 p-1 p1- }
              {b01 : B a01} {b10 : B a10} {b11 : B a11}  
              {q0- : PathOver B p0- b00 b01}
              {q-0 : PathOver B p-0 b00 b10}
              {q-1 : PathOver B p-1 b01 b11}
              {q1- : PathOver B p1- b10 b11}
              → SquareOver (λ X₁ → X₁) (ap-square B f) (over-o-ap (λ X₁ → X₁) q0-) (over-o-ap (λ X₁ → X₁) q-0) (over-o-ap (λ X₁ → X₁) q-1) (over-o-ap (λ X₁ → X₁) q1-)
              → SquareOver B f q0- q-0 q-1 q1-
  -}
{-
  out-SquareΣ : {A : Type} {B : A → Type}
                  {p00 p01 p10 p11 : Σ B}
                  {l : p00 == p01}
                  {t : p00 == p10}
                  {b : p01 == p11}
                  {r : p10 == p11}
                → (Square l t b r) → 
                         (Σ (λ (s1 : Square (ap fst l) (ap fst t) (ap fst b) (ap fst r)) → 
                            SquareOver B s1
                                       (over-o-ap B (apdo snd l))
                                       (over-o-ap B (apdo snd t))
                                       (over-o-ap B (apdo snd b))
                                       (over-o-ap B (apdo snd r))))
  out-SquareΣ id = (id , id)

  
  SquareΣ-eqv : {A : Type} {B : A → Type}
                  {p00 p01 p10 p11 : Σ B}
                  {l : p00 == p01}
                  {t : p00 == p10}
                  {b : p01 == p11}
                  {r : p10 == p11}
                → Equiv (Square l t b r)
                         (Σ (λ (s1 : Square (ap fst l) (ap fst t) (ap fst b) (ap fst r)) → 
                            SquareOver B s1
                                       (over-o-ap B (apdo snd l))
                                       (over-o-ap B (apdo snd t))
                                       (over-o-ap B (apdo snd b))
                                       (over-o-ap B (apdo snd r))))
  SquareΣ-eqv = (out-SquareΣ , ?) 

  -- derive from above
  SquareΣ-eqv-intro : {A : Type} {B : A → Type}
                  {p00 p01 p10 p11 : A}
                  {l : p00 == p01}
                  {t : p00 == p10}
                  {b : p01 == p11}
                  {r : p10 == p11}
                  → ∀ {p00b p01b p10b p11b}
                  {lb : PathOver B l p00b p01b}
                  {tb : PathOver B t p00b p10b}
                  {bb : PathOver B b p01b p11b}
                  {rb : PathOver B r p10b p11b}
                → Equiv (Square (pair= l lb) (pair= t tb) (pair= b bb) (pair= r rb))
                         (Σ (λ (s1 : Square l t b r) → 
                            SquareOver B s1 lb tb bb rb))
  SquareΣ-eqv-intro = ?

  out-SquareOver-Π-eqv : {A : Type} {B1 : A → Type} {B2 : Σ B1 → Type}
              {a00 : A} {b00 : (x : B1 a00) → B2 (a00 , x)} 
              {a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
              {f   : Square p0- p-0 p-1 p1- }
              {b01 : (x : B1 a01) → B2 (a01 , x)} {b10 : (x : B1 a10) → B2 (a10 , x)} {b11 : (x : B1 a11) → B2 (a11 , x)}  
              {q0- : PathOver (\ a -> (x : B1 a) → B2 (a , x)) p0- b00 b01}
              {q-0 : PathOver (\ a -> (x : B1 a) → B2 (a , x)) p-0 b00 b10}
              {q-1 : PathOver (\ a -> (x : B1 a) → B2 (a , x)) p-1 b01 b11}
              {q1- : PathOver (\ a -> (x : B1 a) → B2 (a , x)) p1- b10 b11}
              →  (SquareOver (\ a -> (x : B1 a) → B2 (a , x)) f q0- q-0 q-1 q1-) 
              →  ((b100 : B1 a00) (b110 : B1 a10) (b101 : B1 a01) (b111 : B1 a11)
                         (q10- : PathOver B1 p0- b100 b101)
                         (q1-0 : PathOver B1 p-0 b100 b110)
                         (q1-1 : PathOver B1 p-1 b101 b111)
                         (q11- : PathOver B1 p1- b110 b111) →
                         (f1 : SquareOver B1 f q10- q1-0 q1-1 q11-) → 
                         SquareOver B2 (ine SquareΣ-eqv-intro (f , f1)) (oute PathOverΠ-eqv q0- _ _ q10-) (oute PathOverΠ-eqv q-0 _ _ q1-0) (oute PathOverΠ-eqv q-1 _ _ q1-1) (oute PathOverΠ-eqv q1- _ _ q11-))
  out-SquareOver-Π-eqv id _ _ _ _ _ _ _ _ f1 = {!!}

  SquareOver-Π-eqv : {A : Type} {B1 : A → Type} {B2 : Σ B1 → Type}
              {a00 : A} {b00 : (x : B1 a00) → B2 (a00 , x)} 
              {a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
              {f   : Square p0- p-0 p-1 p1- }
              {b01 : (x : B1 a01) → B2 (a01 , x)} {b10 : (x : B1 a10) → B2 (a10 , x)} {b11 : (x : B1 a11) → B2 (a11 , x)}  
              {q0- : PathOver (\ a -> (x : B1 a) → B2 (a , x)) p0- b00 b01}
              {q-0 : PathOver (\ a -> (x : B1 a) → B2 (a , x)) p-0 b00 b10}
              {q-1 : PathOver (\ a -> (x : B1 a) → B2 (a , x)) p-1 b01 b11}
              {q1- : PathOver (\ a -> (x : B1 a) → B2 (a , x)) p1- b10 b11}
              → Equiv (SquareOver (\ a -> (x : B1 a) → B2 (a , x)) f q0- q-0 q-1 q1-) 
                      ((b100 : B1 a00) (b110 : B1 a10) (b101 : B1 a01) (b111 : B1 a11)
                         (q10- : PathOver B1 p0- b100 b101)
                         (q1-0 : PathOver B1 p-0 b100 b110)
                         (q1-1 : PathOver B1 p-1 b101 b111)
                         (q11- : PathOver B1 p1- b110 b111) →
                         (f1 : SquareOver B1 f q10- q1-0 q1-1 q11-) → 
                         SquareOver B2 (ine SquareΣ-eqv-intro (f , f1)) (oute PathOverΠ-eqv q0- _ _ q10-) (oute PathOverΠ-eqv q-0 _ _ q1-0) (oute PathOverΠ-eqv q-1 _ _ q1-1) (oute PathOverΠ-eqv q1- _ _ q11-))
  SquareOver-Π-eqv = out-SquareOver-Π-eqv , ?


  in-square-Type : ∀ {A B C D} {l : A == B} {t : A == C} {b : B == D} {r : C == D}
                  → ((x : A) → coe (b ∘ l) x == coe (r ∘ t) x)
                  → (Square {Type} l t b r)
  in-square-Type = ?
-}

{-
  square-Type-eqv : ∀ {A B C D} {l : A == B} {t : A == C} {b : B == D} {r : C == D}
                → Equiv (Square {Type} l t b r)
                        ((x : A) → coe (b ∘ l) x == coe (r ∘ t) x)
  square-Type-eqv = improve (hequiv out-square-Type in-square-Type ? ?) 

  out-squareover-El : ∀ {A B C D} {l : A == B} {t : A == C} {b : B == D} {r : C == D} {s : (Square {Type} l t b r)}
                          {b1 : A} {b2 : B} {b3 : C} {b4 : D}
                          {lo : PathOver (\ X -> X) l b1 b2}
                          {to : PathOver (\ X -> X) t b1 b3}
                          {bo : PathOver (\ X -> X) b b2 b4}
                          {ro : PathOver (\ X -> X) r b3 b4}
                        → (SquareOver (\ X -> X) s lo to bo ro)
                        → (Square{D} (over-to-hom/left (bo ∘o lo)) 
                                      (out-square-Type s b1) 
                                      id
                                      (over-to-hom/left (ro ∘o to)))
  out-squareover-El id = id
-}
{-
    in-squareover-El : ∀ {A B C D} {l : A == B} {t : A == C} {b : B == D} {r : C == D} {s : (Square {Type} l t b r)}
                            {b1 : A}
                            {b2 : B}
                            {lo : PathOver (\ X -> X) l b1 b2}
                            {b3 : C}
                            {to : PathOver (\ X -> X) t b1 b3}
                            {b4 : D}
                            {bo : PathOver (\ X -> X) b b2 b4}
                            {ro : PathOver (\ X -> X) r b3 b4}
                         → (Square (over-to-hom/left (bo ∘o lo)) 
                                    (out-square-Type s b1) 
                                    id
                                    (over-to-hom/left (ro ∘o to)))
                         → (SquareOver (\ X -> X) s lo to bo ro)
  -- in-squareover-El id = path-induction-homo-e _ (path-induction-homo-e _ (path-induction-homo-e _ {!!})) 
-}  
{-
  squareover-El-eqv : ∀ {A B C D} {l : A == B} {t : A == C} {b : B == D} {r : C == D} {s : (Square {Type} l t b r)}
                          {b1 : A} {b2 : B} {b3 : C} {b4 : D}
                          {lo : PathOver (\ X -> X) l b1 b2}
                          {to : PathOver (\ X -> X) t b1 b3}
                          {bo : PathOver (\ X -> X) b b2 b4}
                          {ro : PathOver (\ X -> X) r b3 b4}
                       → Equiv (SquareOver (\ X -> X) s lo to bo ro)
                               (Square (over-to-hom/left (bo ∘o lo)) 
                                       (out-square-Type s b1) 
                                       id
                                       (over-to-hom/left (ro ∘o to)))
  squareover-El-eqv = improve (hequiv out-squareover-El (in-squareover-El _ _ _ _ _ _ _ _) ? ? ) 

  out-SquareOver-constant : {A : Type} {B : Type} {a00 : A} {b00 : B }  
              {a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
              {f   : Square p0- p-0 p-1 p1- }
              {b01 : B} {b10 : B} {b11 : B}  
              {q0- : PathOver (\ _ -> B) p0- b00 b01}
              {q-0 : PathOver (\ _ -> B) p-0 b00 b10}
              {q-1 : PathOver (\ _ -> B) p-1 b01 b11}
              {q1- : PathOver (\ _ -> B) p1- b10 b11}
              → SquareOver (\ _ -> B) f q0- q-0 q-1 q1- 
              → Square (out-PathOver-constant q0-) (out-PathOver-constant q-0) (out-PathOver-constant q-1) (out-PathOver-constant q1-)
  out-SquareOver-constant id = id
  
  SquareOver-constant-eqv : {A : Type} {B : Type} {a00 : A} {b00 : B }  
              {a01 a10 a11 : A} 
              {p0- : a00 == a01}
              {p-0 : a00 == a10}
              {p-1 : a01 == a11}
              {p1- : a10 == a11}
              {f   : Square p0- p-0 p-1 p1- }
              {b01 : B} {b10 : B} {b11 : B}  
              {q0- : PathOver (\ _ -> B) p0- b00 b01}
              {q-0 : PathOver (\ _ -> B) p-0 b00 b10}
              {q-1 : PathOver (\ _ -> B) p-1 b01 b11}
              {q1- : PathOver (\ _ -> B) p1- b10 b11}
              → Equiv (SquareOver (\ _ -> B) f q0- q-0 q-1 q1-)
                      (Square (out-PathOver-constant q0-) (out-PathOver-constant q-0) (out-PathOver-constant q-1) (out-PathOver-constant q1-))
  SquareOver-constant-eqv = (out-SquareOver-constant , ?) 
-}

