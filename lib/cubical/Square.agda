
{-# OPTIONS --type-in-type --without-K #-}

open import lib.BasicTypes
open import lib.cubical.PathOver

module lib.cubical.Square where

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

  module PathOver= where

    out-PathOver-= : {A B : Type} {f g : A → B}
                {a a' : A} {p : a == a'}
                {pa : f a == g a}
                {pa' : f a' == g a'}
               → PathOver (\ x -> f x == g x) p pa pa'
               → Square pa (ap f p) (ap g p) pa'
    out-PathOver-= id = hrefl-square

    postulate 
      in-PathOver-= : {A B : Type} {f g : A → B}
                {a a' : A} {p : a == a'}
                {pa : f a == g a}
                {pa' : f a' == g a'}
               → Square pa (ap f p) (ap g p) pa'
               → PathOver (\ x -> f x == g x) p pa pa'
      
    out-PathOver-=-eqv : {A B : Type} {f g : A → B}
                {a a' : A} {p : a == a'}
                {pa : f a == g a}
                {pa' : f a' == g a'}
               → Equiv (PathOver (\ x -> f x == g x) p pa pa')
                        (Square pa (ap f p) (ap g p) pa')
    out-PathOver-=-eqv = improve (hequiv out-PathOver-= in-PathOver-= FIXME1 FIXME2) where
      postulate FIXME1 : _
                FIXME2 : _
  

  extend-triangle : {A : Type} {a00 a01 a11 : A}
              {p0- : a00 == a01}
              {p-1 : a01 == a11}
              {p1- : a00 == a11}
              (f   : Square p0- id p-1 p1-)
              → {a00' : A} (p : a00' == a00) 
              → Square (p0- ∘ p) id p-1 (p1- ∘ p)
  extend-triangle f id = f

  ∘-square-vertical : {A : Type}
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
  ∘-square-vertical id s = s
  
  _∘-square-v_ = ∘-square-vertical

  -- FIXME: how do you get this from a Kan filling?
  ∘-square-vertical/degen-bot : {A : Type}
    {a b c d : A}
    {l : a == b} 
    {t : a == c} 
    {bt : b == d} 
    {r : c == d} 
    {b' : b == d}  
    → (Square l t bt r)
    → (Square id bt b' id)
    → Square l t b' r
  ∘-square-vertical/degen-bot id s = s

  ∘-square-vertical/degen-top : {A : Type}
    {a b c d : A}
    {l : a == b} 
    {t : a == c} 
    {bt : a == c} 
    {r : c == d} 
    {b' : b == d}  
    → (Square id t bt id)
    → (Square l bt b' r)
    → Square l t b' r
  ∘-square-vertical/degen-top s id = s

  ∘-square-horiz : {A : Type}
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
  ∘-square-horiz id s = s

  _∘-square-h_ = ∘-square-horiz

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

  connection2 : {A : Type} {a1 a2 a3 : A} {p : a1 == a2} {q : a2 == a3} → Square p p q q
  connection2 {p = id} {q = id} = id

  ∘-square : {A : Type} {a0 a1 a2 : A} {p : a0 == a1} {q : a1 == a2} 
           → Square p id q (q ∘ p)
  ∘-square {p = id} = connection


  ap-square : {A B : Type} (g : A → B) → 
              {a00 a01 a10 a11 : A} 
              {l : a00 == a01}
              {t : a00 == a10}
              {b : a01 == a11}
              {r : a10 == a11}
              (f   : Square l t b r)
              → Square (ap g l) (ap g t) (ap g b) (ap g r)
  ap-square f id = id

  horiz-degen-square : {A : Type} {a a' : A} {p q : a == a'} (r : p == q)
                     → Square p id id q
  horiz-degen-square {p = id}{q = .id} id = id
  -- disc-to-square {p0- = p} {id} {id} {q}

  horiz-degen-square-to-path : {A : Type} {a a' : A} {p q : a == a'} 
                     → Square p id id q → p == q
  horiz-degen-square-to-path {p = p} s = square-to-disc s ∘ ! (∘-unit-l p)

  vertical-degen-square : {A : Type} {a a' : A} {p q : a == a'} (r : p == q)
                     → Square id p q id
  vertical-degen-square {p = id}{q = .id} id = id


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
  SquareΣ-eqv = (out-SquareΣ , FIXME) where postulate FIXME : ∀ {A : Type} → A

  -- derive from above
  postulate
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
  
  postulate
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


  postulate
    in-square-Type : ∀ {A B C D} {l : A == B} {t : A == C} {b : B == D} {r : C == D}
                  → ((x : A) → coe (b ∘ l) x == coe (r ∘ t) x)
                  → (Square {Type} l t b r)

  out-square-Type : ∀ {A B C D} {l : A == B} {t : A == C} {b : B == D} {r : C == D}
                → (Square {Type} l t b r)
                → ((x : A) → coe (b ∘ l) x == coe (r ∘ t) x)
  out-square-Type id x = id

  square-Type-eqv : ∀ {A B C D} {l : A == B} {t : A == C} {b : B == D} {r : C == D}
                → Equiv (Square {Type} l t b r)
                        ((x : A) → coe (b ∘ l) x == coe (r ∘ t) x)
  square-Type-eqv = improve (hequiv out-square-Type in-square-Type FIXME FIXME) where
    postulate
      FIXME : {A : Type} → A

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

  postulate
    in-squareover-El : ∀ {A B C D} {l : A == B} {t : A == C} {b : B == D} {r : C == D} (s : (Square {Type} l t b r))
                          {b1 : A}
                          (b2 : B) 
                          (lo : PathOver (\ X -> X) l b1 b2)
                          (b3 : C)
                          (to : PathOver (\ X -> X) t b1 b3)
                          (b4 : D)
                          (bo : PathOver (\ X -> X) b b2 b4)
                          (ro : PathOver (\ X -> X) r b3 b4)
                       → (Square (over-to-hom/left (bo ∘o lo)) 
                                  (out-square-Type s b1) 
                                  id
                                  (over-to-hom/left (ro ∘o to)))
                       → (SquareOver (\ X -> X) s lo to bo ro)
  --in-squareover-El id = path-induction-homo-e _ (path-induction-homo-e _ (path-induction-homo-e _ {!!})) 

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
  squareover-El-eqv = improve (hequiv out-squareover-El (in-squareover-El _ _ _ _ _ _ _ _) FIXME FIXME) where
    postulate FIXME : {A : Type} → A

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
              → Square (oute PathOver-constant-eqv q0-) (oute PathOver-constant-eqv q-0) (oute PathOver-constant-eqv q-1) (oute PathOver-constant-eqv q1-)
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
                      (Square (oute PathOver-constant-eqv q0-) (oute PathOver-constant-eqv q-0) (oute PathOver-constant-eqv q-1) (oute PathOver-constant-eqv q1-))
  SquareOver-constant-eqv = (out-SquareOver-constant , FIXME) where
    postulate FIXME : {A : Type} → A
