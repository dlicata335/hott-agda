{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open import lib.cubical.Cubical

module misc.GlueFullUA where

  self-double : ∀ {A} {x : A} {α : x == x} → α == α ∘ α → α == id
  self-double {α = α} p = ! (!-inv-l-front α α ∘ ap (_∘_ (! α)) p ∘ ! (!-inv-l α))

  endo-path-naturality : ∀ {A} (f : {x y : A} → x == y -> x == y) → { x y : A} (p : x == y) → f p == p ∘ f id 
  endo-path-naturality f id = ! (∘-unit-l (f id))

  retract-of-Id-is-Id : ∀ {A} {R : A → A → Type} → 
                  (r : {x y : A} → x == y -> R x y)
                  (s : {x y : A} → R x y → x == y)
                  (comp1 : {x y : A} (c : R x y) → r (s c) == c) -- r is a retract of s 
                → {x y : A} → IsEquiv {x == y} {R x y} (r {x}{y})
  retract-of-Id-is-Id r s comp1 = snd (improve (hequiv r s comp2 comp1)) where

    s-r-idempotent : ∀ {x y} p → s{x}{y} (r{x}{y} (s{x}{y} (r{x}{y} p))) == s (r p)
    s-r-idempotent p = ap s (comp1 (r p))
  
    comp2 : ∀ {x y} (p : x == y) → s (r p) == p
    comp2 id = self-double (endo-path-naturality (λ x → s (r x)) (s (r id)) ∘ ! (s-r-idempotent id)) 

  -- read α : A == B as a line in type, and PathOver α as a line as a classifier

  postulate
    -- this is the ua e instance of glue (Glue B [i=0 -> (B , id-equiv), i=1 -> (X, e)])
    -- contravariance isn't necessary, I did that just to match CCHM Glue
    Glue : ∀ (B : Type) {X : Type} → Equiv X B → B == X

    -- this is a use of the ua Glue where α and β are already lines
    Glue-for-lines : ∀ {A B} {α : A == B} {β} → (∀ {a b} → Equiv (PathOver (\ X → X) α a b) (PathOver (\ X → X) β a b)) → α == β

    -- this is the intro and elim for Glue
    unglue-eqv : ∀ {B X} (e : Equiv X B) {b0 x} → Equiv (PathOver (\ X → X) (Glue B e) b0 x) (b0 == fst e x)

  -- proof of full univalence below also uses funext,
  -- so you need to postulate/have that separately (or can it be proved directly from the above 3 axioms?)

  coe-Glue-eqv : ∀ {B X} (e : Equiv X B) {b0 x} 
     → Equiv (b0 == coe (! (Glue B e)) x) (b0 == fst e x)
  coe-Glue-eqv {B} e = (unglue-eqv e) ∘equiv (hom-to-over/right-eqv {A = \ X → X} (Glue B e))

  Glue-with-id : ∀ {B} → Glue B (id-equiv) == id
  Glue-with-id = Glue-for-lines (hom-to-over/right-eqv id ∘equiv unglue-eqv id-equiv)

  !Glue : ∀ {B X : Type} → B == X → Equiv X B 
  !Glue α = !equiv (coe-equiv α)

  full : ∀ {B X} → IsEquiv {Equiv X B} {B == X} (Glue B)
  full {B} = snd (improve (hequiv (Glue B)
                                  !Glue 
                                  (λ e → pair≃ (composite1 e) (HProp-unique (IsEquiv-HProp _) _ _)) 
                                  composite2)) where

       composite1 : ∀ {X} (e : Equiv X B) → coe (! (Glue B e)) == fst e 
       composite1 e = λ≃ (λ x → fst (coe-Glue-eqv e) id)

       composite2 : ∀ {B X} → (y : B == X) → Path (Glue B (!equiv (coe-equiv y))) y
       composite2 id = Glue-with-id

  VV : ∀ {A B} → IsEquiv {A == B} {Equiv A B} (pathToEquiv)
  VV = transport IsEquiv (λ≃ fix-map) (snd (!equiv-equiv ∘equiv !equiv (_ , full))) where
    fix-map : ∀ {A B} (x : A == B) → Path (fst (!equiv-equiv ∘equiv !equiv (Glue A , full)) x) (pathToEquiv x)
    fix-map id = id

  -- ----------------------------------------------------------------------

  glue : ∀ {B X} (e : Equiv X B) {b0 x}
       → (b : b0 == fst e x)
       → PathOver (\ X → X) (Glue B e) b0 x 
  glue e = IsEquiv.g (snd (unglue-eqv e))

  unglue : ∀ {B X} (e : Equiv X B) {b0 x} 
         → PathOver (λ X → X) (Glue B e) b0 x
         → Path{B} b0 (fst e x)
  unglue e = fst (unglue-eqv e)

  unglueβ : ∀ {B X} {b0 x} (e : Equiv X B) (b : b0 == fst e x) → unglue e (glue e b) == b
  unglueβ e b = IsEquiv.β (snd (unglue-eqv e)) b

  unglueη : ∀ {B X} {b x} (e : Equiv X B) (p : PathOver (λ X → X) (Glue B e) b x) 
          → glue e (unglue e p) == p
  unglueη e b = IsEquiv.α (snd (unglue-eqv e)) b

  ungluecoh : ∀ {B X} (e : Equiv X B) {b0 x} 
            → (p : PathOver (λ X → X) (Glue B e) b0 x) 
            → (unglueβ e (unglue e p)) == (ap (unglue e) (unglueη e p)) 
  ungluecoh e p = IsEquiv.γ (snd (unglue-eqv e)) p


