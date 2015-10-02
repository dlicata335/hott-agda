
open import functorlogic.Lib 

module functorlogic.Modes where

  -- use postulates rather than variables so the rewrite mechanism works
  -- don't want a datatype because we don't want elims

  {-# BUILTIN REWRITE _==_ #-}

  postulate
    Mode : Set 

    _≥_ : Mode -> Mode -> Set 
    1m : {m : Mode} → m ≥ m
    _∘1_ : {x y z : Mode} → z ≥ y → y ≥ x → z ≥ x -- function composition order

    ∘1-unit-l : ∀ {x y : Mode} {α : x ≥ y} → (1m ∘1 α) == α
    ∘1-unit-r : ∀ {x y : Mode} {α : x ≥ y} → (α ∘1 1m) == α
    ∘1-assoc  : ∀ {x y z w : Mode} {α : w ≥ z} {β : z ≥ y} {γ : y ≥ x} → ((α ∘1 β) ∘1 γ) == (α ∘1 (β ∘1 γ))

  {-# REWRITE ∘1-unit-l #-}
  {-# REWRITE ∘1-unit-r #-}
  {-# REWRITE ∘1-assoc #-}

  postulate
    ∘1-assoc'  : ∀ {x y z w : Mode} {α : w ≥ z} {β : z ≥ y} {γ : y ≥ x} → (∘1-assoc {α = α} {β} {γ}) == id

  postulate
    _⇒_ : ∀ {p q} → (α β : p ≥ q) → Set 
    1⇒ : ∀ {p q} → {α : p ≥ q} → α ⇒ α
    _·2_ : {x y : Mode} {p q r : x ≥ y} → p ⇒ q → q ⇒ r → p ⇒ r
    _∘1cong_ : {x y z : Mode} {p p' : x ≥ y} {q q' : y ≥ z} → p ⇒ p' → q ⇒ q' → (p ∘1 q) ⇒ (p' ∘1 q')

  1⇒' : ∀ {p q} → {α β : p ≥ q} → α == β -> α ⇒ β
  1⇒' id = 1⇒

  postulate
    ∘1cong-unit-l : {x z : Mode} {q q' : x ≥ z} (β : q ⇒ q') → (1⇒ {_}{_}{1m} ∘1cong β) == β
    ∘1cong-unit-r : {x z : Mode} {q q' : x ≥ z} (β : q ⇒ q') → (β ∘1cong 1⇒ {_}{_}{1m} ) == β
    -- FIXME: doesn't always seem to be working as a rewrite
    ∘1cong-assoc : {x y z w : Mode} {p p' : x ≥ y} {q q' : y ≥ z} {r r' : z ≥ w} {e1 : p ⇒ p'} {e2 : q ⇒ q'} {e3 : r ⇒ r'} 
                 → ((e1 ∘1cong e2) ∘1cong e3) == (e1 ∘1cong (e2 ∘1cong e3))
    ·2-unit-r : {x y : Mode} {p q : x ≥ y} (α : p ⇒ q) → (α ·2 1⇒) == α
    ·2-unit-l : {x y : Mode} {p q : x ≥ y} (α : p ⇒ q) → (1⇒ ·2 α) == α
    ·2-assoc  : ∀ {x y : Mode} {α β γ δ : x ≥ y} {e1 : α ⇒ β} {e2 : β ⇒ γ} {e3 : γ ⇒ δ}
              → ((e1 ·2 e2) ·2 e3) == (e1 ·2 (e2 ·2 e3))
    interchange : {x y z : Mode} {p1 p2 p3 : x ≥ y} {e1 : p1 ⇒ p2} {e2 : p2 ⇒ p3}
                  {q1 q2 q3 : y ≥ z} {f1 : q1 ⇒ q2} {f2 : q2 ⇒ q3}
                → ((e1 ·2 e2) ∘1cong (f1 ·2 f2))  == ((e1 ∘1cong f1) ·2 (e2 ∘1cong f2))
    -- FIXME: shouldn't this be provable from the others?
    ·1cong-1⇒ : {x y z : Mode} {p : z ≥ y} {q : y ≥ x} → (1⇒ {_}{_}{p} ∘1cong 1⇒ {_}{_}{q}) == 1⇒

  {-# REWRITE ∘1cong-unit-l #-}
  {-# REWRITE ∘1cong-unit-r #-}
  {-# REWRITE ·2-unit-r #-}
  {-# REWRITE ·2-unit-l #-}
  {-# REWRITE ·1cong-1⇒ #-}
  {-# REWRITE ·2-assoc #-}
  {-# REWRITE ∘1cong-assoc #-}
