
{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.NType
open import lib.Universe

module lib.Group where

  Ident : ∀ {A} -> (A -> A -> Type) -> Type
  Ident Arr = ∀ {x} -> Arr x x

  Inv : ∀ {A} -> (A -> A -> Type) -> Type
  Inv Arr = ∀ {x y} -> Arr x y -> Arr y x

  Comp : ∀ {A} -> (A -> A -> Type) -> Type
  Comp Arr = ∀ {x y z} -> Arr x y -> Arr y z -> Arr x z

  record Group : Type where
   field
    El       : Type
    El-level : NType (tl 0) El
    ident   : El
    inv     : El -> El 
    comp    : El -> El -> El
    unitl   : ∀ a -> comp ident a ≃ a
    unitr   : ∀ a -> comp a ident ≃ a
    assoc   : ∀ a b c -> comp (comp a b) c ≃ comp a (comp b c)
    invr    : ∀ a -> (comp a (inv a)) ≃ ident
    invl    : ∀ a -> (comp (inv a) a) ≃ ident
  open Group

  record GroupHom (G : Group) (H : Group) : Type where
   field
    f : El G -> El H
    pres-ident : f (ident G) ≃ ident H
    pres-comp  : ∀ g1 g2 → f (comp G g1 g2) ≃ comp H (f g1) (f g2)
  
  PathGroup : (A : NTypes (tl 1)) (a0 : fst A) -> Group
  PathGroup (A , A-level) a0 = record { El = Path a0 a0; El-level = use-level A-level _ _; ident = id; inv = !; comp = \ x y -> y ∘ x; 
                                        unitl = λ _ → id ; unitr = λ a → ∘-unit-l a ; assoc = (λ a b c → ∘-assoc c b a) ; invl = λ a → !-inv-r a; invr = λ a → !-inv-l a }

