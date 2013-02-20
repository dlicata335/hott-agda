
{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open Int
open Truncation

module homotopy.Modular where

  -- FIXME move to library

  nfold∘ : ∀ {A a} → Nat → Path{A} a a → Path a a
  nfold∘ Z α = id
  nfold∘ (S n) α = α ∘ nfold∘ n α

  module M where
    private
      data M' (d : Nat) : Type where
        Base : M' d
  
    M : Nat -> Type
    M = M'
  
    base : ∀ {d} → M d
    base = Base
  
    postulate {- HoTT Axiom -}
      loop  : (d : Nat) → Path{M d} base base
      order : ∀ {d : Nat} → nfold∘ d (loop d) ≃ id 

    M-rec : {d : Nat} {C : Type} 
           -> (c : C)
           -> (loop' : Path c c)
           -> (order' : nfold∘ d loop' ≃ id)
           -> M d -> C
    M-rec c _ _ Base = c

    postulate {- HoTT Axiom -} 
      βloop/rec : {d : Nat} {C : Type} 
           -> (c : C)
           -> (loop' : Path c c)
           -> (order' : nfold∘ d loop' ≃ id)
           -> Path (ap (M-rec c loop' order') (loop d)) loop'
  
    M-elim :   ∀ {d} (C : M d -> Type)
            -> (c : C base) 
               (loop' : Path (transport C (loop d) c) c)
               (order' : {!!})
            -> (x : M d) -> C x
    M-elim _ x _ _ Base = x

  open M using (M-rec ; M-elim ; M)

  data Fin : Nat -> Set where
    Z : {n : Nat} -> Fin (S n)
    S : {n : Nat} -> Fin n -> Fin (S n)

  last? : ∀ {n} → Fin (S n) → Maybe (Fin n)
  last? {Z} Z = None
  last? {Z} (S ())
  last? {S n} Z = Some Z
  last? {S n} (S fn) with last? fn
  ... | Some fn' = Some (S fn')
  ... | None = None

  fsucc : ∀ {n} → Fin n → Fin n
  fsucc {Z} ()
  fsucc {S n} fn with last? fn
  ...         | None = Z
  ...         | Some x = S x

  postulate 
    fsucc-is-equiv : ∀ {n} → IsEquiv (fsucc{n})

  nfold-o : ∀ {A} (n : Nat) -> (f : A → A) → (A → A)
  nfold-o Z f = (\ x -> x)
  nfold-o (S n) f = f o (nfold-o n f)

  postulate
    fsucc-order : ∀ n → nfold-o n (fsucc{n}) ≃ (\ x -> x)
  -- fsucc-order Z = id
  -- fsucc-order (S n) = λ≃ (l n) where
  --   l : ∀ n → (x : Fin (S (S n)))
  --     → Path (nfold-o (S n) fsucc x) x
  --   l n x with last? x
  --   ...  | Some a = {!l _ (S a)!}
  --   ...  | None = {!!}
  -- start of this file

  coe-nfold∘ : ∀ {A} → (n : Nat) (α : Path{Type} A A)
             → coe (nfold∘ n α) ≃ nfold-o n (coe α)
  coe-nfold∘ Z α = id
  coe-nfold∘ (S n) α = λ≃ (λ x → ap (coe α) (ap≃ (coe-nfold∘ n α))) ∘ transport-∘ (λ x → x) α (nfold∘ n α)


  module MPath (d0 : Nat) where

    d : Nat
    d = S d0

    decode' : {d' : _} → Fin d' → Path{M d} M.base M.base
    decode' Z = id
    decode' (S n) = M.loop d ∘ decode' n

    Codes : M d → Type
    Codes = M-rec (Fin d)
                  (ua (fsucc , fsucc-is-equiv)) 
                  (type≃-ext _ _ (λ x → ap≃ (fsucc-order d) ∘ ap (λ p → nfold-o d p x) (type≃β _) ∘ ap≃ (coe-nfold∘ d _)))

    P : M d → Type
    P x = Path{M d} M.base x

    encode : {x : M d} → P x → Codes x 
    encode α = transport Codes α Z

    postulate
      _≤n_ : Nat → Nat → Type 
      ≤n-unS-left : ∀ {m n} → (S m) ≤n (S n) → m ≤n S n
      weaken : ∀ {m n} → m ≤n n → Fin m → Fin n
      weaken-Z : {m n : Nat} (lt : (S m) ≤n (S n)) → weaken lt Z ≃ Z

      fsucc-weaken : ∀ {m1 m2} → (lt : S m1 ≤n S m2) (n : Fin m1)
        → fsucc (weaken (≤n-unS-left lt) n) ≃ (weaken lt (S n))

    encode-decode' : ∀ {d'} (c : Fin d') → (lt : d' ≤n d) 
                   → encode (decode' c) ≃ weaken lt c
    encode-decode' Z lt = ! (weaken-Z lt)
    encode-decode' (S n) lt =
      encode (decode' (S n)) ≃〈 id 〉 
      encode (M.loop d ∘ decode' n) ≃〈 id 〉 
      transport Codes (M.loop d ∘ decode' n) Z ≃〈 ap≃ (transport-∘ Codes (M.loop d) (decode' n)) 〉 
      transport Codes (M.loop d) (encode (decode' n)) ≃〈 ap (transport Codes (M.loop d)) (encode-decode' n (≤n-unS-left lt)) 〉 
      transport Codes (M.loop d) (weaken (≤n-unS-left lt) n) ≃〈 ap≃ (transport-ap-assoc Codes (M.loop d)) 〉 
      coe (ap Codes (M.loop d)) (weaken (≤n-unS-left lt) n) ≃〈 ap (λ x → coe x (weaken (≤n-unS-left lt) n)) (M.βloop/rec _ _ _) 〉 
      coe (ua (fsucc , fsucc-is-equiv)) (weaken (≤n-unS-left lt) n) ≃〈 ap≃ (type≃β (fsucc , fsucc-is-equiv)) 〉 
      fsucc (weaken (≤n-unS-left lt) n) ≃〈 fsucc-weaken lt _ 〉 
      (weaken lt (S n)) ∎

    decode : {x : M d} → Codes x → P x
    decode {x} = 
      M-elim (\ x -> Codes x → P x) decode' 
             (transport (λ x' → Codes x' → P x') (M.loop d) decode' ≃〈 {!!} 〉
              transport P (M.loop d) o decode' o transport Codes (! (M.loop d))  ≃〈 {!!} 〉
              decode' ∎)
             {!!}
             x where
      STS1 : transport P (M.loop d) o decode' 
           ≃ decode' o transport Codes (M.loop d)
      STS1 = {!!}
    
      STS2 : ∀ {d'} (x : Fin d')
           → (M.loop d) ∘ (decode' x) ≃ decode' (fsucc x)
      STS2 {Z} ()
      STS2 {S d'} x with last? x
      ... | Some x' = {!id!}
      ... | None = {!!}
