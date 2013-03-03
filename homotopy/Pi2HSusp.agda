
{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open Int
open Truncation
open LoopSpace
open Suspension
open import homotopy.HStructure

module homotopy.Pi2HSusp (A : Type) 
                         (a0 : A)
                         (A-level : NType (tl 1) A)
                         (A-Connected : Connected (tl 0) A)
                         (A-H : H-Structure A a0) where

  P : (Susp A) → Type
  P x = τ₁ (Path {Susp A} No x)

  open H-Structure A-H

  Codes : (Susp A) → Type
  Codes = (Susp-rec A
                    A 
                    (λ a → (ua (_⊙_ a , isequivl a))))

  Codes-level : (x : _) -> NType (tl 1) (Codes x)
  Codes-level = Susp-elim _ A-level A-level (λ _ → HProp-unique (NType-is-HProp _) _ _)

  encode0 : ∀ {x} → (Path No x) -> (Codes x)
  encode0 α = transport (Codes) α a0

  encode : ∀ {x} → P x -> (Codes x)
  encode {x} = Trunc-rec (Codes-level x) encode0 

  decode' : A → (τ₁ (Path{Susp A} No No))
  decode' a = [ (! (mer a0) ∘ mer a) ]

  abstract
    transport-Codes-mer : ∀ a a' → 
      transport Codes (mer a) a' ≃ a ⊙ a'
    transport-Codes-mer a a' = 
      (transport Codes (mer a) a') ≃〈 ap≃ (transport-ap-assoc Codes (mer a)) 〉 
      (coe (ap Codes (mer a)) a') 
        ≃〈 ap (\ x -> coe x a') (Susp-rec/βmer {mer' = (λ a → (ua (_⊙_ a , isequivl a)))})〉 
      coe ((ua (_⊙_ a , isequivl a))) a' ≃〈 ap≃ (type≃β (_⊙_ a , isequivl a)) 〉
      (a ⊙ a') ∎

    transport-Codes-mer-a0-! : ∀ a → 
      transport Codes (! (mer a0)) a ≃ a
    transport-Codes-mer-a0-! a = 
      transport Codes (! (mer a0)) a ≃〈 ap≃ (transport-ap-assoc Codes (! (mer a0))) 〉 
      (coe (ap (Codes) (! (mer a0))) a) 
        ≃〈 ap (λ x → coe x a) (ap-! Codes (mer a0)) 〉 
      (coe (! (ap Codes (mer a0))) a) 
        ≃〈 ap (λ p → coe (! p) a) (Susp-rec/βmer {mer' = (λ a → (ua (_⊙_ a , isequivl a)))})〉
      coe (! ((ua (_⊙_ a0 , isequivl a0)))) a ≃〈 ap (λ x → coe (! x) a) (type≃-ext (ua (_⊙_ a0 , isequivl a0)) id (λ x → unitl x ∘ ap≃ (type≃β (_⊙_ a0 , isequivl a0)))) 〉
      coe (! id) a ≃〈 id 〉
      a ∎

  abstract 
    encode-decode' : (a : A) → encode{No}(decode' a) ≃ a
    encode-decode' a = encode {No} (decode' a) ≃〈 id 〉 
                       encode {No} [ (! (mer a0) ∘ mer a) ] ≃〈 id 〉 
                       transport Codes (! (mer a0) ∘ mer a) a0 ≃〈 ap≃ (transport-∘ Codes (! (mer a0)) (mer a)) 〉 
                       transport Codes (! (mer a0)) (transport Codes (mer a) a0) ≃〈 ap (transport Codes (! (mer a0))) (transport-Codes-mer a a0) 〉 
                       transport Codes (! (mer a0)) (a ⊙ a0) ≃〈 ap (transport Codes (! (mer a0))) (unitr a) 〉 
                       transport Codes (! (mer a0)) a ≃〈 transport-Codes-mer-a0-! a 〉 
                       a ∎

  abstract
    homomorphism : ∀ a a' → 
              Path{Trunc (tl 1) (Path {(Susp A)} No So) }
                   [ mer (a ⊙ a') ] [ (mer a ∘ ! (mer a0) ∘ mer a') ]
    homomorphism = ConnectedProduct.wedge-elim {A = A} {B = A} A-Connected A-Connected
                      (λ a a' → _ , use-level (Trunc-level{tl 1}) _ _)
                      (Inr id) {a0} {a0}
                      (λ a → [ (mer (a0 ⊙ a)) ] ≃〈 ap ([_]) (ap mer (unitl a)) 〉
                             [ (mer a) ] ≃〈 ap ([_]) (! (!-inv-r-front (mer a0) (mer a))) 〉
                             [ (mer a0 ∘ ! (mer a0) ∘ mer a) ] ∎)
                      (λ a →
                           [ (mer (a ⊙ a0)) ] ≃〈 ap ([_]) (ap mer (unitr a)) 〉
                           [ (mer a) ] ≃〈 ap ([_]) (! (!-inv-l-back (mer a) (mer a0))) 〉
                           [ (mer a ∘ ! (mer a0) ∘ mer a0) ] ∎)
                      (ap2 (λ x y → 
                             [ (mer (a0 ⊙ a0)) ] ≃〈 x 〉
                             [ (mer a0) ] ≃〈 y 〉
                             [ (mer a0 ∘ ! (mer a0) ∘ mer a0) ] ∎)
                         (ap (λ x → ap ([_]) (ap mer x)) unitcoh)
                         (coh1 (mer (a0)))) where
      coh1 : ∀ {k A} {a a' : A} (p : a ≃ a')
           -> ap (([_]{k})) (! (!-inv-r-front p p)) ≃ ap (([_]{k})) (! (!-inv-l-back p p))
      coh1 id = id

  decode : ∀ {x} → Codes x → P x 
  decode {x} = Susp-elim (\ x ->  Codes x → P x)
                         decode'
                         (λ a → [ (mer a) ])
                         (λ a → transport-→-from-square Codes P (mer a)
                                      decode' (λ a' → [ (mer a') ]) 
                                      (λ≃ (STS a)))
                         x where
    abstract
     STS : (a a' : A) → transport P (mer a) (decode' a') ≃ [ mer (transport Codes (mer a) a') ]
     STS a a' = transport P (mer a) (decode' a') ≃〈 id 〉
                transport P (mer a) [ (! (mer a0) ∘ mer a') ] ≃〈 transport-Trunc' (\x -> Path No x) (mer a) _ 〉
                [ transport (\ x -> Path No x) (mer a) (! (mer a0) ∘ mer a') ] ≃〈 ap [_] (transport-Path-right (mer a) _) 〉
                [ (mer a) ∘ (! (mer a0) ∘ mer a') ] ≃〈 (! (homomorphism _ _)) 〉
                [ (mer (a ⊙ a')) ] ≃〈 ap ([_] o mer) (! (transport-Codes-mer a a')) 〉 
                [ (mer (transport Codes (mer a) a')) ] ∎


  abstract
    decode-encode : ∀ {x : _} (α : P x) -> decode (encode α) ≃ α
    decode-encode tα = Trunc-elim (\ α -> decode (encode α) ≃ α) (λ x → path-preserves-level Trunc-level) 
                                  (path-induction (λ _ p → decode (encode [ p ]) ≃ [ p ]) 
                                                  (ap [_] (!-inv-l (mer a0))))
                                  tα

  main-lemma-eqv : Equiv (τ₁ (Path{Susp A} No No)) A
  main-lemma-eqv = (improve (hequiv encode decode decode-encode encode-decode'))

  main-lemma : (τ₁ (Path{Susp A} No No)) ≃ A
  main-lemma = ua main-lemma-eqv

  π2Susp : (π (S One) (Susp A) No) ≃ π One A a0 
  π2Susp = (π (S One) (Susp A) No) ≃〈 id 〉
           (τ₀ (Loop (S One) (Susp A) No)) ≃〈 id 〉
           (τ₀ (Loop One (Loop One (Susp A) No) id)) ≃〈 ! (Loop-Trunc0 One) 〉
           (Loop One (τ₁ (Path{(Susp A)} No No)) [ id ]) ≃〈 ap-Loop≃ One main-lemma (ap≃ (type≃β main-lemma-eqv) {[ id ]}) 〉
           (Loop One A a0) ≃〈 ! (UnTrunc.path (tl 0) (Loop One A a0) (use-level A-level _ _)) 〉
           π One A a0 ∎
