
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

  private
    Two = One +1

  B2 = Trunc (tlp Two) (Susp A)

  base2 : B2
  base2 = [ No ]

  P : B2 → Type
  P x = τ₁ (Path {B2} base2 x)

  open H-Structure A-H

  Codes : B2 → NTypes (tlp One)
  Codes = Trunc-rec (NTypes-level (tlp One))
                    (Susp-rec (A , A-level) 
                              (A , A-level)
                              (λ a → coe (ΣSubsetPath (λ _ → (NType-is-HProp _)))
                                         (ua (_⊙_ a , isequivl a)))) 

  encode0 : ∀ {x} → (Path {B2} base2 x) -> fst (Codes x)
  encode0 α = transport (fst o Codes) α a0

  encode : ∀ {x} → P x -> fst (Codes x)
  encode {x} = Trunc-rec (snd (Codes x)) encode0 

  decode' : A → (τ₁ (Path{B2} base2 base2))
  decode' a = [ ap [_] (! (mer a0) ∘ mer a) ]

  transport-Codes-mer : ∀ a a' → 
    (transport (\ z -> fst (Codes [ z ]))) (mer a) a' ≃ a ⊙ a'
  transport-Codes-mer a a' = 
    (transport (\ z -> fst (Codes [ z ])) (mer a) a') ≃〈 ap≃ (transport-ap-assoc (λ z → fst (Codes [ z ])) (mer a)) 〉 
    (coe (ap (λ z → fst (Codes [ z ])) (mer a)) a') 
      ≃〈 (ap (\ x -> coe x a') (ap-o fst (Codes o [_]) (mer a))) 〉 
    (coe (fst≃ (ap (Codes o [_]) (mer a))) a') 
      ≃〈 ap (λ p → coe (fst≃ p) a') Susp-rec/βmer 〉 
    coe
      (fst≃ (coe (ΣSubsetPath NType-is-HProp) (ua (_⊙_ a , isequivl a))))
      a' ≃〈 ap (λ x → coe x a') (ΣSubsetPathβ NType-is-HProp (ua (_⊙_ a , isequivl a))) 〉
    coe ((ua (_⊙_ a , isequivl a))) a' ≃〈 ap≃ (type≃β (_⊙_ a , isequivl a)) 〉
    (a ⊙ a') ∎

  transport-Codes-mer-a0-! : ∀ a → 
    transport (fst o Codes o [_]) (! (mer a0)) a ≃ a
  transport-Codes-mer-a0-! a = 
    transport (\ z -> fst (Codes [ z ])) (! (mer a0)) a ≃〈 ap≃ (transport-ap-assoc (λ z → fst (Codes [ z ])) (! (mer a0))) 〉 
    (coe (ap (λ z → fst (Codes [ z ])) (! (mer a0))) a) 
      ≃〈 (ap (\ x -> coe x a) (ap-o fst (Codes o [_]) (! (mer a0)))) 〉 
    (coe (fst≃ (ap (Codes o [_]) (! (mer a0)))) a) 
      ≃〈 ap (λ x → coe (fst≃ x) a) (ap-! (Codes o [_]) (mer a0)) 〉 
    (coe (fst≃ (! (ap (Codes o [_]) (mer a0)))) a) 
      ≃〈 ap (λ x → coe x a) (ap-! fst (ap (Codes o [_]) (mer a0))) 〉 
    (coe (! (fst≃ (ap (Codes o [_]) (mer a0)))) a) 
      ≃〈 ap (λ p → coe (! (fst≃ p)) a) Susp-rec/βmer 〉
    coe
      (! (fst≃ (coe (ΣSubsetPath NType-is-HProp) (ua (_⊙_ a0 , isequivl a0)))))
      a ≃〈 ap (λ x → coe (! x) a) (ΣSubsetPathβ NType-is-HProp (ua (_⊙_ a0 , isequivl a0))) 〉
    coe (! ((ua (_⊙_ a0 , isequivl a0)))) a ≃〈 ap (λ x → coe (! x) a) (type≃-ext (ua (_⊙_ a0 , isequivl a0)) id (λ x → unitl x ∘ ap≃ (type≃β (_⊙_ a0 , isequivl a0)))) 〉
    coe (! id) a ≃〈 id 〉
    a ∎

  abstract 
    encode-decode' : (a : A) → encode{base2}(decode' a) ≃ a
    encode-decode' a = encode {base2} (decode' a) ≃〈 id 〉 
                       encode {base2} [ ap [_] (! (mer a0) ∘ mer a) ] ≃〈 id 〉 
                       transport (fst o Codes) (ap [_] (! (mer a0) ∘ mer a)) a0 ≃〈 ! (ap≃ (transport-ap-assoc' (fst o Codes) [_] (! (mer a0) ∘ mer a))) 〉 
                       transport (fst o Codes o [_]) (! (mer a0) ∘ mer a) a0 ≃〈 ap≃ (transport-∘ (fst o Codes o [_]) (! (mer a0)) (mer a)) 〉 
                       transport (fst o Codes o [_]) (! (mer a0))
                         (transport (fst o Codes o [_]) (mer a) a0) ≃〈 ap (transport (fst o Codes o [_]) (! (mer a0))) (transport-Codes-mer a a0) 〉 
                       transport (fst o Codes o [_]) (! (mer a0)) (a ⊙ a0) ≃〈 ap (transport (fst o Codes o [_]) (! (mer a0))) (unitr a) 〉 
                       transport (fst o Codes o [_]) (! (mer a0)) a ≃〈 transport-Codes-mer-a0-! a 〉 
                       a ∎

  homomorphism : ∀ a a' → 
            Path{(Path {Trunc (tl 2) (Susp A)} [ No ] [ So ]) }
                 (ap [_] (mer (a ⊙ a'))) (ap [_] (mer a ∘ ! (mer a0) ∘ mer a'))
  homomorphism = ConnectedProduct.wedge-elim {A = A} {B = A} A-Connected A-Connected
                    (λ a a' →
                       Path {Path {Trunc (tl 2) (Susp A)} [ No ] [ So ]}
                       (ap [_] (mer (a ⊙ a'))) (ap [_] (mer a ∘ ! (mer a0) ∘ mer a'))
                       , use-level (use-level (Trunc-level {tl 2}) _ _) _ _)
                    (Inr id) {a0} {a0}
                    (λ a → ap [_] (mer (a0 ⊙ a)) ≃〈 ap (ap [_]) (ap mer (unitl a)) 〉
                           ap [_] (mer a) ≃〈 ap (ap [_]) (! (!-inv-r-front (mer a0) (mer a))) 〉
                           ap [_] (mer a0 ∘ ! (mer a0) ∘ mer a) ∎)
                    (λ a →
                         ap [_] (mer (a ⊙ a0)) ≃〈 ap (ap [_]) (ap mer (unitr a)) 〉
                         ap [_] (mer a) ≃〈 ap (ap [_]) (! (!-inv-l-back (mer a) (mer a0))) 〉
                         (ap [_] (mer a ∘ ! (mer a0) ∘ mer a0) ∎))
                    (ap2 (λ x y → 
                           ap [_] (mer (a0 ⊙ a0)) ≃〈 x 〉
                           ap [_] (mer a0) ≃〈 y 〉
                           ap [_] (mer a0 ∘ ! (mer a0) ∘ mer a0) ∎)
                       (ap (λ x → ap (ap [_]) (ap mer x)) unitcoh)
                       (coh1 (mer (a0)))) where
    coh1 : ∀ {k A} {a a' : A} (p : a ≃ a')
         -> ap (ap ([_]{k})) (! (!-inv-r-front p p)) ≃ ap (ap ([_]{k})) (! (!-inv-l-back p p))
    coh1 id = id

  decode : ∀ {x} → fst (Codes x) → P x 
  decode {x} = Trunc-elim (λ x' → fst (Codes x') → P x') (λ _ → Πlevel (λ _ → increment-level Trunc-level)) 
                          (Susp-elim _ 
                                     decode'
                                     (λ a → [ ap [_] (mer a) ])
                                     (λ a → transport-→-from-square (fst o Codes o [_]) (P o [_]) (mer a)
                                              decode' (λ a' → [ ap [_] (mer a') ]) 
                                              (λ≃ (STS a))))
                          x where
    abstract
     STS : (a a' : A) → 
              transport (\ z -> P [ z ]) (mer a) (decode' a') ≃
              [ ap [_] (mer ((transport (\ z -> fst (Codes [ z ]))) (mer a) a')) ]
     STS a a' = transport (\ z -> P [ z ]) (mer a) (decode' a') ≃〈 id 〉
                transport (\ z -> P [ z ]) (mer a) [ ap [_] (! (mer a0) ∘ mer a') ] ≃〈 transport-Trunc' (λ x' → Path base2 [ x' ]) (mer a) _ 〉
                [ transport (\ x -> Path base2 [ x ]) (mer a) (ap [_] (! (mer a0) ∘ mer a')) ] ≃〈 ap [_] (transport-Path-post' [_] (mer a) _) 〉
                [ ap [_] (mer a) ∘ ap [_] (! (mer a0) ∘ mer a') ] ≃〈 ap [_] (! (ap-∘ [_] (mer a) (! (mer a0) ∘ mer a'))) 〉
                [ ap [_] (mer a ∘ ! (mer a0) ∘ mer a') ] ≃〈 ap [_] (! (homomorphism _ _)) 〉
                [ ap [_] (mer (a ⊙ a')) ] ≃〈 ap ([_] o ap [_] o mer) (! (transport-Codes-mer a a')) 〉 
                [ ap [_] (mer ((transport (\ z -> fst (Codes [ z ]))) (mer a) a')) ] ∎


  abstract
    decode-encode : ∀ {x : _} (α : P x) -> decode (encode α) ≃ α
    decode-encode tα = Trunc-elim (\ α -> decode (encode α) ≃ α) (λ x → path-preserves-level Trunc-level) 
                                  (path-induction (λ _ p → decode (encode [ p ]) ≃ [ p ]) 
                                                  (ap ([_] o ap [_]) (!-inv-l (mer a0))))
                                  tα

  main-lemma-eqv : Equiv (τ₁ (Path{B2} base2 base2)) A
  main-lemma-eqv = (improve (hequiv encode decode decode-encode encode-decode'))

  main-lemma : (τ₁ (Path{B2} base2 base2)) ≃ A
  main-lemma = ua main-lemma-eqv

  path : (π Two B2 base2) ≃ π One A a0 
  path = (π Two B2 base2) ≃〈 id 〉
         (τ₀ (Loop Two B2 base2)) ≃〈 id 〉
         (τ₀ (Loop One (Loop One B2 base2) id)) ≃〈 ! (Loop-Trunc0 One) 〉
         (Loop One (τ₁ (Path{B2} base2 base2)) [ id ]) ≃〈 ap-Loop≃ One main-lemma (ap≃ (type≃β main-lemma-eqv) {[ id ]}) 〉
         (Loop One A a0) ≃〈 ! (UnTrunc.path (tl 0) (Loop One A a0) (use-level A-level _ _)) 〉
         π One A a0 ∎
