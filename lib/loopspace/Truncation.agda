
{-# OPTIONS --type-in-type --without-K #-}

open import lib.First
open import lib.Paths
open import lib.Functions
open import lib.Nat
open import lib.Int
open import lib.Prods
open import lib.Sums
open Int
open import lib.AdjointEquiv
open import lib.NType
open import lib.Truncations
open Truncation
open import lib.WrappedPath

open import lib.loopspace.Basics
open import lib.loopspace.Groupoid

module lib.loopspace.Truncation where

  abstract 
    -- if you have enough gas
    Loop-level : ∀ n k {A} {a} → NType (tlp (n +pn k)) A → NType (tl k) (Loop n A a)
    Loop-level One k {A = A} p = use-level (transport (λ x → NType x A) (tlp+1 k) p) _ _
    Loop-level (S n) k {A} p = use-level (Loop-level n (S k) (transport (λ x → NType (tlp x) A) (! (+pn-rh-S n k)) p)) _ _

    -- if you run out of gas
    Loop-level-S : ∀ k {A} {a} → NType (tlp k) A → NType -2 (Loop (S k) A a)
    Loop-level-S One nA' = ntype (id , (λ _ → HSet-UIP (use-level nA' _ _) _ _ _ _))
    Loop-level-S (S n') nA' = transport (NType -2) (! (LoopPath.path (S n'))) (Loop-level-S n' (use-level nA' _ _))

    {-# NO_TERMINATION_CHECK #-}
    -- FIXME: doesn't work in 2.4.1 without-K 
    Loop-level-> : ∀ n k {A} {a} → NType n A → n <tl (tlp k) → NType -2 (Loop k A a)
    Loop-level-> .(S (S -2)) One {A} {a} nA (ltS {.(S (S -2))}) = ntype (id , (λ y → HSet-UIP nA _ _ _ _))
    Loop-level-> .(S -2) One nA (ltSR ltS) = use-level nA _ _
    Loop-level-> .-2 One nA (ltSR (ltSR ltS)) = path-preserves-level nA
    Loop-level-> n One nA (ltSR (ltSR (ltSR ())))
    Loop-level-> n (S k) {A} {a} nA lt with lt-unS-right lt
    ... | Inl lt' = path-preserves-level (Loop-level-> n k nA lt')
    ... | Inr eq = Loop-level-S k (transport (λ x → NType x A) eq nA) 
  
    NType-LoopOver : ∀ n k {A} {a} (α : Loop n A a) {B} {b} → ((x : A) → NType (S k) (B x)) → NType k (LoopOver n α B b)
    NType-LoopOver One k α p = use-level (p _) _ _
    NType-LoopOver (S n) k α{B}{b} p = use-level{S k} (NType-LoopOver n (S k) _ (λ x → increment-level (p x))) _ _ 
  
    HSet-Loop : ∀ n {A} {a} → NType (tlp n) A → HSet (Loop n A a)
    HSet-Loop n {A} i = Loop-level n Z (transport (\ n -> NType (tlp n) A) (! (+pn-rh-Z n)) i)
     
    Loop-preserves-level : ∀ n k {A a} -> NType k A → NType k (Loop n A a)
    Loop-preserves-level One k tA = path-preserves-level tA
    Loop-preserves-level (S n) k tA = path-preserves-level (Loop-preserves-level n k tA)

  mutual
    Loop-Trunc : ∀ (n : Positive) (k : Nat) {A} {a} → Loop n (Trunc (tlp (n +pn k)) A) [ a ] ≃ Trunc (tl k) (Loop n A a)
    Loop-Trunc One k {A} {a} = ! (TruncPath.path (tl k)) ∘ ap-Loop-Trunc-tlevel≃ One (tlp+1 k)
    Loop-Trunc (S n) k {A} {a} = ! (TruncPath.path (tl k)) ∘ ap-Loop≃ One (Loop-Trunc n (S k)) (Loop-Trunc-id n (S k)) ∘ ap-Loop-Trunc-tlevel≃ (S n) (! (ap tlp (+pn-rh-S n k)))

    Loop-Trunc-id : ∀ n k {A a} → coe (Loop-Trunc n k {A} {a}) (id^ n) ≃ [ id^ n ]
    Loop-Trunc-id One k = (ap≃ (type≃β! (TruncPath.eqv _)) {id} ∘ ap (transport (λ X → X) (! (TruncPath.path (tl k)))) (ap-Loop-Trunc-tlevel≃-id One (tlp+1 k))) ∘ ap≃ (transport-∘ (λ X → X) (! (TruncPath.path (tl k))) (ap-Loop-Trunc-tlevel≃ One (tlp+1 k)))
    Loop-Trunc-id (S n) k = (ap≃ (type≃β! (TruncPath.eqv _)) {id} ∘ ap (transport (λ X → X) (! (TruncPath.path (tl k)))) (ap-Loop≃-id One (Loop-Trunc n (S k)) (Loop-Trunc-id n (S k))) ∘ ap (transport (λ X → X) (! (TruncPath.path (tl k))) o transport (λ X → X) (ap-Loop≃ One (Loop-Trunc n (S k)) (Loop-Trunc-id n (S k)))) (ap-Loop-Trunc-tlevel≃-id (S n) (! (ap tlp (+pn-rh-S n k))))) ∘ ap≃ (transport-∘3 (λ X → X) (! (TruncPath.path (tl k))) (ap-Loop≃ One (Loop-Trunc n (S k)) (Loop-Trunc-id n (S k))) (ap-Loop-Trunc-tlevel≃ (S n) (! (ap tlp (+pn-rh-S n k)))))

  Loop-Trunc0 : ∀ n {A} {a} → Loop n (Trunc (tlp n) A) [ a ] ≃ π n A a
  Loop-Trunc0 n = Loop-Trunc n 0 ∘ ap-Loop-Trunc-tlevel≃ n (! (ap tlp (+pn-rh-Z n)))

  π<=Trunc : ∀ k n (lt : tlp k <=tl tlp n) {A} (a0 : A) 
             -> π k (Trunc (tlp n) A) [ a0 ] ≃ π k A a0
  π<=Trunc k n lt {A} a0 with <=-to-+{k}{n} lt 
  ... | (m , eq) =  π k (Trunc (tlp n) A) [ a0 ] ≃〈 id 〉 
                    τ₀ (Loop k (Trunc (tlp n) A) [ a0 ]) ≃〈 ap τ₀ (ap-Loop-Trunc-tlevel≃ k (! eq)) 〉 
                    τ₀ (Loop k (Trunc (tlp (k +pn m)) A) [ a0 ]) ≃〈 ap τ₀ (Loop-Trunc k m) 〉 
                    τ₀ (Trunc (tl m) (Loop k A  a0))             ≃〈 FuseTrunc.path (tl 0) (tl m) (Loop k A a0) 〉 
                    (Trunc (mintl (tl 0) (tl m)) (Loop k A  a0)) ≃〈 ap (λ x → Trunc x (Loop k A a0)) (min0nat m) 〉 
                    (π k A a0) ∎

  



  abstract
    {-# NO_TERMINATION_CHECK #-}
    -- FIXME: doesn't work in 2.4.1 without-K 
    HProp-Loop-in-Trunc< : ∀ k n {A t} → k <tl (tlp n) → HProp (Loop n (Trunc k A) t)
    HProp-Loop-in-Trunc< -2 One lt = increment-level (path-preserves-level Trunc-level)
    HProp-Loop-in-Trunc< -2 (S n) lt = increment-level (path-preserves-level (Loop-preserves-level n -2 (Trunc-level { -2})))
    HProp-Loop-in-Trunc< (S .(S -2)) One ltS = use-level (Trunc-level {S (S -2)}) _ _
    HProp-Loop-in-Trunc< (S .-2) One {A} {t} (ltSR ltS) = path-preserves-level Trunc-level
    HProp-Loop-in-Trunc< (S k) One (ltSR (ltSR (ltSR ()))) 
    HProp-Loop-in-Trunc< (S k) (S n) {A}{t} lt with lt-unS-right lt 
    ... | Inl lt' = path-preserves-level (HProp-Loop-in-Trunc< (S k) n lt')
    ... | Inr eq = let eq = ! eq in 
                   use-level
                     (coe
                      (ap (NType (S (S -2))) 
                        (ap-Loop≃ n (ap (λ n' → Trunc n' A) eq)
                          (ap≃ (transport-inv-2 (λ n' → Trunc n' A) eq) {t} 
                           ∘ ! (ap≃ (transport-ap-assoc (λ n' → Trunc n' A) eq)
                            {transport (λ x → Trunc x A) (! eq) t}))))
                      (HSet-Loop n {_} {transport (λ x → Trunc x A) (! eq) t}
                       (Trunc-level {tlp n} {A})))
                     _ _ 
