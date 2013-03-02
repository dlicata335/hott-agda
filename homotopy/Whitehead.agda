{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open Truncation
open LoopSpace
open Int

module homotopy.Whitehead where

  module LoopEquivToPathEquiv {A B : Type}
                              (f : A → B)
                              (zero : IsEquiv {Trunc (tl 0) A} {Trunc (tl 0) B} (Trunc-func f))
                              (loops : (x : A) → IsEquiv{(Path{A} x x)} {(Path{B} (f x) (f x))} (ap f)) where

    eqv : (x : A) (x' : A) (α : x ≃ x') → IsEquiv{(Path{A} x x')}{(Path{B} (f x) (f x'))} (ap f)
    eqv x .x id  = loops x

    paths' : (x : A) (x' : A) → IsWEq{(Path{A} x x')}{(Path{B} (f x) (f x'))} (ap f)
    paths' x x' β = Trunc-rec (Contractible-is-HProp _)
                             (λ α → coe (! (IsWeq≃IsEquiv (ap f))) (eqv x x' α) β)
                             fact2 where 
      fact1 : Path{Trunc (tl 0) A} ([ x ]) ([ x' ])
      fact1 = IsEquiv.α zero [ x' ] ∘ ap (IsEquiv.g zero) (ap [_] β) ∘ ! (IsEquiv.α zero [ x ])

      fact2 : Trunc -1 (Path x x') 
      fact2 = coe (! (TruncPath.path -1)) fact1

    abstract
      paths : (x : A) (x' : A) → IsEquiv{(Path{A} x x')}{(Path{B} (f x) (f x'))} (ap f)
      paths x x' = coe (IsWeq≃IsEquiv (ap f)) (paths' x x')
  

  module SplitEquiv {A B : Type} 
                    (f : A → B)
                    (zero : IsEquiv {Trunc (tl 0) A} {Trunc (tl 0) B} (Trunc-func f))
                    (one : (x : A) → IsEquiv {(Path{A} x x)} {(Path{B} (f x) (f x))} (ap f))
         where

     one' : (x x' : A) → IsEquiv {(Path{A} x x')} {(Path{B} (f x) (f x'))} (ap f)
     one' = LoopEquivToPathEquiv.paths f zero one

     iseqv' : IsWEq f 
     iseqv' y = gen tx tβ where
       tx : Trunc (tl 0) A 
       tx = IsEquiv.g zero [ y ]

       tβ : Path{Trunc (tl 0) B} (Trunc-func f (IsEquiv.g zero [ y ])) [ y ]
       tβ = IsEquiv.β zero [ y ]

       gen : (x : Trunc (tl 0) A) → Path{Trunc (tl 0) B} (Trunc-func f x) [ y ] 
                -> Contractible (HFiber f y)
       gen = Trunc-elim _ (λ _ → increment-level (Πlevel (λ _ → Contractible-is-HProp _))) 
        (λ x tα →
          Trunc-rec (Contractible-is-HProp _)
          (λ α → (x , α) , 
                 (λ {(x' , α') → pair≃ (IsEquiv.g (one' x x') (! α' ∘ α))
                                       (transport (λ v → Path (f v) y) (IsEquiv.g (one' x x') (! α' ∘ α)) α ≃〈 transport-Path-pre' f (IsEquiv.g (one' x x') (! α' ∘ α)) α 〉 
                                        α ∘ ! (ap f (IsEquiv.g (one' x x') (! α' ∘ α))) ≃〈 ap (λ x0 → α ∘ ! x0) (IsEquiv.β (one' x x') (! α' ∘ α)) 〉 
                                        α ∘ ! (! α' ∘ α) ≃〈 ap (λ x0 → α ∘ x0) (!-∘ (! α') α) 〉 
                                        α ∘ ! α ∘ ! (! α') ≃〈 !-inv-r-front α (! (! α')) 〉 
                                        ! (! α') ≃〈 !-invol α' 〉 
                                        α' ∎)}))
          (coe (! (TruncPath.path -1)) tα))

     iseqv : IsEquiv f 
     iseqv = coe (IsWeq≃IsEquiv f) iseqv'

  module Whitehead-NType where

    whitehead : {A B : Type} (n : Positive) 
                (nA : NType (tlp n) A) (nB : NType (tlp n) B)
                (f : A → B)
                (zero : IsEquiv {Trunc (tl 0) A} {Trunc (tl 0) B} (Trunc-func f))
                (pis  : ∀ k x → IsEquiv{Trunc (tl 0) (Loop k A x)}{Trunc (tl 0) (Loop k B (f x))} (Trunc-func (ap^ k f)))
              -> IsEquiv f
    whitehead One nA nB f zero pis = 
      SplitEquiv.iseqv f zero 
        (λ x →        snd (UnTrunc.eqv (tl 0) _ (use-level nB (f x) (f x))
               ∘equiv (Trunc-func (ap f) , pis One x)
               ∘equiv (!equiv (UnTrunc.eqv (tl 0) _ (use-level nA x x)))))
    whitehead {A}{B} (S n) nA nB f zero pis = SplitEquiv.iseqv f zero (λ x → IH x) where
      IH : (x : A) → IsEquiv {Path x x}{Path (f x) (f x)} (ap f)
      IH x = whitehead n (use-level nA x x) (use-level nB (f x) (f x)) (ap f) 
                       (pis One x)
                       (λ k α → transport IsEquiv (coe-incr-pis k α) (coe-is-equiv (incr-pis k α))) where 

              incr-pis : ∀ k α → (π k (Path {A} x x) α) ≃ (π k (Path {B} (f x) (f x)) (ap f α))
              incr-pis k α = 
                 -- optimized proof-term
                    ap (Trunc (tl 0)) ((! (rebase-Loop-Path k (ap f α))) ∘ (LoopPath.path k))
                  ∘ ua (Trunc-func (ap^ (S k) f) , pis (S k) x)
                  ∘ ap (Trunc (tl 0)) ((! (LoopPath.path {A} {x} k)) ∘ (rebase-Loop-Path k α))
              {- legible version:
                π k (Path {A} x x) α ≃〈 ap (Trunc (tl 0)) (rebase-Loop-Path k α) 〉 
                π k (Path {A} x x) id ≃〈 ap (Trunc (tl 0)) (! (LoopPath.path {A} {x} k)) 〉 
                π (S k) A x ≃〈 ua (Trunc-func (ap^ (S k) f) , pis (S k) x) 〉 
                π (S k) B (f x) ≃〈 ap (Trunc (tl 0)) (LoopPath.path k) 〉 
                π k (Path {B} (f x) (f x)) id ≃〈 ap (Trunc (tl 0)) (! (rebase-Loop-Path k (ap f α))) 〉
                π k (Path {B} (f x) (f x)) (ap f α) ∎ 
              -}

              coe-incr-pis : ∀ k α -> coe (incr-pis k α) ≃ Trunc-func (ap^ k (ap f))
              coe-incr-pis k α = coe (incr-pis k α) ≃〈 rearrange (ap^ (S k) f) (pis (S k) x) (! (rebase-Loop-Path k (ap f α))) (LoopPath.path k) (! (LoopPath.path {A} {x} k)) (rebase-Loop-Path k α)〉 
                                 Trunc-func (  coe (! (rebase-Loop-Path k (ap f α))) 
                                             o coe (LoopPath.path k)
                                             o (ap^ (S k) f) 
                                             o coe (! (LoopPath.path {A} {x} k))
                                             o coe (rebase-Loop-Path k α)) ≃〈 ap Trunc-func STS 〉
                                 Trunc-func (ap^ k (ap f)) ∎ where 
                rearrange : ∀ {A B C C' D E : Type} (f : C → C') (e : IsEquiv (Trunc-func f))
                              (α1 : D ≃ E) (α2 : C' ≃ D) (α3 : B ≃ C) (α4 : A ≃ B) → 
                            coe (ap (Trunc (tl 0)) (α1 ∘ α2)
                                 ∘ ua (Trunc-func f , e)
                                 ∘ ap (Trunc (tl 0)) (α3 ∘ α4))
                            ≃ Trunc-func (coe α1 o coe α2 o f o coe α3 o coe α4)
                rearrange f e id id id id = type≃β (Trunc-func f , e) ∘ ap coe (∘-unit-l (ua (Trunc-func f , e)))
    
                reduce-rebase-Loop-Path :
                          ∀ {x' : A} (α : x ≃ x')
                             (fl : ∀ {x'} (α : x ≃ x') 
                                   → Loop k (Path x x') α 
                                   → Loop k (Path (f x) (f x')) (ap f α))
                           -> Path
                              (coe (! (rebase-Loop-Path k (ap f α))) o
                               fl id o
                               coe (rebase-Loop-Path k α))
                              (fl α) 
                reduce-rebase-Loop-Path id fl = id

                STS : (  coe (! (rebase-Loop-Path k (ap f α))) 
                       o coe (LoopPath.path k)
                       o (ap^ (S k) f) 
                       o coe (! (LoopPath.path {A} {x} k))
                       o coe (rebase-Loop-Path k α))
                      ≃ (ap^ k (ap f))
                STS = coe (! (rebase-Loop-Path k (ap f α))) o
                      coe (LoopPath.path k) o
                      ap^ (S k) f o
                      coe (! (LoopPath.path {A} {x} k)) o
                      coe (rebase-Loop-Path k α) ≃〈 ap2 (λ x' y → coe (! (rebase-Loop-Path k (ap f α))) o x' o ap^ (S k) f o y o coe (rebase-Loop-Path k α)) (type≃β (LoopPath.eqv k)) (type≃β! (LoopPath.eqv k)) 〉 

                      coe (! (rebase-Loop-Path k (ap f α))) o
                      loopSN1 k o ap^ (S k) f o loopN1S k o
                      coe (rebase-Loop-Path k α) ≃〈 ap (λ x' → coe (! (rebase-Loop-Path k (ap f α))) o x' o coe (rebase-Loop-Path k α)) (! (λ≃ (ap^-ap-assoc k f))) 〉 

                      coe (! (rebase-Loop-Path k (ap f α))) o
                      (ap^ k (ap f)) o
                      coe (rebase-Loop-Path k α) ≃〈 reduce-rebase-Loop-Path α (λ {x' : A} (α' : Path x x') (l : Loop k (Id x x') α') → ap^ k (ap f) l) 〉
 
                      (ap^ k (ap f) ∎) 

    -- ENH strengthen to 
    -- (pis  : ∀ k x → k <=tl n → IsEquiv{(π k A x)}{(π k B (f x))} (Trunc-func (ap^ k f)))
    -- by truncation the rest are trivial
