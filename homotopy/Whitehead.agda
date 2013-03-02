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

    paths : (x : A) (x' : A) → IsWEq{(Path{A} x x')}{(Path{B} (f x) (f x'))} (ap f)
    paths x x' β = Trunc-rec (Contractible-is-HProp _)
                             (λ α → coe (! (IsWeq≃IsEquiv (ap f))) (eqv x x' α) β)
                             fact2 where 
      fact1 : Path{Trunc (tl 0) A} ([ x ]) ([ x' ])
      fact1 = IsEquiv.α zero [ x' ] ∘ ap (IsEquiv.g zero) (ap [_] β) ∘ ! (IsEquiv.α zero [ x ])

      fact2 : Trunc -1 (Path x x') 
      fact2 = coe (! (TruncPath.path -1)) fact1
  

  module Split {A B : Type} 
               (f : A → B)
               (zero : IsEquiv {Trunc (tl 0) A} {Trunc (tl 0) B} (Trunc-func f))
               (one' : (x x' : A) → IsEquiv {(Path{A} x x')} {(Path{B} (f x) (f x'))} (ap f))
         where

     eqv : IsWEq f 
     eqv y = gen tx tβ where
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
  
  module One {A B : Type} 
             (nA : NType (tl 1) A)
             (nB : NType (tl 1) B)
             (f : A → B)
             (zero : IsEquiv {Trunc (tl 0) A} {Trunc (tl 0) B} (Trunc-func f))
             -- (one  : (x : A) → IsEquiv {π One A x} {π One B (f x)} (Trunc-func (ap f)))
             (one' : (x x' : A) → IsEquiv {Trunc (tl 0) (Path{A} x x')} {Trunc (tl 0) (Path{B} (f x) (f x'))} (Trunc-func (ap f)))
         where

     eqv : IsWEq f 
     eqv y = Trunc-rec (Contractible-is-HProp _)
                       (λ p → (fst p , fst (snd p)) , (λ xα' → pair≃ (fst (snd (snd p) (fst xα') (snd xα'))) (snd (snd (snd p) (fst xα') (snd xα')))))
                       (together' tx tβ) where
       tx : Trunc (tl 0) A 
       tx = IsEquiv.g zero [ y ]

       tβ : Path{Trunc (tl 0) B} (Trunc-func f (IsEquiv.g zero [ y ])) [ y ]
       tβ = IsEquiv.β zero [ y ]

       one'' : ∀ x x' → Equiv (Path x x') (Path (f x) (f x'))
       one'' x x' = UnTrunc.eqv (tl 0) _ (use-level nB _ _) ∘equiv (_ , (one' x x')) ∘equiv !equiv (UnTrunc.eqv (tl 0) _ (use-level nA _ _))

       together' : (x : Trunc (tl 0) A) → Path{Trunc (tl 0) B} (Trunc-func f x) [ y ] 
                -> Trunc -1 (Σ \ (x : A) → 
                             Σ (\ (α : (Path (f x) y)) → 
                             ((x' : A) → (α' : Path (f x') y)
                              → (Σ \ (β : (Path x x')) 
                              → transport (λ x0 → Path (f x0) y) β α ≃ α'))))
       together' = Trunc-elim _ (λ _ → Πlevel (λ _ → increment-level Trunc-level)) -- (\ _ -> Πlevel (\ _ -> (increment-level (Contractible-is-HProp _)) ))
                                (λ x α → Trunc-rec Trunc-level
                                                   (λ α → [ x , α , (λ x' α' → IsEquiv.g (snd (one'' x x')) (! α' ∘ α) , ({!!} ∘ ap (λ x0 → α ∘ ! x0) (IsEquiv.β (snd (one'' x x')) (! α' ∘ α))) ∘ transport-Path-pre' f (IsEquiv.g (snd (one'' x x')) (! α' ∘ α)) α) ])
                                                   (coe (! (TruncPath.path -1)) α))
