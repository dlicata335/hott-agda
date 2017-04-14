{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open import mso.Signatures
open import mso.Formulas
open import mso.ClosedTruth
open import mso.opentruth
open import mso.treedecomp

open ListM
open Index

module mso.NewOuterLemmas where

  postulate
    fixed2fixed1 : ∀ (A1 A2 : Subset) → fixed A1 A2 → fixed1 A1 --when you have a bag (fixed) that's in 2 subsets, it's in the other one. i.e. fixed -> fixed1
    fixed2fixed2 : ∀ (A1 A2 : Subset) → fixed A1 A2 → fixed1 A2 -- fixed - fixed1 (part 2)
    fixed2union : ∀ (A1 A2 : Subset) → fixed A1 A2 → fixed1 (union A1 A2) -- if you have a decidable subset that's in both A1 and A2, then it's in A1 union A2
    fixed1Sub : ∀ (A1 A2 : Subset) → fixed1 A1 → Sub A1 A2 → fixed1 A2 --if you have X = fixed1 A for any set A, X =fixed1 A' for any superset A' of A
  postulate
    decSingleton : ∀ {τ} → (x : Individ τ) → DecidableSub (singleton {τ = τ} x) --a singleton set is always decidable
    individSinSubset : ∀ {τ} (A : Subset) → ( x : IndividS A τ) → Sub (singleton {τ = τ} (fst x)) A --if x is an IndividS A for some subset A, then it's in A!!


  combineJoin : ∀ {Σ} {oc} (B1 B2 : Subset) (A : Structure oc Σ)  (φ : Formula Σ)  → (decb1 : DecidableSub B1) (decb2 : DecidableSub B2) (X : fixed B1 B2)
                    (b1subAset : Sub B1 (fst A)) (b2subAset : Sub B2 (fst A)) →
                               (recurcall1 : (provesR (restriction A B1 decb1 b1subAset) φ (fixed2fixed1 B1 B2 X)))
                               (recurcall2 : (provesR (restriction A B2 decb2 b2subAset) φ (fixed2fixed2 B1 B2 X)))
                               →  Either (Either ((restriction A (union B1 B2) (unionDec {S1 = B1} {B2} decb1 decb2) --uniondec bc we need to show B1UB2 is decidable for restriction
                                                               (subLUB b1subAset b2subAset)) ⊩o φ) --need to show B1UB2 ⊂ A for restriction
                                                 ((restriction A (union B1 B2) (unionDec {S1 = B1} {B2} decb1 decb2)
                                                               (subLUB b1subAset b2subAset)) ⊩o φ false))
                                         (provesR (restriction A (union B1 B2) (unionDec {S1 = B1} {B2} decb1 decb2)
                                                  (subLUB b1subAset b2subAset)) φ (fixed2union B1 B2 X)) --subLUB to show B1UB2 ⊂ fst A, fixed2union to say that X is a bag of this union
  combineJoin B1 B2 A φ decb1 decb2 X b1subAset b2subAset recurcall1 recurcall2 = {!!}

  combineIntro : ∀ {Σ} {τ} (B : Subset) (A : Structure Closed Σ) (φ : Formula Σ) (x : IndividS (fst A) τ)
                                        (xnew : (Sub (singleton {τ = τ} (fst x)) (complement B))) --x is not in B, the overall bag so far
                                        (decb : DecidableSub B) (bsubAset : Sub B (fst A)) (X : fixed1 B) → --B is decidable and a subset of universe of A
                                        (recurcall : provesR (restriction A B decb bsubAset) φ X) → --result of recursive call from intro
                                        (nai : provesR (restriction A (union (fst X) (singleton {τ = τ} (fst x))) --result of naive algorithm on A[X∪x] , φ
                                                                    (unionDec {S1 = (fst X)} {singleton (fst x)} (snd (snd X)) (decSingleton (fst x)))
                                                                     (subLUB (subtrans (fst (snd X)) bsubAset) (individSinSubset (fst A) x))) --this was all the restriction
                                                       φ ((fst X) , (subINL , (snd (snd X))))) --formula and bag
                       → Either (Either ((restriction A (union B (singleton {τ = τ} (fst x))) --restriction subset
                                                      (unionDec {S1 = B} {singleton (fst x)} decb (decSingleton (fst x))) --that subset is dec
                                                        (subLUB bsubAset (individSinSubset (fst A) x))) ⊩o φ) -- that subset is subset of universe
                                        ((restriction A (union B (singleton {τ = τ} (fst x)))
                                                      (unionDec {S1 = B} {singleton (fst x)} decb (decSingleton (fst x)))
                                                        (subLUB bsubAset (individSinSubset (fst A) x))) ⊩o φ false))
                                (provesR (restriction A (union B (singleton {τ = τ} (fst x)))
                                                     (unionDec {S1 = B} {singleton (fst x)} decb (decSingleton (fst x))) --restriction subset is decidable
                                                       (subLUB bsubAset (individSinSubset (fst A) x)))
                                                       φ ((fst X) , ((subtrans (fst (snd X)) subINL) , (snd (snd X))))) --formula and bag
  combineIntro  = {!!}

  combineForget : ∀ {Σ} {τ} (B : Subset) (A : Structure Closed Σ)  (φ : Formula Σ) (X : fixed1 B)
                               (x : IndividS (fst X) τ) (decB : DecidableSub B) (bsubAset : Sub B (fst A))
                                  (xgone : (Sub (singleton {τ = τ} (fst x))) (complement (fst X))) →
                                         (recurcall :   (provesR (restriction A B decB bsubAset) φ X ))
                    → (provesR (restriction A B decB bsubAset) φ X )
  combineForget = {!!}


  algorithm : ∀ {Σ} (B : Subset) (X : fixed1 B) (A : Structure Closed Σ) (φ : Formula Σ) (BinA : Sub B (fst A))
                         → (TD : TreeDecomp {Σ = Σ} {A} (fst X) B)
                           → Either (Either (A ⊩o φ) (A ⊩o φ false)) (provesR A φ (fixed1Sub B (fst A) X BinA))
  algorithm = {!!}

  openToClosed : ∀ {Σ} → (A : Structure Closed Σ) (φ : Formula Σ) → (otruth : A ⊩o φ) → A ⊩c φ --EMC -> MC i.e. Lemma 11
  openToClosed = {!!}

  provesRtoClosed :  ∀ {Σ} → (A : Structure Closed Σ) (φ : Formula Σ) (X : fixed1 (fst A)) → (red : provesR A φ X ) → A ⊩c φ --reducedEMC -> MC i.e. Lemma 13
  provesRtoClosed = {!!}
