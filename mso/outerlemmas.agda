{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude
open import mso.Signatures
open import mso.Formulas
open import mso.ClosedTruth
open import mso.opentruth
open import mso.treedecomp

open ListM
open Index

module mso.outerlemmas where

--tried to make a lemma where you can get whether a structureS is open/closed
  openOrClosedhelp : ∀ {oc A Σ} →  StructureS oc A Σ → OC
  openOrClosedhelp strucS = {!!}

--gets rid of all extensions of signature that had nils in them
  postulate
    nonils : (Σ : Signature) → Signature
{-
--truncating structure?
  truncstruc : ∀ {oc A Σ} → (struc : StructureS oc A Σ) → Either (StructureS Closed A Σ) (StructureS Closed A (truncsig Σ))
  truncstruc [] = Inl []
  truncstruc (struc ,is x) = Inl (struc ,is x)
  truncstruc (struc ,none) = Inr {!struc!}
  truncstruc (struc ,rs x) = {!!}

--you can close a structureS
  closurehelp : ∀ {oc Σ A} → (ostrucS :  StructureS oc A Σ) →  (StructureS Closed A (nonils Σ))
  closurehelp  [] = {![]!}
  closurehelp (ostrucS ,is x) = {!!}
  closurehelp (ostrucS ,none) = {!!}
  closurehelp (ostrucS ,rs x) = {!!}
  closurehelp Σ
  closurehelp Σ (ostrucS ,is x) =  {!!} -- (closurehelp ostrucS) ,is x
  closurehelp Σ (ostrucS ,none) = {!!}
  closurehelp Σ (ostrucS ,rs xs) =  {!!} --(closurehelp ostrucS) ,rs xs -}

--you can close a structure
  {-closure : ∀ {oc Σ} → (ostruc :  Structure oc Σ) → Structure Closed (nonils Σ)
  closure ostruc = fst ostruc , {!closurehelp (snd ostruc)!}

  getOnClosed : -}

--open truth implies closed truth

  openToClosed : ∀ {Σ} → (struc : Structure Closed Σ) (φ : Formula Σ) → (otruth : struc ⊩o φ) → struc ⊩c φ
  openToClosed (SetA , StrucA) (∀i τ φ) (fst , snd) a = openToClosed (SetA , StrucA ,is a) φ (fst a)
  openToClosed (SetA , StrucA) (∃i τ φ) otruth = {!!}
  openToClosed (SetA , StrucA) (∀p τ φ) otruth P = {!!}
  openToClosed (SetA , StrucA) (∃p τ φ) (fst , snd) = fst , (openToClosed (SetA , StrucA ,rs fst) φ snd) --does this get smaller?
  openToClosed (SetA , StrucA) (φ1 ∧ φ2) (fst , snd) = (openToClosed (SetA , StrucA) φ1 fst) , (openToClosed (SetA , StrucA) φ2 snd)
  openToClosed (SetA , StrucA) (φ1 ∨ φ2) (Inl x) = Inl (openToClosed (SetA , StrucA) φ1 x)
  openToClosed (SetA , StrucA) (φ1 ∨ φ2) (Inr x) = Inr (openToClosed (SetA , StrucA) φ2 x)
  openToClosed (SetA , StrucA) ⊤ otruth = otruth
  openToClosed (SetA , StrucA) ⊥ otruth = otruth
  openToClosed (SetA , StrucA) (R x x₁) (fst , snd) = {!!}
  openToClosed (SetA , StrucA) (¬R x x₁) otruth x₂ = {!!}

--jk dnt care
-- A proves φ reduced -> A proves φ undecided
 {- redToUndec : ∀ { Σ} (A : Structure Open Σ) (φ : Formula Σ) → (game : A ⊩s φ )→ (X : fixed1 (fst A))
               → (red : isReduced A φ game X) → isUndecided A φ game
  redToUndec A (∀i τ φ) game X red = {!!} , {!!}
  redToUndec A (∃i τ φ) game X red = {!!}
  redToUndec A (∀p τ φ) game X red = {!!}
  redToUndec A (∃p τ φ) game X red = {!!}
  redToUndec A (φ ∧ φ₁) game X red = {!!}
  redToUndec A (φ ∨ φ₁) game X red = {!!}
  redToUndec A ⊤ game X red = {!!}
  redToUndec A ⊥ game X red = {!!}
  redToUndec A (R x x₁) game X red = {!!}
  redToUndec A (¬R x x₁) game X red = {!!} -}


--try to prove red -> closed truth


--closure of A proves φ undec -> Either cl(A) proves φ true (open?) or A proves φ false (??)

--JOIN INTRODUCE FORGET

  algorithm : ∀ {Σ} {oc} {X B : Subset} (TD: Treedecomp X B) (A : Structure oc Σ) (φ : Formula Σ)
              → Either (Either (A ⊩o φ) (A ⊩o φ false)) (provesR A φ X)
  algorithm TD A φ = ? {-
  algorithm Intro X ∪ x B ∪ x = combineIntro(algorithm(TD X B, A[B], φ), naive(φ, A[X∪x], X∪x))
  algorithm Join X B1∪B2 = combineJoin(algorithm(TD X B1, A[B1], φ), algorithm(TD X B2, A[B2], φ))
  algorithm Forget X\x B = combineForget(algorithm(TD X B, A[B], φ), naive(φ, A[X], X))
  algorithm Empty empty empty = naive(φ, A[empty], empty)
-}

  combineIntro : ∀ {Σ} {oc} (Aset B X : Subset) (Astruc : StructureS oc Aset Σ)  (φ : Formula Σ) (x : IndividS A τ) (xnew : x ∉ B) (pf : Aset == union( B x) ) →
    (recurcall: → provesR (A, Asttuc)[B] X φ)) → (nai : provesR  φ ((Aset, Astruc)[X∪x] X∪x))
    →  Either (Either ((Aset, Astruc) ⊩o φ) ((Aset, Astruc) ⊩o φ false)) (provesR (Aset, Astruc)[B∪x] φ X)

 combineForget : ∀ {Σ} {oc} (A  B X X' : Subset) (Astruc : StructureS oc A Σ)  (φ : Formula Σ) (x : IndividS X τ) (xgone : x ∉ X') →
    (recurcall: →  (provesR (Aset, Astruc)[B] X)) →  (provesR (A, Astruc)[B] φ X') --look

 combineJoin : ∀ {Σ} {oc} (Aset B1 B2 X : Subset) (Astruc : StructureS oc Aset Σ)  (φ : Formula Σ) (pf : Aset == union(B1 B2) ) →
    (recurcall1: → Either (Either ((Aset, Astruc)[B1] ⊩o φ) ((Aset, Astruc)[B1] ⊩o φ false)) (provesR (Aset, Astruc)[B1] φ X))
  (recurcall2: → Either (Either ((Aset, Astruc)[B2] ⊩o φ) ((Aset, Astruc)[B2] ⊩o φ false)) (provesR (Aset, Astruc)[B2] φ X))
    →  Either (Either ((Aset, Astruc) ⊩o φ) ((Aset, Astruc) ⊩o φ false)) (provesR (Aset, Astruc) φ X)

  provesRtoOpen : ∀ (stuff) (provesR A φ X) → A ⊩o φ

  --provesRto to a proves closed

 combineJoin : just take the proveSR part
 combineJoin : ∀ {Σ} {oc} (Aset B1 B2 X : Subset) (Astruc : StructureS oc Aset Σ)  (φ : Formula Σ) →
    (recurcall1: → (provesR (Aset, Astruc)[B1] φ X))
  (recurcall2: → (provesR (Aset, Astruc)[B2] φ X))
    →  Either (Either ((Aset, Astruc)[B1 ∪ B2] ⊩o φ) ((Aset, Astruc)[B1 ∪ B2] ⊩o φ false)) (provesR (Aset, Astruc)[B1 ∪ B2] φ X)

--then send algo to either provesRtoOpen or OpentoClosed.

--confused about: now where do we use lemma11? seems like I muddled 2 things into one.
--do I need some wrapper that mediates between algorithm and combine that says that combine is the same as the union???

--NVM?
 --compatible :
 --strucUnion :
 emcUnion : ∀ {Σ} {oc1 oc2} (A1 : Structure oc1 Σ) (A1 : Structure oc2 Σ) (φ : Formula Σ) → (pf : A1 A2 compatible)
                                → A1 ⊩o φ → A2 ⊩o φ → strucUnion (A1 A2) ⊩o φ

combineIntro : ∀ {Σ} {oc} (Aset B X : Subset) (Astruc : StructureS oc Aset Σ) (φ : Formula Σ) (x : IndividS A τ) (xnew : x ∉ B) →
    (recurcall: → provesR (A, Astruc)[B] X φ) → (nai : provesR  φ (Aset, Astruc)[X∪x] X∪x) →
    →  Either (Either ((Aset, Astruc)[union B {x}] ⊩o φ) ((Aset, Astruc)[union B {x}] ⊩o φ false)) (provesR (Aset, Astruc)[B∪x] φ X)

 combineForget : ∀ {Σ} {oc} (A B X X' : Subset) (Astruc : StructureS oc A Σ)  (φ : Formula Σ) (x : IndividS X τ) (xgone : x ∉ X') →
    (recurcall: →  (provesR (Aset, Astruc)[B] X))  → (provesR (A, Astruc)[B] φ X') --look to see if forget can make something true or false



 combineJoin : ∀ {Σ} {oc} (B1 B2 X : Subset) (A : Structure oc Σ)  (φ : Formula Σ)  → --need decb1 decb2 b1subAset b2Asubset?
    (recurcall1: →  (provesR (restriction A B1 decb1 b1subAset) φ X))
  (recurcall2: → (provesR (restriction A B2 decB2 B2subAset) φ X))
    →  Either (Either ((restriction A (union B1 B2) decB1B2 B1B2subAset) ⊩o φ) ((restriction A (union B1 B2) decB1B2 B1B2subAset φ X) ⊩o φ false))
    (provesR (restriction A (union B1 B2) decB1B2 B1B2subAset) φ X)

combineIntro : ∀ {Σ} {oc} (B X : Subset) (A: Structure oc Aset Σ) (φ : Formula Σ) (x : IndividS A τ) (xnew : (Sub (singleton {τ = τ} x) (complement B))) →
    (recurcall: provesR (restriction A B decb bsubAset) X φ) →
    (nai : provesR (restriction A (union X (singleton {τ = τ} x)) decXx XxsubAset) φ (union X (singleton {τ = τ} x)))
    → Either (Either ((restriction A (union B (singleton {τ = τ} x)) decBx BxsubA) ⊩o φ)
                     ((restriction A (union B (singleton {τ = τ} x)) decBx BxsubA) ⊩o φ false))
                      ((restriction A (union B (singleton {τ = τ} x)) decBx BxsubA) provesR  φ X)

 combineForget : ∀ {Σ} {oc} (A B X X' : Subset) (Astruc : StructureS oc A Σ)  (φ : Formula Σ) (x : IndividS X τ) (xgone : x ∉ X') →
    (recurcall: →  (provesR (Aset, Astruc)[B] X))  → (provesR (A, Astruc)[B] φ X') --look to see if forget can make something true or false

 combineJoin : ∀ {Σ} {oc} (Aset B1 B2 X : Subset) (Astruc : StructureS oc Aset Σ)  (φ : Formula Σ)  →
    (recurcall1: →  (provesR (Aset, Astruc)[B1] φ X))
  (recurcall2: → (provesR (Aset, Astruc)[B2] φ X))
    →  Either (Either ((Aset, Astruc)[B1 ∪ B2] ⊩o φ) ((Aset, Astruc)[B1 ∪ B2] ⊩o φ false)) (provesR (Aset, Astruc)[B1 ∪ B2] φ X)
