
{-# OPTIONS --type-in-type  #-}

open import lib.Prelude
open import mso.Signatures
open import mso.Formulas
open import mso.ClosedTruth

open ListM
open Index

module mso.opentruth where

  ValueOpen : Subset → SigThing → Type
  ValueOpen A (i τ) = Maybe (IndividS A τ)  --could be a nil but only for a nullary const.
  ValueOpen A (r τs) = (IndividsS A τs → Type)
  --interpreting a signature; result type of get

  getOpen : ∀ {Σ oc} {st : SigThing}
      → st ∈ Σ
      → (A : Structure oc Σ)
      → ValueOpen (fst A) st
  getOpen i0 (A , (_ ,is a)) = Some a
  getOpen i0 (A , (_ ,rs rel)) = rel
  getOpen i0 (A , (_ ,none)) = None
  getOpen (iS i1) (A , SA ,is _) = getOpen i1 (A , SA)
  getOpen (iS i1) (A , SA ,rs _) = getOpen i1 (A , SA)
  getOpen (iS i1) (A , SA ,none) = getOpen i1 (A , SA)
  --lokup in signature

  getsOpen : ∀ {Σ oc} {τs : List Tp}
       → Terms Σ τs
       → (A : Structure oc Σ)
       → Maybe (IndividsS (fst A) τs)   --wanna make sure ALL constant are in domain
  getsOpen [] A = Some <>
  getsOpen (x ,t xs) A  with  (getsOpen xs A) | (getOpen x A)
  ... | Some vs | Some v = Some (vs , v)  --making sure all elements are interpreted
  ... | _ | _ = None  --if not it's dead to us

  --lets you look up a bunch of terms
--predicate identiftying existential formulas bc we need to use uni rules for uni formulas
  data isE {Σ : Signature} : Formula Σ → Type where
    isEexistsi : ∀ {τ} {φ : Formula (i τ :: Σ )} → isE (∃i τ φ)
    isEexistsr :  ∀ {τ} {φ : Formula (r (τ :: []) :: Σ )} → isE (∃p τ φ)
    isEor :  ∀ {φ1 φ2 : Formula Σ } → isE (φ1 ∨ φ2)
    isEfalse : ∀ {φ : Formula Σ } → isE ⊥

--predicate for universal formulas
  data isU {Σ : Signature} : Formula Σ → Type where
    isUforalli : ∀ {τ} {φ : Formula (i τ :: Σ )} → isU (∀i τ φ)
    isUforallr : ∀ {τ} {φ : Formula (r (τ :: []) :: Σ )} → isU (∀p τ φ)
    isUand :  ∀ {φ1 φ2 : Formula Σ } → isU (φ1 ∧ φ2)
    isUtrue :  ∀ {φ : Formula Σ } → isU ⊤

  data isR {Σ : Signature} : Formula Σ → Type where
    isr : ∀ {τs} {r : r τs ∈ Σ} {xs} → isR (R r xs)
    isnotr : ∀ {τs} {r : r τs ∈ Σ} {xs} → isR (¬R r xs)

  data ubranch {Σ1 : Signature} : ∀ { Σ2 : Signature} {oc1 oc2} (A1 : Structure oc1 Σ1) (φ1 : Formula Σ1) (A2 : StructureS oc2 (fst A1) Σ2) (φ2 : Formula Σ2) → Type where
    ufstb : ∀ {oc} {A1 : Structure oc Σ1} → {φ1 φ2 : Formula Σ1} → ubranch A1 (φ1 ∧ φ2) (snd A1) φ1
    usndb : ∀ {oc} {A1 : Structure oc Σ1} → {φ1 φ2 : Formula Σ1} → ubranch A1 (φ1 ∧ φ2) (snd A1) φ2
    uforallb : ∀ {oc} {τ} {A1 : Structure oc Σ1} → {φ : Formula (i τ :: Σ1 )} (a : IndividS (fst A1) τ) → ubranch A1 (∀i τ φ) ( (snd A1) ,is a) φ
    uforallnil : ∀ {oc} {τ} {A1 : Structure oc Σ1} → {φ : Formula (i τ :: Σ1 )}  → ubranch A1 (∀i τ φ) ((snd A1) ,none) φ
    uforallr : ∀ {oc} {τ} {A1 : Structure oc Σ1} → {φ : Formula (r (τ :: []) :: Σ1 )} (r : IndividsS (fst A1) (τ :: []) → Type) → ubranch A1 (∀p τ φ) ( (snd A1) ,rs r) φ

  data ebranch {Σ1 : Signature} : ∀ { Σ2 : Signature} {oc1 oc2} (A1 : Structure oc1 Σ1) (φ1 : Formula Σ1) (A2 : StructureS oc2 (fst A1) Σ2) (φ2 : Formula Σ2) → Type where
    efstb : ∀ {oc} {A1 : Structure oc Σ1} → {φ1 φ2 : Formula Σ1} → ebranch A1 (φ1 ∨ φ2) (snd A1) φ1
    esndb : ∀ {oc} {A1 : Structure oc Σ1} → {φ1 φ2 : Formula Σ1} → ebranch A1 (φ1 ∨ φ2) (snd A1) φ2
    eExistsb : ∀ {oc} {τ} {A1 : Structure oc Σ1} → {φ : Formula (i τ :: Σ1 )} (a : IndividS (fst A1) τ) → ebranch A1 (∃i τ φ)  ((snd A1) ,is a) φ
    eExistsr : ∀ {oc} {τ} {A1 : Structure oc Σ1} → {φ : Formula (r (τ :: []) :: Σ1 )} (r : IndividsS (fst A1) (τ :: []) → Type) → ebranch A1 (∃p τ φ) ((snd A1) ,rs r) φ

--overarching branch
  data branch {Σ1 : Signature} : ∀ { Σ2 : Signature} {oc1 oc2} (A1 : Structure oc1 Σ1) (φ1 : Formula Σ1) (A2 : StructureS oc2 (fst A1)  Σ2) (φ2 : Formula Σ2) → Type where
    ebr : ∀ {Σ2} {oc1 oc2} {A1 : Structure oc1 Σ1} {φ1 : Formula Σ1} {A2 : StructureS  oc2 (fst A1) Σ2} {φ2 : Formula Σ2}
            → isE φ1 → ebranch A1 φ1 A2 φ2 → branch A1 φ1 A2 φ2
    ubr : ∀ {Σ2} {oc1 oc2} {A1 : Structure oc1 Σ1} {φ1 : Formula Σ1} {A2 : StructureS oc2 (fst A1) Σ2} {φ2 : Formula Σ2}
            → isU φ1 → ubranch A1 φ1 A2 φ2 → branch A1 φ1 A2 φ2

  -- open TRUTH: i.e. the structure is open, but the formula is really provable anyway
  data _⊩o_ {oc : _} {Σ : _} (A : Structure oc Σ) : Formula Σ → Type where
    provesu : {φ : Formula Σ}
            → isU φ
            → (∀ {Σ' oc'} {A' : StructureS oc' (fst A) Σ'} {φ'} → ubranch A φ A' φ' → (fst A , A') ⊩o φ')
            → A ⊩o φ
    provese : ∀ {Σ' oc'} {A' : StructureS oc' (fst A) Σ'} {φ : Formula Σ} {φ'}
            → isE φ
            → ebranch A φ A' φ' → (fst A , A') ⊩o φ'
            → A ⊩o φ
    provesbase : ∀ {τs} {rel} {xs : Terms _ τs} vs → ((getsOpen xs A) == (Some vs)) → (getOpen rel A) (vs) → A ⊩o (R rel xs)
    provesnotbase : ∀ {τs} {rel} {xs : Terms _ τs}
                  → (vs : _) → ((getsOpen xs A == (Some vs)))  -- getsOpen actually returns Some vs for some vs
                  → ((getOpen rel A) (vs) → Void) -- and the relation is false on those
                  →  A ⊩o (¬R rel xs)

  _⊩o_false : ∀ {oc Σ} → Structure oc Σ → Formula Σ → Type
  A ⊩o φ false = A ⊩o (φ *)

  data branchfrom {Σ1 : Signature} {oc1} (A1 : Structure oc1 Σ1) (φ1 : Formula Σ1) : Type where
    branchto : ∀ {Σ2 : Signature} {oc2 : _} → (A2 : StructureS oc2 (fst A1) Σ2) (φ2 : Formula Σ2) → branch A1 φ1 A2 φ2 → branchfrom A1 φ1

  --unbranchify : ∀ {Σ1 : Signature} {oc1} (A1 : Structure oc1 Σ1) (φ1 : Formula Σ1) → branchfrom A1 φ1 → Σ Σ2

  Branches : {Σ1 : Signature} {oc1 : _} (A1 : Structure oc1 Σ1) (φ1 : Formula Σ1) → Type
  Branches A1 φ1 = List (branchfrom A1 φ1)

  -- uformula with ubranches, eform with ebranch, or rel cases
  -- raw game tree that is compatible with the formula
  data _⊩s_ {oc : _} {Σ : _} (A : Structure oc Σ) (φ : Formula Σ) : Type where
    leaf : (isR φ) → A ⊩s φ
    node : (bs : Branches A φ) →
           (∀ {Σ'} {oc'} {A' : StructureS oc' (fst A) Σ'} {φ'} b → (branchto A' φ' b) ∈ bs → ((fst A , A') ⊩s φ'))
           → A ⊩s φ

  -- TODO: define equivalence on ⊩s

  fixed : (A1 : Subset) (A2 : Subset) → Type
  fixed A1 A2 = Σ \ (X : Subset) → ((Sub X (A1)) × ( Sub X (A2))) × DecidableSub X

  fixed1 : (A1 : Subset) → Type
  fixed1 A1 = Σ \ (X : Subset) → (Sub X (A1)) × DecidableSub X

  lemma1 : ∀ (A1 : Subset) → fixed1 A1 → fixed A1 A1
  lemma1 A1 (sb , pfs) = sb , (((fst pfs) , (fst pfs)) , (snd pfs))

  positionEquiv' : ∀ {Σ oc1 oc2} (A1 : Structure oc1 Σ) (A2 : Structure oc2 Σ) → fixed (fst A1) (fst A2)  → Type
  positionEquiv' A1 A2 (X , (X⊆A1 ,  X⊆A2) ,  decX )  = positionEquiv A1 A2 X X⊆A1  X⊆A2 decX

  BranchBijection : {Σ : Signature} {oc1 oc2 : _} (A1 : Structure oc1 Σ) (A2 : Structure oc2 Σ) (φ : Formula Σ) → Branches A1 φ → Branches A2 φ → Type
  BranchBijection A1 A2 φ branches1 branches2 =
                  ∀ {Σ' φ'} →
                    Equiv (Σ (λ oc' → Σ (λ (A' : StructureS oc' (fst A1) Σ') → Σ \ b → (branchto A' φ' b) ∈ branches1)))
                          (Σ (λ oc' → Σ (λ (A' : StructureS oc' (fst A2) Σ') → Σ \ b → (branchto A' φ' b) ∈ branches2)))


  mutual

    gameEquiv : ∀ {Σ oc1 oc2} (A1 : Structure oc1 Σ) (A2 : Structure oc2 Σ) (φ : Formula Σ) → A1 ⊩s φ → A2 ⊩s φ → fixed (fst A1) (fst A2) → Type --f didn't have the same type but it worked??
    gameEquiv A1 A2 φ g1 g2 f =  positionEquiv' A1 A2 f × gameEquiv' A1 A2 φ g1 g2 f

    gameEquiv' : ∀ {Σ oc1 oc2} (A1 : Structure oc1 Σ) (A2 : Structure oc2 Σ) (φ : Formula Σ) → A1 ⊩s φ → A2 ⊩s φ → fixed (fst A1) (fst A2) → Type
    gameEquiv' A1 A2 φ (leaf x1) (leaf x2) f = Unit
    gameEquiv' A1 A2 φ (leaf x1) (node bs x2) f = Void
    gameEquiv' A1 A2 φ (node bs1 x1) (leaf x2) f = Void
    gameEquiv' A1 A2 φ (node bs1 x1) (node bs2 x2) f = Σ (λ (b : BranchBijection A1 A2 φ bs1 bs2) →
                                                            ∀ {Σ' oc'} {A' : StructureS oc' (fst A1) Σ'} {φ'} bi →
                                                            (brnchi : branchto A' φ' bi ∈ bs1) →
                                                            gameEquiv ((fst A1) , A') ((fst A2) , (fst (snd (fst b (_ , A' , bi , brnchi))))) φ' (x1 bi brnchi)
                                                            (x2 _ (snd (snd (snd (fst b (_ , A' , bi , brnchi))))))
                                                            f)

  {-# NO_TERMINATION_CHECK #-}
 --this terminates because φ' is smaller than φ
 --bi ∈ bs is enough if conjecture: any two reduced games for A ⊩s φ are equivalent (CHECK!!!!)
  isRed : ∀ {Σ oc} (A : Structure oc Σ) (φ : Formula Σ) → A ⊩s φ → (X : fixed1 (fst A)) → Type
  isRed A φ (leaf x) fix = Unit
  isRed A φ (node bs x) fix =  (∀ {Σ' oc'} {A' : StructureS oc' (fst A) Σ'} {φ'} bj → (prfbr : branchto A' φ' bj ∈ bs) →
                                      isRed (fst A , A') φ' (x bj prfbr) fix) ×
                               (isU φ → ∀ {Σ' oc'} {A' : StructureS oc' (fst A) Σ'} {φ'} bi →
                                    Either (branchto A' φ' bi ∈ bs) (Either ((fst A , A') ⊩o φ')
                                    (Σ
                                       (λ oc'' →
                                          Σ
                                          (λ (A'' : StructureS oc'' (fst A) Σ') →
                                             Σ
                                             (λ bj →
                                                Σ
                                                (λ (pfbr2 : branchto A'' φ' bj ∈ bs) →
                                                   (gi : (fst A , A') ⊩s φ') →
                                                   isRed (fst A , A') φ' gi fix →
                                                   gameEquiv (fst A , A') (fst A , A'') φ' gi (x bj pfbr2)
                                                   (lemma1 _ fix)))))))) ×
                               (isE φ → ∀ {Σ' oc'} {A' : StructureS oc' (fst A) Σ'} {φ'} bi →
                               Either (branchto A' φ' bi ∈ bs)
                               (Either ((fst A , A') ⊩o φ' false) (Σ
                                                                     (λ oc'' →
                                                                        Σ
                                                                        (λ (A'' : StructureS oc'' (fst A) Σ') →
                                                                           Σ
                                                                           (λ bj →
                                                                              Σ
                                                                              (λ (pfbr2 : branchto A'' φ' bj ∈ bs) →
                                                                                 (gi : (fst A , A') ⊩s φ') →
                                                                                 isRed (fst A , A') φ' gi fix →
                                                                                 gameEquiv (fst A , A') (fst A , A'') φ' gi (x bj pfbr2)
                                                                                 (lemma1 _ fix))))))))

  provesR : ∀ {Σ oc} (A : Structure oc Σ) (φ : Formula Σ) (X : fixed1 (fst A))  → Type
  provesR  A φ X = Σ (λ (game : A ⊩s φ) → isRed A φ game X)

  {-  provesR2 : ∀ {Σ oc} (A : Structure oc Σ) (φ : Formula Σ) (game : A ⊩s φ) (X : fixed1 (fst A)) → isRed A φ game X
  provesR2 A φ (leaf x) X pf = Unit
  provesR2 A φ (node bs x) X pf = {!!} -- this seems impossible
-}

 -- define provesR is a definition of a raw game that's reduced (define abbrev for (Σ \ (game : A ⊩s φ) game → isReduced A φ game X))


  --lemmaNaive : if you have a gametree for fst A , snd A and φ1 and the same thing for φ2
  --> then you get the function required in 6 (takes a branch that was in the 2 element list and sends it to one of the gametrees
  lemmaNaive : ∀ { Σ' Σ'' : List SigThing} {oc' oc'' : OC} {A : Structure oc' Σ'} {φ1 φ2 : Formula Σ'} {φ' : Formula Σ'' } → {A' : StructureS oc'' (fst A) Σ''} →
                                         (game1 : A ⊩s φ1) (game2 : A ⊩s φ2) →
                                          (b : branch A (φ1 ∧ φ2) A' φ') →
                                           ((branchto A' φ' b ∈  branchto (snd A) φ1 (ubr isUand ufstb) ::  branchto (snd A) φ2 (ubr isUand usndb) :: [] →
                                               (fst A , A') ⊩s φ'))
  lemmaNaive g1 g2 (ebr () x₁)
  lemmaNaive g1 g2 (ubr isUand ufstb) x = g1
  lemmaNaive g1 g2 (ubr isUand usndb) x = g2

  lemmaNaiveOr : ∀ { Σ' Σ'' : List SigThing} {oc' oc'' : OC} {A : Structure oc' Σ'} {φ1 φ2 : Formula Σ'} {φ' : Formula Σ''} → {A' : StructureS oc'' (fst A) Σ''} →
                                         (game1 : A ⊩s φ1) (game2 : A ⊩s φ2) →
                                          (b : branch A (φ1 ∨ φ2) A' φ') →
                                           ((branchto A' φ' b ∈  branchto (snd A) φ1 (ebr isEor efstb) ::  branchto (snd A) φ2 (ebr isEor esndb) :: [] →
                                               (fst A , A') ⊩s φ'))
  lemmaNaiveOr g1 g2 brch = {!!}

  --lemma for turning reduced halves into wholes needs to happen
  {-lemmaNaiveRed : ∀ { Σ' : List SigThing} {oc' : OC} {A : Structure oc' Σ'} {φ1 φ2 φ' : Formula Σ'} → {A' : StructureS oc' (fst A) Σ'} →
                                         (game1 : A ⊩s φ1) (game2 : A ⊩s φ2) →
                                          (b : branch A (φ1 ∧ φ2) A' φ') →
                                           ((branchto A' φ' b ∈  branchto (snd A) φ1 (ubr isUand ufstb) ::  branchto (snd A) φ2 (ubr isUand usndb) :: [] →
                                               (fst A , A') ⊩s φ'))
  lemmaNaiveRed g1 g2 = ? -}



--naive algorithm to work on the restricted bags... this is what we had on the board but I feel very wrong about this
 --postulate
  naive : ∀ {Σ'} → (φ : Formula Σ') (A : Structure Closed Σ') → (X : fixed1 (fst A)) → Either (Either (A ⊩o φ) (A ⊩o φ false)) (provesR A φ X) --change to opentruth??
  naive (∀i τ φ) A fix = {!!} --forall with finite domain so really just a tuple of just checking all the things in the subset
  naive (∃i τ φ) A fix = {!!}
  naive (∀p τ φ) A fix = {!!}
  naive (∃p τ φ) A fix = {!!}
  naive (φ1 ∧ φ2) A fix with naive φ1 A fix | naive φ2 A fix
  naive (φ1 ∧ φ2) A fix | Inl (Inl x) | Inl (Inl x1) = Inl (Inl (x , x1))
  naive (φ1 ∧ φ2) A fix | Inl (Inl x) | Inl (Inr x1) = Inl (Inr (Inr x1))
  naive (φ1 ∧ φ2) A fix | Inl (Inr x) | Inl (Inl x1) = Inl (Inr (Inl x))
  naive (φ1 ∧ φ2) A fix | Inl (Inr x) | Inl (Inr x1) = Inl (Inr (Inl x))
  naive (φ1 ∧ φ2) A fix | Inl (Inl x) | Inr x1 = Inr {!!} --the game is reduced because half of it is true and the rest is reduced
  naive (φ1 ∧ φ2) A fix | Inl (Inr x) | Inr x1 = Inl (Inr (Inl x))
  naive (φ1 ∧ φ2) A fix | Inr x | Inl (Inl x1) = Inr {!x!} --the second part we proved true so idk what to do here?
  naive (φ1 ∧ φ2) A fix | Inr x | Inl (Inr x1) = Inl (Inr (Inr x1))
  naive (φ1 ∧ φ2) A fix | Inr x | Inr x1 = Inr ((node (branchto _ _ (ubr isUand ufstb) :: branchto _ _ (ubr isUand usndb) :: [])
                                                                (λ b → lemmaNaive {A = A} {φ1 = φ1} {φ2 = φ2} (fst x) (fst x1) b) )
                                      , ({!(fst (snd x) , fst (snd x1))!} , {!(snd (snd x) , snd (snd x1))!})) --how do i put the halves back together?
  naive (φ1 ∨ φ2) A fix with naive φ1 A fix |  naive φ2 A fix
  naive (φ1 ∨ φ2) A fix | Inl (Inl x) | Inl (Inl x₁) = Inl (Inl (Inl x))
  naive (φ1 ∨ φ2) A fix | Inl (Inr x) | Inl (Inl x₁) = Inl (Inl (Inr x₁))
  naive (φ1 ∨ φ2) A fix | Inl (Inl x) | Inl (Inr x₁) = Inl (Inl (Inl x))
  naive (φ1 ∨ φ2) A fix | Inl (Inr x) | Inl (Inr x₁) = Inl (Inr (x , x₁))
  naive (φ1 ∨ φ2) A fix | Inl (Inl x) | Inr x₁ = {!!} --what to do when one half is reduced and one half is true for existential?
  naive (φ1 ∨ φ2) A fix | Inl (Inr x) | Inr x1 = Inr ({!fst x1!} , {!!}) --this is a reduced game, how do i get there?
  naive (φ1 ∨ φ2) A fix | Inr x | Inl (Inl x₁) = {!!}
  naive (φ1 ∨ φ2) A fix | Inr x | Inl (Inr x₁) = {!!}
  naive (φ1 ∨ φ2) A fix | Inr x | Inr x₁ = Inr ((node
                                                   (branchto _ _ (ebr isEor efstb) ::
                                                    branchto _ _ (ebr isEor esndb) :: [])
                                                   {!!}) , {!!})
  naive ⊤ A fix = {!!}
  naive ⊥ A fix = {!!}
  naive (R x x₁) A fix = {!!}
  naive (¬R x x₁) A fix = {!!}

{-
  introduce : (A : Structure Open Σ) (φ : Formula Σ) (game : A ⊩s φ) (X : fixed1 (fst A)) →
  (xnew : (Sub (singleton {τ = τ} x) (complement X)))
combine and introduce and forget
-}
