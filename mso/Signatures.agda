{-# OPTIONS --type-in-type --without-K #-}

open import lib.Prelude

module mso.Signatures where

  Dec : Type → Type
  Dec A = Either A (A → Void)

  data Tp : Type where
    node : Tp
    edge : Tp

  -- all supposed to have decidable equality
  Individ : Tp → Type
  Individ node = String
  Individ edge = String

  postulate 
    IndividDec : ∀ {τ} (p q : Individ τ) → Dec (p == q)

  Args : Type
  Args = List Tp

  Individs : Args → Type
  Individs [] = Unit
  Individs (τ :: τs) = Individs τs × Individ τ

  data SigThing : Type where   --a thing in a signature is either
    i : Tp → SigThing          --
    r : List Tp → SigThing

  Signature = List SigThing

  _,i_ : Signature → Tp → Signature
  Σ ,i τ = i τ :: Σ

  _,r_ : Signature → Args → Signature
  Σ ,r τs = r τs :: Σ

  infixl 10 _,i_
  infixl 10 _,r_

  Graph : Signature
  Graph = [] ,r (node :: node :: [])

  Subset = (τ : Tp) → Individ τ → Type -- FIXME: decidable/finite?
     --predicate on elements of certain type, diffent
     --types can have different stipulatons

  DecidableSub : (S1 : Subset) → Type
  DecidableSub S1  = ∀ {τ} (x : Individ τ) → Dec (S1 τ x)

  example1 : Subset
  example1 node x = x == "a"
  example1 edge x = x == "7"

  IndividS : Subset → Tp → Type
  IndividS A τ = Σ \ (x : Individ τ) → A τ x
     --an individ that's in a subset

  IndividsS : Subset → Args → Type
  IndividsS A [] = Unit
  IndividsS A (τ :: τs) = IndividsS A τs × IndividS A τ
      --relation type thats in subset (all args are in)

  mapIndividS : ∀ {A1 A2 : Subset} → (∀ {τ} → IndividS A1 τ → IndividS A2 τ) →  (∀ {τ} → IndividsS A1 τ → IndividsS A2 τ)
  mapIndividS f {[]} x = <>
  mapIndividS f {x :: τ} (a , b) = mapIndividS f a , f b

  data OC : Type where
    Open : OC
    Closed : OC

  data StructureS : OC → Subset → Signature → Type where
     []      : ∀ {oc A} → StructureS oc A []
     _,is_   : ∀ {oc A Σ τ} → StructureS oc A Σ → IndividS A τ → StructureS oc A (Σ ,i τ)
     _,none  : ∀ {oc A Σ τ} → StructureS oc A Σ → StructureS Open A (Σ ,i τ)              -- s,_/x
     _,rs_   : ∀ {oc A Σ τs} → StructureS oc A Σ → (IndividsS A τs → Type) → StructureS oc A (Σ ,r τs)
     -- tau is node or edge/arg type
  postulate
    openify : ∀ {oc A Σ} → StructureS oc A Σ → StructureS Open A Σ
    --any structure can be regarded as open

  Structure : OC → Signature → Type
  Structure oc Sig = Σ \ (A : Subset) → StructureS oc A Sig

{-
  example : Structure (· ,i node ,i edge)
  example = example1 , (<> , ("a" , id)) , {!!}

  particulargraph : Structure Graph
  particulargraph = {!!}
-}

  union : (S1 : Subset) (S2 : Subset) → (Subset)
  union S1 S2 τ x = Either (S1 τ x) (S2 τ x)

  constants : ∀ {Σ oc} → (A1 : Structure oc Σ) → (Subset)
  constants (A1 , []) τ x = Void
  constants (A , _,is_ {τ = τ} s1  x) = union (constants (A , s1))                                       --want old constants from A plus new constant x, ie all individS equal to x. eek is proof that x and y are of same individual type,
                                          (λ τ1 y →                                                      --transport takes elems of same type between each other
                                             Σ (λ (eek : τ == τ1) → y == transport Individ eek (fst x))) -- only need fst x because individS is individ with underlying set
  constants (A1 , s1 ,none) = constants (A1 , s1)                                                         -- and we're forgetting about the set. subset is just predicate!
  constants (A , s1 ,rs x) = constants (A , s1)

  postulate 
    constantsDec : ∀ {Σ oc} (A1 : Structure oc Σ) → DecidableSub (constants A1)
    unionDec : ∀ {S1 S2} → DecidableSub S1 → DecidableSub S2 → DecidableSub (union S1  S2)

  data Sub (S1 : Subset)  (S2 : Subset) : Type where  --datatypes are injective type constructors so easier for agda to parse pieces of
    sub : (∀ {τ} x → S1 τ x → S2 τ x) → Sub S1 S2

  unsub : {S1 S2 : Subset} (prf : Sub S1 S2) → (∀ {τ} x → S1 τ x → S2 τ x)
  unsub (sub x) = x

  promoteIndividS : ∀ {τ} {S1 S2 : Subset} (proof : Sub S1 S2) (ind : IndividS S1 τ  ) -> IndividS S2 τ --fill out! takes an individ of a Subset to larger set
  promoteIndividS {τ} {S1} {S2} pf ind = fst(ind) , unsub pf (fst ind) (snd ind)

  promoteIndividsS : ∀ {τs} {S1 S2 : Subset} (proof : Sub S1 S2) (ind : IndividsS S1 τs  ) -> IndividsS S2 τs --takes an individs of a Subset to a larger set
  promoteIndividsS pf2 ind2 = mapIndividS (promoteIndividS pf2) ind2

   -- Lemma: if A is Sub C, B is Sub C, then A union B is Sub C
  subLUB : ∀ {A B C : Subset} → (pf1 : Sub A C) (pf2 : Sub B C) → (Sub (union A B) (C))
  subLUB pf1 pf2 = sub (λ x → \ { (Inl P) → unsub pf1 x P ; (Inr P) → unsub pf2 x P } )

--sublemma
  constantSubHelp : ∀ {A} {τx} (x : IndividS A τx) {τ : Tp} (x₁ : Individ τ) →  (eek : τx == τ) → (x₁ == transport Individ eek (fst x)) → A τ x₁
  constantSubHelp x ._ id id = snd x

  --Lemma : constants of A is a Subset of fst (A)
  constantSub : ∀ {Σ oc} (A : Structure oc Σ) → Sub (constants A) (fst A)
  constantSub (A , []) = sub (λ _ → λ ()) ---this shows void is subset of everything (empty subset is subset of everything; given x and evidence x is in empty set -> impossible
  constantSub (A , struc ,is x) = subLUB (constantSub (A , struc)) (sub (λ x1 P → constantSubHelp x x1 (fst P) (snd P)))
  constantSub (A , struc ,none) = constantSub (A , struc) --is this right?
  constantSub (A , struc ,rs x) = constantSub (A , struc) --is this right?

  subINL : ∀ {A B : Subset} → (Sub (A) (union A B )) --fill out!!
  subINL {A} {B} = sub (λ x x1 → Inl x1) --is this right??

  subINR : ∀ {A B : Subset} → (Sub (B) (union A B ))
  subINR {A} {B} = sub (λ x x1 → Inr x1)

  subtrans : ∀ {A B C : Subset } → (Sub A B) → (Sub B C) → Sub A C
  subtrans {A} {B} {C} (sub x1) (sub x2) = sub (λ x → λ xinA → x2 _ (x1 x xinA))
  preserves :  ∀ {Σ oc1 oc2} (A1 : Structure oc1 Σ) (A2 : Structure oc2 Σ)
               (f : ∀ {τ} → IndividS (fst A1) τ → IndividS (fst A2) τ ) → Type
  preserves (A1 , []) (A2 , []) f = Unit
  preserves (A1 , s1 ,is x) (A2 , s2 ,is xx)  f = preserves (A1 , s1) (A2 , s2) f × (fst (f x) == fst xx)
  preserves (A1 , s1 ,is x) (A2 , s2 ,none)  f = Void
  preserves (A1 , s1 ,none) (A2 , s2 ,is x) f = Void
  preserves (A1 , s1 ,none) (A2 , s2 ,none)  f = preserves (A1 , s1) (A2 , s2)  f
  preserves (A1 , s1 ,rs U1) (A2 , s2 ,rs U2)  f = Σ (λ (p : preserves (A1 , s1) (A2 , s2)  f)
                                                       → (v : IndividsS A1 _ ) → U1 v
                                                       → U2 (mapIndividS f v))

  iso : ∀ {Σ oc1 oc2} (A1 : Structure oc1 Σ) (A2 : Structure oc2 Σ) → Type
  iso A1 A2 = Σ \ (f : ∀ {τ} → IndividS (fst A1) τ → IndividS (fst A2) τ )→ preserves A1 A2 f × (∀ τ → IsEquiv (f {τ})) --IsEquiv says that theres an inverse that composes to id with f


  restrictionS : ∀ {Σ} {oc1} {A1} (A1' : StructureS oc1 A1  Σ) (S1 : Subset) → DecidableSub S1 → Sub S1 (A1) →  StructureS Open S1 Σ
  restrictionS [] S1 dec sb = []
  restrictionS (A1' ,is x) S1 dec sb with dec (fst x)
  ... | Inl inS = restrictionS A1' S1 dec sb ,is (fst x , inS) 
  ... | Inr out = restrictionS A1' S1 dec sb ,none
  restrictionS (A1' ,none) S1 dec sb = restrictionS A1' S1 dec sb ,none
  restrictionS (A1' ,rs U) S1 dec sb = restrictionS A1' S1 dec sb ,rs (λ v → U (promoteIndividsS sb v))

  restriction : ∀ {Σ} {oc1} (A1 : Structure oc1  Σ) (S1 : Subset) → DecidableSub S1 → Sub S1 (fst A1) →  Structure Open Σ
  restriction (A1' , struc) S1 dec sb = S1 , restrictionS struc S1 dec sb

  positionEquiv : ∀ {Σ oc1 oc2} (A1 : Structure oc1 Σ) (A2 : Structure oc2 Σ) 
                  (X : Subset)  (XinA1 : Sub X (fst A1)) (XinA2 : Sub X (fst A2)) 
                → DecidableSub X 
                → Type
  positionEquiv A1 A2 X X⊆A1 X⊆A2 decX = Σ \ (h : iso (restriction A1 (union (constants A1) X) (unionDec {S1 = constants A1} {S2 = X} (constantsDec A1) decX) (subLUB (constantSub A1) X⊆A1)) 
                                                      (restriction A2 (union (constants A2) X) (unionDec {S1 = constants A2} {S2 = X} (constantsDec A2) decX) (subLUB (constantSub A2) X⊆A2)))
                                         → ∀ {τ} (x : IndividS X τ) → fst h (promoteIndividS (subINR {A = constants A1} {B = X}) x) == promoteIndividS (subINR {A = constants A2} {B = X}) x

 -- OLD defintion of positionEquiv by induction on the structure; might be useful if we need something like this later
 -- might need to check position equivalence at some point
 {- mutual
    positionEquiv : ∀ {Σ oc1 oc2} (A1 : Structure oc1 Σ) (A2 : Structure oc2 Σ) (X : Subset) (XinA1 : Sub X (fst A1)) (XinA2 : Sub X (fst A2)) → Type
    positionEquiv (A1 , []) (A2 , []) X _ _ = Unit
    positionEquiv (A , s1 ,is x) (A2 , s2 ,is xx) X x1 x2 = {!Σ (\ ( p1 : positionEquiv (A , s1) (A2 , s2) X x1 x2) → (v1 : IndividS (union (constants (A , s1)) X) _) → x (promoteIndividS (subLUB (constantSub (A , s1)) x1) v1) -> xx (promoteIndividS (subLUB (constantSub (A2 , s2)) x2) (positionEquiv-fn {A1 = (A , s1)} {A2 = (A2 , s2)} p1 v1)))!}
    positionEquiv (A , s1 ,is x) (A2 , s2 ,none) X _ _ = Void
    positionEquiv (A1 , s1 ,none) (A2 , s2 ,is x) X _ _ = Void
    positionEquiv (A1 , s1 ,none) (A2 , s2 ,none) X x1 x2 = positionEquiv (A1 , s1) (A2 , s2) X x1 x2  --need to have different ocs because introducing a nil can open a struc (see above)
    positionEquiv (A , s1 ,rs U1) (A2 , s2 ,rs U2) X x1 x2 = Σ (λ (p : positionEquiv (A , s1) (A2 , s2) X x1 x2)
                                                       → (v : IndividsS (union (constants (A , s1)) X) _) → U1 (promoteIndividsS (subLUB (constantSub (A , s1)) x1) v)
                                                       → U2 (promoteIndividsS (subLUB (constantSub (A2 , s2)) x2)
                                                               (positionEquiv-fnS {A1 = (A , s1)} {A2 = (A2 , s2)} p v))) --use two lemmas abover here

    positionEquiv-fnHelp :  ∀ {Σ oc1 oc2} {A1 : Structure oc1 Σ} {A2 : Structure oc2 Σ} {X : Subset} {x1 : Sub X (fst A1)} {x2 : Sub X (fst A2)} →  positionEquiv A1 A2 X x1 x2  →
                                                                     ∀ {τ} → IndividS ( (constants A1)) τ → IndividS ((constants A2)) τ
    positionEquiv-fnHelp {A1 = A1 , []} {A2 , []} poseq ind = ind
    positionEquiv-fnHelp {A1 = A , snd ,is x} {A₁ , snd1 ,is x₁} poseq ind = {!!}
    positionEquiv-fnHelp {A1 = A , snd ,is x} {A2 , snd1 ,none} () ind
    positionEquiv-fnHelp {A1 = A1 , snd ,none} {A , snd1 ,is x} () ind
    positionEquiv-fnHelp {A1 = A1 , snd ,none} {A2 , snd1 ,none} poseq ind = positionEquiv-fnHelp {A1 = A1 , snd} { A2 = A2 , snd1 } poseq ind
    positionEquiv-fnHelp {A1 = A1 , snd ,rs x} {A2 , snd1 ,rs x₁} poseq ind = positionEquiv-fnHelp {A1 = A1 , snd} { A2 = A2 , snd1 } (fst poseq) ind --confused because of the individsS vs individS thing going on here

    --first define on const A1 -> const A2, then extend to X with id, then pointwise extend to individsS (map)
    positionEquiv-fn :  ∀ {Σ oc1 oc2} {A1 : Structure oc1 Σ} {A2 : Structure oc2 Σ} {X : Subset} {x1 : Sub X (fst A1)} {x2 : Sub X (fst A2)} →  positionEquiv A1 A2 X x1 x2  →
                                                                     ∀ {τ} → IndividS (union (constants A1) (X)) τ → IndividS (union (constants A2) (X)) τ
    positionEquiv-fn {A1 = A1} {A2} poseq (x , Inl x1) = fst (positionEquiv-fnHelp poseq (x , x1)) ,
                                                           Inl (snd (positionEquiv-fnHelp poseq (x , x1)))
    positionEquiv-fn {A1 = A1} {A2} poseq (x , Inr x1) = x , Inr x1

    --promoteIndividS subINL (positionEquiv-fnHelp poseq ind) --does this work in one go like that or do I need to case split again? also help with im args?

    positionEquiv-fnS :  ∀ {Σ oc1 oc2} {A1 : Structure oc1 Σ} {A2 : Structure oc2 Σ} {X : Subset} {x1 : Sub X (fst A1)} {x2 : Sub X (fst A2)} →  positionEquiv A1 A2 X x1 x2  →
                                                                     ∀ {τ} → IndividsS (union (constants A1) (X)) τ → IndividsS (union (constants A2) (X)) τ
    positionEquiv-fnS poseq {[]} ind = ind
    positionEquiv-fnS {A1 = A1} {A2 = A2} poseq {x :: τ} ind = (positionEquiv-fnS {A1 = A1} {A2} poseq {τ} (fst ind)) , positionEquiv-fn {A1 = A1} {A2} poseq (snd ind)

    data EquivInd {Σ oc1 oc2 τ} {A1 : Structure oc1 Σ} {A2 : Structure oc2 Σ} {X : Subset} {XinA1 : Sub X (fst A1)} {XinA2 : Sub X (fst A2)}
                                (poseq : positionEquiv A1 A2 X XinA1 XinA2) (a1 : IndividS (fst A1) τ) (a2 : IndividS (fst A2) τ) : Type where
       eqindX : X τ (fst a1) → X τ (fst a2) → (fst a1) == (fst  a2) → EquivInd poseq a1 a2
       eqindC : ( ca1 : constants A1 τ (fst a1)) → constants A2 τ (fst a2) → _==_ {Individ τ}  (fst ((positionEquiv-fn {A1 = A1} {A2 = A2} {X = X} {XinA1} {XinA2} poseq) {!!} )) (fst  a2) → EquivInd poseq a1 a2
-}

  -- sometimes helpful to factor things this way

  Branch : ∀ {oc} {Σ : Signature} (A : Structure oc Σ) → (s : SigThing) → Type
  Branch A (r τs) = IndividsS (fst A) τs → Type
  Branch {Open} A (i τ) = Either (IndividS (fst A) τ) Unit
  Branch {Closed} A (i τ) = (IndividS (fst A) τ) 

  extend : ∀ {oc} {Σ : Signature} (A : Structure oc Σ) {s : SigThing} → Branch A s → Structure oc (s :: Σ)
  extend {Open} (A , AA) {i x} (Inl a) = A , AA ,is a
  extend {Open} (A , AA) {i x} (Inr p) = A , AA ,none
  extend {Closed} (A , AA) {i x} a = A , AA ,is a
  extend (A , AA) {r x} b = A , AA ,rs b

