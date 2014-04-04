%include agda.fmt

\ignore{
\begin{code}

{-# OPTIONS --type-in-type --no-termination-check #-}

open import lib.Prelude 
open BoolM 
import lib.PrimTrustMe
open import computational-interp.hcanon.HSetLang

module computational-interp.hcanon.HSetProof where
\end{code}}

I'm using an intrinsic encoding of syntax.  The syntax is necessary
because we need to define the logical relation/prove the fundamental
theorem by induction, and we can't induct on all Agda terms inside Agda.

\begin{itemize}
\item |Ctx Γ|, where Γ is an Agda type, is syntax representing a context, which interprets to Γ:
\noagda\begin{code}
  data Ctx where
    ·   : Ctx Unit
    _,_ : ∀ {Γ A} → (Γ* : Ctx Γ) → Ty Γ* A → Ctx (Σ A)
\end{code}

\item |Ty Γ* A|, where |Γ* : Ctx Γ| and |A : Γ → Type|, 
is syntax representing a type, which decodes to the Agda type |A|.  

\noagda \begin{code}
  data Ty where
    bool : ∀ {Γ} {Γ* : Ctx Γ} → Ty Γ* (\ _ -> Bool)
    prop : ∀ {Γ} {Γ* : Ctx Γ} → Ty Γ* (\ _ -> Type)  -- really small hprops?
    proof : ∀ {Γ} {Γ* : Ctx Γ} (M : Tm Γ* prop) → Ty Γ* (\ θ → (interp M θ))
    Π : ∀ {Γ A B} {Γ* : Ctx Γ} 
          (A* : Ty Γ* A) (B* : Ty (Γ* , A*) B) 
       → Ty Γ* (\ θ → (x : A θ) → (B (θ , x)))
    id : ∀ {Γ A} {Γ* : Ctx Γ} (A* : Ty Γ* A) (M N : Tm Γ* A*) 
        → Ty Γ* (\ θ → interp M θ == interp N θ)
    -- some explicit structural properties
    w : ∀ {Γ A B} {Γ* : Ctx Γ} → (A* : Ty Γ* A) (B* : Ty Γ* B) → Ty (Γ* , A*) (\ θ → B (fst θ))
    subst1 : ∀ {Γ A B} {Γ* : Ctx Γ} {A* : Ty Γ* A} (B* : Ty (Γ* , A*) B)
               (M : Tm Γ* A*) → Ty Γ* (\ θ → B (θ , interp M θ))
    ex : ∀ {Γ A B C} {Γ* : Ctx Γ} (A* : Ty Γ* A) (B* : Ty Γ* B) 
       → Ty ((Γ* , A*) , w A* B*) C 
       → Ty ((Γ* , B*) , w B* A*) (\ θ → C ((fst (fst θ) , snd θ) , snd (fst θ)))
\end{code}

\item |Tm Γ* A*|, where |Γ* : Ctx Γ| and |A* : Ty Γ* A|, is syntax representing a 
term, which decodes to a function |(θ : Γ) → A θ|:

\noagda \begin{code}
  interp  : ∀ {Γ A} {Γ* : Ctx Γ} {A* : Ty Γ* A} → Tm Γ* A* → (θ : Γ) → (A θ)
\end{code}

Then we just give the typing rules; |interp| is defined like you would expect:

\noagda \begin{code}
  data Tm where
    -- last variable
    v    : ∀ {Γ A} {Γ* : Ctx Γ} {A* : Ty Γ* A} → Tm (Γ* , A*) (w A* A*)
    -- general weakening
    w    : ∀ {Γ A B} {Γ* : Ctx Γ} {A* : Ty Γ* A} {B* : Ty Γ* B} 
         → Tm Γ* B* → Tm (Γ* , A*) (w A* B*)
    true : ∀ {Γ} {Γ* : Ctx Γ} → Tm Γ* bool
    false : ∀ {Γ} {Γ* : Ctx Γ} → Tm Γ* bool
    unit  : ∀ {Γ} {Γ* : Ctx Γ} → Tm Γ* prop
    unit⁺  : ∀ {Γ} {Γ* : Ctx Γ} → Tm Γ* prop
    void  : ∀ {Γ} {Γ* : Ctx Γ} → Tm Γ* prop
    `∀    : ∀ {Γ} {Γ* : Ctx Γ} (A* : Tm Γ* prop) (B* : Tm (Γ* , proof A*) prop) → Tm Γ* prop
    <>    : ∀ {Γ} {Γ* : Ctx Γ} → Tm Γ* (proof unit)
    <>⁺     : ∀ {Γ} {Γ* : Ctx Γ} → Tm Γ* (proof unit⁺)
    split1 : ∀ {Γ} {Γ* : Ctx Γ} {C : _} (C* : Ty (Γ* , proof unit⁺) C)
          → Tm Γ* (subst1 C* <>⁺) 
          → (x : Tm Γ* (proof unit⁺)) → Tm Γ* (subst1 C* x)
    abort : ∀ {Γ C} {Γ* : Ctx Γ} {C* : Ty Γ* C} → Tm Γ* (proof void) → Tm Γ* C*
    plam  : ∀ {Γ} {Γ* : Ctx Γ} {A* : Tm Γ* prop} {B* : Tm (Γ* , proof A*) prop}
          → Tm (Γ* , proof A*) (proof B*) → Tm Γ* (proof (`∀ A* B*))
    papp  : ∀ {Γ} {Γ* : Ctx Γ} {A* : Tm Γ* prop} {B* : Tm (Γ* , proof A*) prop}
          → Tm Γ* (proof (`∀ A* B*)) → (M* : Tm Γ* (proof A*)) → Tm Γ* (subst1 (proof B*) M*)
    if    : ∀ {Γ C} {Γ* : Ctx Γ} {C* : Ty (Γ* , bool) C} 
          → Tm Γ* (subst1 C* true) 
          → Tm Γ* (subst1 C* false) 
          → (x : Tm Γ* bool) → Tm Γ* (subst1 C* x)
    lam  : ∀ {Γ A B} {Γ* : Ctx Γ} {A* : Ty Γ* A} {B* : Ty (Γ* , A*) B}
         → Tm (Γ* , A*) B* → Tm Γ* (Π A* B*)
    app  : ∀ {Γ A B} {Γ* : Ctx Γ} {A* : Ty Γ* A} {B* : Ty (Γ* , A*) B} 
         → Tm Γ* (Π A* B*) → (M* : Tm Γ* A*) → Tm Γ* (subst1 B* M*)
    refl : ∀ {Γ A} {Γ* : Ctx Γ} {A* : Ty Γ* A} (M : Tm Γ* A*) → Tm Γ* (id A* M M) 
    tr   : ∀ {Γ A C} {Γ* : Ctx Γ} {A* : Ty Γ* A} 
           (C* : Ty (Γ* , A*) C) {M1 M2 : Tm Γ* A*} (α : Tm Γ* (id A* M1 M2))
         →  Tm Γ* (subst1 C* M1) → Tm Γ* (subst1 C* M2)
    uap  : ∀ {Γ} {Γ* : Ctx Γ} {P : Tm Γ* prop} {Q : Tm Γ* prop} 
           (f : Tm (Γ* , proof P) (w (proof P) (proof Q)))
           (g : Tm (Γ* , proof Q) (w (proof Q) (proof P)))
           → Tm Γ* (id prop P Q)
    deq : ∀ {Γ A} {Γ* : Ctx Γ} {A* A'* : Ty Γ* A} → Tm Γ* A* → Tm Γ* A'* -- any two ways of saying the same type are equal
    lam=  : ∀ {Γ A B} {Γ* : Ctx Γ} {A* : Ty Γ* A} {B* : Ty (Γ* , A*) B} 
           (f g : Tm Γ* (Π A* B*))
           (α : Tm (Γ* , A*) (id B* (unlam f) (unlam g)))
           → Tm Γ* (id _ f g)
\end{code}
\end{itemize}

Here's the definition of candidates so far:

\begin{code}
  Propo = Type -- really small hprops?

  record Candidate (P : Propo) : MetaType where
   constructor cand
   field 
    redP            : (Q : Propo) → P == Q → Q → MetaType
    -- redP respects paths in all positions
    -- (this is what transport would be if it were (Σ \ Q -> P == Q × Q) → Type)
    transportPfull : {Q1 Q2 : Propo} {α1 : P == Q1} {α2 : P == Q2} {p1 : Q1} {p2 : Q2}
                     (propo : Q1 == Q2) (path : propo ∘ α1 == α2) (elt : coe propo p1 == p2)
                   → redP Q1 α1 p1 → redP Q2 α2 p2
   -- special case: redP respects homotopy of elements
   transportP      : (Q : Propo) (α : P == Q) → (p1 p2 : Q) → p1 == p2 → redP Q α p1 → redP Q α p2
   transportP _ α _ _ β r = transportPfull id (∘-unit-l α) β r
  open Candidate
\end{code}

|MetaType| is a synonym For |Type| that I'm using for "metalanguage
types", as opposed to things like |Γ| and |A|, which I'm thinking of as
object language types.  The key idea is that you're never allowed to
|transport| at a family of |MetaType|s: don't think of these as fibrant.  
So we need to implement transport explicitly.  

|redP| is a predicate on all propositions equal to |P|.  |transportPfull|
is like transport for this predicate: given equal propositions, paths,
and elements, you get a transport function.  A special case that comes
up often is just transforming the proof |p1|.  

Because of the intrinsic encoding, the definition of the logical
relation and the proof of the fundamental theorem is one big mutual
definition:

\begin{code}
  RC : ∀ {Γ} → (Γ* : Ctx Γ) (θ : Γ) → MetaType
  R : ∀ {Γ A} (Γ* : Ctx Γ) (A* : Ty Γ* A) → {θ : Γ} → RC Γ* θ → (A θ) → MetaType
  Q : ∀ {Γ A} (Γ* : Ctx Γ) (A* : Ty Γ* A) → {θ : Γ} → (rθ : RC Γ* θ) 
     → {M N : A θ} → R Γ* A* rθ M → R Γ* A* rθ N → (α : M == N) → MetaType
  fund : ∀ {Γ A θ} (Γ* : Ctx Γ) (A* : Ty Γ* A) (rθ : RC Γ* θ) → (M : Tm Γ* A*) → R Γ* A* rθ (interp M θ)
\end{code}

|R| is what Carlo was calling |E|: it's the logical predicate on terms.
It takes (1) a syntactic context |Γ*| (2) a syntactcic type |A*| (3) a
reducible substitution |θ| and (4) a "semantic" term |M|---i.e. an
element of the Agda type |A θ|---\emph{not} a syntactic term |M*|.  This
way, |R| is defined on \emph{definitional} equivalence classes of terms,
and we can prove homotopies between terms as usual in Agda, rather than
having to do it inside the encoded language.  We don't need to think of
it as being defined on homotopy-equivalence-classes; we'll come back to
this below.

|Q| is the corresponding thing for paths: given two reducible terms |M| and |N|,
it is a predicate on paths between them.  

|RC| says that an element of a context is reducible if everything in it is reducible:

\begin{code}
  RC · θ = Unit
  RC (Γ* , A*) (θ , M) = Σ (λ (sθ : RC Γ* θ) → R Γ* A* sθ M)
\end{code}

|fund| (fundamental theorem) says that the interpretation of |M| is always in the relation.  

\begin{code}
  R _ bool rθ M = Either (M == True) (M == False)
  R Γ* prop rθ P = Candidate P
  R Γ* (proof M) rθ pf = R-proof Γ* M rθ pf
  R Γ* (Π{Γ}{A}{B} A* B*) {θ} rθ M = (N : (A θ)) (rN : R Γ* A* rθ N) → R (Γ* , A*) B* (rθ , rN) (M N)
  R Γ* (id A* M N) rθ α = Q Γ* A* rθ (fund Γ* A* rθ M) (fund Γ* A* rθ N) α
\end{code}

OK, now the definition of |R|: at |bool|, you either have a path to true
or a path to false.  At |prop|, you have a candidate.  At Π it's the
usual thing.  At |id| it's |Q|.  For Agda reasons, the case for |proof
M| needs to be broken out into a separate lemma, so it is below.  We
also need cases for the explicit structural properties, which just
manipulate the context in the appropriate way (compare with the usual
statement of compositionality):

\begin{code}
  R ._ (w{Γ* = Γ*} A* B*) {θ , _} (rθ , _) M = 
    R Γ* B* rθ M
  R .Γ* (subst1{Γ}{A0}{B}{Γ*}{A0*} B* M0) {θ} rθ M = 
    R (Γ* , A0*) B* (rθ , fund _ A0* rθ M0) M
  R ._ (ex {Γ* = Γ*} A* B* C*) ((rθ , rb) , ra) M = R-ex Γ* A* B* C* rθ rb ra M
\end{code}

\begin{code}
  R-ex Γ* A* B* C* rθ rb ra M = R ((Γ* , A*) , w A* B*) C* ((rθ , ra) , rb) M
\end{code}

Now, |R Γ* (proof φ) rθ pf| is defined as follows:  

\begin{code}
  R-proof Γ* φ rθ pf = redP (fund Γ* prop rθ φ) φ id pf
\end{code}

That is, the interpretation of φ gives you a candidate, and you ask that
the predicate for the candidate (which works for any type equal to φ)
holds at |φ|, |id|, |pf|.

On to Q:

\begin{code}
  -- is this an hprop in the metalanguage?
  Q Γ* bool rθ rM rN α = Unit  -- FIXME: should we insist that it's refl?
  Q Γ* prop rθ rM rN α = ((x : _) → redP rM _ id x → redP rN _ id (coe α x)) × ((y : _) → redP rN _ id y → redP rM _ id (coe (! α) y))
  Q Γ* (proof M) rθ rM rN α = Unit
  Q Γ* (Π A* B*) rθ rM rN α = (x : _) (rx : R Γ* A* rθ x) → Q (Γ* , A*) B* (rθ , rx) (rM _ rx) (rN _ rx) (ap≃ α)
  Q Γ* (id A* M N) rθ rM rN α = Unit
  Q ._ (w{Γ* = Γ*} A* B*) rθ rM rN α = Q Γ* B* (fst rθ) rM rN α
  Q ._ (subst1{_}{_}{_}{Γ*}{A0*} B* M) rθ rM rN α = Q (Γ* , A0*) B* (rθ , fund Γ* A0* rθ M) rM rN α
  Q ._ (ex {Γ* = Γ*} A* B* C*) ((rθ , ra) , rb) rM rN α = Q ((Γ* , A*) , w A* B*) C* ((rθ , rb) , ra) rM rN α
\end{code}

Thus far, I haven't needed anything out of |Q| at |bool|, |proof M|, and
|id|, so they're just |Unit|.  However, I could imagine saying more
here... e.g. at |bool| we might say that the path reduces to refl or
something like that.  I'm trying the proof with the weakest conditions
possible first, because if that works it would be interesting. 

OK, now we "just" need to prove the fundamental theorem.  But of course
there's lots of other structure that you need, too, all mutually.  I
haven't thought through whether the induction works yet.

Here are the lemmas I've needed so far.  If you want to read the proofs
that I have so far, the full version of this is on github
(\url{https://github.com/dlicata335/hott-agda/blob/master/computational-interp/hcanon/HSetProof.agda})

We need to implement transport for |Q| / |R|; think of this as closure under head expansion.   

\begin{code}
  transportQ : ∀ {Γ A} (Γ* : Ctx Γ) (A* : Ty Γ* A) → {θ : Γ} → (rθ : RC Γ* θ) 
             → {M N : A θ} → (rM : R Γ* A* rθ M) → (rN : R Γ* A* rθ N) → {α α' : M == N} (p : α == α')
             → Q Γ* A* rθ rM rN α → Q Γ* A* rθ rM rN α'

  transportR : ∀ {Γ A θ M M'} (Γ* : Ctx Γ) (A* : Ty Γ* A) (rθ : RC Γ* θ) → M == M' → 
               R Γ* A* rθ M → R Γ* A* rθ M'
\end{code}

Proof: induction on |A*|, using |transportPfull| for the candidates.  

Note: I \emph{think} we can get away without proving that these are
bijections/equivalences, which would be hard because it invovles
reasoing \emph{about} the proof of the fundamental lemma.  So far, all
I've needed is that \emph{up to |Q|} |! α| cancels |transport|ing |M|: 

\begin{code}
  transportRQ : ∀ {Γ A θ M1 M2} {α : M1 == M2} (Γ* : Ctx Γ) (A* : Ty Γ* A) (rθ : RC Γ* θ) (rM1 : R Γ* A* rθ M1) 
              → Q Γ* A* rθ (transportR Γ* A* rθ α rM1) rM1 (! α)
\end{code}
This lemma is really important because it lets you massage by a beta
reduction step "for free": it looks like it's saying that any |α| is
reducible, but only when it is relating |rM1| and |transportR ... rM1|.  

Warning: sticky bit: The one place where this semantic definitional
equality bites is in showing that any two types with the same denotation
have the same relation (or, at least, that we can get between them):

\begin{code}
  R-deq : ∀ {Γ A θ M} (Γ* : Ctx Γ) (A* A1* : Ty Γ* A) (rθ : RC Γ* θ) → R Γ* A* rθ M → R Γ* A1* rθ M
\end{code}

Proof: I doubt this can be Agdaed for this representation, because we
have no way to induct on definitional equality; haven't thought about
how to prove it on paper yet.

Refl/inverses/composition are good:
\begin{code}
  fund-refl : ∀ {Γ A} (Γ* : Ctx Γ) (A* : Ty Γ* A) → {θ : Γ} → (rθ : RC Γ* θ) 
       → {M : A θ} → (rM : R Γ* A* rθ M) 
       → Q Γ* A* rθ rM rM id

  fund-sym : ∀ {Γ A θ M N α} (Γ* : Ctx Γ) (A* : Ty Γ* A) (rθ : RC Γ* θ)
               (rM : R Γ* A* rθ M) (rN : R Γ* A* rθ N)
           → Q Γ* A* rθ rM rN α
           → Q Γ* A* rθ rN rM (! α)

  fund-trans : ∀ {Γ A θ M N O α β} (Γ* : Ctx Γ) (A* : Ty Γ* A) (rθ : RC Γ* θ)
               (rM : R Γ* A* rθ M) (rN : R Γ* A* rθ N) (rO : R Γ* A* rθ O) 
             → Q Γ* A* rθ rM rN α
             → Q Γ* A* rθ rN rO β
             → Q Γ* A* rθ rM rO (β ∘ α)
\end{code}
Proof: induction on |A|.  

|transport| and |ap| are good:

\begin{code}
  fund-tr : ∀ {Γ A C θ M1 M2 α N} (Γ* : Ctx Γ) {A* : Ty Γ* A} (C* : Ty (Γ* , A*) C) (rθ : RC Γ* θ)
          (rM1 : R Γ* A* rθ M1) (rM2 : R Γ* A* rθ M2) 
          (rα : Q Γ* A* rθ rM1 rM2 α) 
          (rN : R (Γ* , A*) C* (rθ , rM1) N)
        → R (Γ* , A*) C* (rθ , rM2) (transport (\ x → C (θ , x)) α N)

  fund-ap : ∀ {Γ A B θ M1 M2 α} 
           (Γ* : Ctx Γ) {A* : Ty Γ* A} {B* : Ty (Γ* , A*) B} (f : Tm (Γ* , A*) B*) (rθ : RC Γ* θ)
           (rM1 : R Γ* A* rθ M1) (rM2 : R Γ* A* rθ M2) 
           (rα : Q Γ* A* rθ rM1 rM2 α)
          → Q (Γ* , A*) B* (rθ , rM2) 
              (fund-tr Γ* B* rθ rM1 rM2 rα (fund (Γ* , A*) B* (rθ , rM1) f)) 
              (fund (Γ* , A*) B* (rθ , rM2) f) 
              (apd (\ x -> interp f (θ , x)) α)
\end{code}


I haven't done much of |ap| yet.  for |transport|, it goes like you
would expect: at bool, it's pretty obvious.  At |prop|, you make a new
candidate, exploiting composing up in the predicate equality.  For
|proof P|, you the fact that |ap| is reducible (which gives you that |ap
P α| is a good equivalence).  For |id|, you do the usual reduction to
sym/trans/ap.  I think the fact that |ap (transport C α) β| is good may
need to be a separate lemma.

\begin{code}
  fund-tr {α = α} Γ* bool rθ rM1 rM2 rα (Inl x) = Inl (x ∘ ap≃ (transport-constant α))
  fund-tr {α = α} Γ* bool rθ rM1 rM2 rα (Inr x) = Inr (x ∘ ap≃ (transport-constant α))
  fund-tr {α = α} Γ* prop rθ rM1 rM2 rα rN = cand (λ φ' p x' → redP rN φ' (p ∘ ! (ap≃ (transport-constant α))) x') 
                                                  {!!} 
  fund-tr {α = α} Γ* (proof M) rθ rM1 rM2 rα rN = transportP (fund (Γ* , _) prop (rθ , rM2) M) _ id _ _ (! (ap≃ (transport-ap-assoc (λ x → interp M (_ , x)) α))) 
                                                            (fst ap-is-reducible _ rN) where
          ap-is-reducible : Q Γ* prop rθ (fund (Γ* , _) prop (rθ , rM1) M) (fund (Γ* , _) prop (rθ , rM2) M) (ap (\ x -> interp M (_ , x)) α)
          ap-is-reducible with fund-ap Γ* M rθ rM1 rM2 rα
          ... | (left , right) = (λ x rx → transportPfull (fund (Γ* , _) prop (rθ , rM2) M) id id {!!} 
                                           (left (coe (! (ap≃ (transport-constant α))) x) 
                                                 {!!})) 
                                , {!!} 
  fund-tr {Γ}{A0}{._}{θ}{M1}{M2}{α}{f} Γ* {A0*} (Π{._}{A}{B} A* B*) rθ rM1 rM2 rα rf = 
          λ x rx → {!fund-tr Γ* B* ? (rf _ (fund-tr Γ* A* rθ rM2 rM1 ? rx)) !} -- need Sigmas / generalization to contexts
  fund-tr {θ = θ} {α = α} {N = β} Γ* {A*} (id {A = C} C* M N) rθ rM1 rM2 rα rβ = 
    transportQ (Γ* , A*) C* (rθ , rM2) (fund (Γ* , A*) C* (rθ , rM2) M) (fund (Γ* , A*) C* (rθ , rM2) N)
               (! (transport-Path-d (λ x → interp M (θ , x)) (λ x → interp N (θ , x)) α β))
               (fund-trans (Γ* , A*) C* (rθ , rM2) _ _ _ (fund-trans (Γ* , A*) C* (rθ , rM2) _ _ _ !rMα aprβ) rNα) where
          rMα : Q (Γ* , A*) C* (rθ , rM2)
                 (fund-tr Γ* C* rθ rM1 rM2 rα (fund (Γ* , A*) C* (rθ , rM1) M))
                 (fund (Γ* , A*) C* (rθ , rM2) M) (apd (λ x → interp M (θ , x)) α)
          rMα = fund-ap Γ* {_}{C*} M rθ rM1 rM2 rα

          !rMα : Q (Γ* , A*) C* (rθ , rM2)
                 (fund (Γ* , A*) C* (rθ , rM2) M)
                 (fund-tr Γ* C* rθ rM1 rM2 rα (fund (Γ* , A*) C* (rθ , rM1) M)) (! (apd (λ x → interp M (θ , x)) α))
          !rMα = fund-sym (Γ* , A*) C* (rθ , rM2) _ _ rMα

          rNα : Q (Γ* , A*) C* (rθ , rM2)
                 (fund-tr Γ* C* rθ rM1 rM2 rα (fund (Γ* , A*) C* (rθ , rM1) N))
                 (fund (Γ* , A*) C* (rθ , rM2) N) (apd (λ x → interp N (θ , x)) α)
          rNα = fund-ap Γ* {_}{C*} N rθ rM1 rM2 rα

          aprβ : Q (Γ* , A*) C* (rθ , rM2)
                 (fund-tr Γ* C* rθ rM1 rM2 rα (fund (Γ* , A*) C* (rθ , rM1) M))
                 (fund-tr Γ* C* rθ rM1 rM2 rα (fund (Γ* , A*) C* (rθ , rM1) N))
                 (ap (transport (λ z → C (θ , z)) α) β)
          aprβ = {!(transport (λ z → C (θ , z)) α)!}
  fund-tr {α = α} Γ* {A*} (w .A* B*) rθ rM1 rM2 rα rN = transportR Γ* B* rθ (! (ap≃ (transport-constant α))) rN
  fund-tr Γ* (subst1 A₃ M) rθ rM1 rM2 rα M₁ = {!!}
  fund-tr ._ (ex _ _ _) rθ rM1 rM2 rα M₁ = {!!}
\end{code}
\end{document}

