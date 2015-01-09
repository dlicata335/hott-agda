%include agda.fmt

\section{Heterogeneous equality}

The equality type that we write as |Path{A} a0 a1| is sometimes called
\emph{homogeneous equality}, because it relates two elements |a0| and
|a1| of the same type |A| (where ``same'' here means
definitional/judgemental equality).  McBride~\citep{mcbride00thesis}
introduced a \emph{heterogeneous equality}, which is an equality type
|a:A = b:B| that relates two elements |a:A| and |b:B| which a priori may
have two different types, but is nonetheless inhabited only when both
the two types and the two terms are judgementally equal.  In McBride's
work, heterogeneous equality is used to elide the reasoning why
equations type check from the equations themselves, which simplifies a
derivation of dependent pattern matching from eliminators.  However,
McBride's heterogeneous equality is logically equivalent to a
homogeneous equality type satisfying uniqueness of identity
proofs~\citep{mcbride00thesis}, which is undesireable in homotopy type
theory, because we do not want all types to be sets.  

This paper provides an investigation of how to manage the reasons why
equations type check is a setting where these reasons are proof-relevant.
While we cannot ignore the reason why an equation type checks entirely,
we can still keep the evidence ``off to the side'', rather than
embedding it in the equation itself.  Specifically, we define a type
|HEq A B α a b| where |α : Path{Type} A B| and |a:A, b:B|.  This
heterogeneous equality relates two elements of two different types
\emph{along a specific equality α between the types}.  The introduction
form is a reflexivity constructor |hid : HEq A A id a a|, and the
elimination rule is the standard inductive family eliminator generated
by this constructor:

\begin{code}
HEq-elim  : {A : Type} {a : A}
  (C : (B : Type) (α : Path A B) (b : B) → HEq A B α a b → Type)
  → C A id a hid
  → (B : Type) (α : Path A B) (b : B) (β : HEq A B α a b)
  → C B α b β
HEq-elim {A}{a} C c .A .id .a hid = c
\end{code}
This says that to construct |C| for all heterogeneous equalities β, it
suffices to consider the case where the types are the same and the terms
are the same and the proofs are |id| and |hid|---but note that the motive
|C| has to be general in the evidence α that the types are the same.

However, this notion of heterogeneous equality need not be taken as a
primitive, because it can be reduced to the homogeneous equality type in
several equivalent ways.  Writing |coe : Path{Type} A B → A → B| for the
function (defined by path induction, as |transport (λ X → X)|) that
coerces along a homogeneous equality, the following types are
equivalent:
\begin{itemize}
\item The inductive family |HEq A B α a b| defined above.

\item |Path{B} (coe α a) b| -- send |a| over to |B| using the
  type equality α, and compare the result with |b|.

\item |Path{A} a (coe (! α) b)| -- send |b| over to |A| using
  the type equality α (inverted), and compare the result with |a|.

\item Define heterogeneous equality by path induction (eliminating
  into the universe): when the type equality α is |id|, a heterogeneous
  equality is a homogeneous equality.

\begin{code}
HEq' A .A id a b = Path{A} a b
\end{code}
\end{itemize}

The equivalences between these types are all immediate by by path
induction or |HEq-elim|, showing that this proof-relevant notion of
heterogeneous equality can be expressed in terms of homogeneous
equality: keeping the evidence that the equation type checks ``off to
the side'' is equivalent to embedding it in the equation on either side,
and to the more symmetric fourth option.  What we will argue in this
paper is that it is useful to think in terms of ``off to the side''
abstractions, even though they can be implemented in terms of
homogeneous paths.

%% As an aside, in a type theory with a homogeneous equality type
%% satisfying uniqueness of identity proofs and function extensionality,
%% McBride's rules~\citep{mcbride00thesis} for |a:A = b:B| can be
%% implemented by the type |(α : A == B) → HEq A B α a b|---if the types
%% are equal then the terms are equal (with the caveat that the β rule for
%% the eliminator holds only propositionally).  On the other hand, the
%% heterogeneous equality in the Coq library~\citep{coq,blog} can be
%% implemented by the type |Σ[ α : A == B ] HEq A B α a b|---the types are
%% equal and the terms are equal.  In both cases, uniqueness of identity
%% proofs is necessary to equate an arbitrary proof |α : A == A| to
%% reflexivity: heterogeniety itself is not incompatible with
%% proof-relelvant equality; it is only problematic if you also assume that

\section{Path Over a Path}
\label{sec:pathover}

\subsection{Type Definition}

The heterogeneous equalities |HEq A B α a a'| we consider will often
have the property that some of the outer structure of |A| and |B| is the
same, and the important part of α happens inside this outer structure.
A typical example is a heterogeneous equality 
\begin{code}
HEq  (Vec Nat (n + m))
     (Vec Nat (m + n))
     (ap (Vec Nat) (+-comm m n))
     v1 v2
\end{code}
In this case, both |A| and |B| have the form |Vec Nat -|, and the reason
why the two types are equal is commutativity of addition applied inside
the context |Vec Nat -|.  Here, we represented this as a heterogeneous
equality using congruence (|ap|) to apply |Vec Nat| to both sides of the
proof of commutativity of addition, constructing a path in the universe.

However, we will find it convenient to think in terms of a
\emph{factored} hetereogeneous equality type, which separates a context
(like |Vec Nat -|) from an equality on the insides of the context.  We
call this a ``path over a path'' type, and it can be defined as an
inductive family as follows:
\begin{code}
data PathOverAPath  {A : Type} (C : A → Type) (a1 : A) : 
               (a2 : A) (α : Path a1 a2)
               (c1 : C a1) (c2 : C a2) → Type where
  idOver : {c1 : C a1} → PathOverAPath C a1 a1 id c1 c1
\end{code}
That is, given a type |A| and two points |a1,a2| connected by a path
|α|, along with a dependent type |C : A → Type|, this type relates an
element of |C a1| to an element of |C a2|.  The constructor |idOver|
represents \emph{reflexivity over reflexivity}, and says that any
reflexive equation where α is also reflexivity holds.  

The example above would be rendered as 
\begin{code}
PathOverAPath (Vec Nat) (n+m) (m+n) (+-comm m n) v1 v2
\end{code}
The context |C| is |Vec Nat|, which is morally applied to |n+m| to get
the type of |v1|, to |m+n| to get the type of |v2|, and to
|+-comm m n| to get the proof that the two types are equal.  

Using implicit arguments (the path α usually provides enough information
to infer its endpoints) and constructor overloading (Agda can infer
whether |id| is constructing a path or a path-over-a-path, though we
will sometimes write |idOver| for clarity), we can shorten this
definition to
\begin{code}
data PathOver  {A : Type} (C : A → Type) {a1 : A} : 
               {a2 : A} (α : Path a1 a2)
               (c1 : C a1) (c2 : C a2) → Type where
  id : {c1 : C a1} → PathOver C id c1 c1
\end{code}
The example becomes a concise
\begin{code}
PathOver (Vec Nat) (+-comm m n) v1 v2
\end{code}

Because types are elements of a universe, the above heterogeneous
equality is the special case of |PathOver (λ (X : Type) → X) α a1 a2|
(though this goes up a universe size level).  Conversely, |PathOver| can
be expressed in terms of heterogeneous equality using |ap| as above.
Indeed, the following types are equivalent:

\begin{itemize}
\item The above inductive family definition of |PathOver C {a1}{a2} α c1 c2|
\item |HEq (C a1) (C a2) (ap C α) c1 c2| for any of the definitions above
\item |Path{C a2} (transport C α c1) c2|
\item |Path{C a1} c1 (transport C (! α) c1)|
\item |PathOver| defined by path induction into the universe as
\begin{code}
PathOver C id c1 c2 = Path c1 c2
\end{code}
\end{itemize}
The equivalences are all simple to construct using path induction or
|HEq-elim| or path-over induction.  The final three options are
analogous to the final three ways to render heterogeneous equality
described above, though they are a bit more direct, using |transport C
α| instead of |coe (ap C α)|.  The third, for example, says that a path
in |C| over α is the same as using the function |transport C α| to move
one endpoint into the same fiber as the other, and giving a homogeneous
path there.  

While we have motivated |PathOver| as a factored heterogeneous equality,
it is also helpful to see the geometric intuition for the concept.
Dependent types correspond to fibrations, so a type |C : A → Type| can
be pictured as its total space |Σ a:A. C a| projecting down to |A| by
first projection.  A path-over |γ : PathOver C α c1 c2| represents a
path in |Σ C| between |(a1,c1)| and |(a2,c2|), such that |ap fst σ| is
exactly |α|.  That is, it is a path in the total space that projects
down to, or \emph{lays over}, |α|:

\begin{center}
  \begin{tikzpicture}[yscale=.5,xscale=3]
    \draw (0,0) arc (-90:170:1cm) node[anchor=south east] {|A|} arc (170:270:1cm);
    \draw (0,4) arc (-90:170:1cm) node[anchor=south east] {|Σ C|} arc (170:270:1cm);
    \draw[->] (0,3.8) -- node[auto] {|fst|} (0,2.2);
    \node[circle,fill,inner sep=1pt,label=left:{|a1|}] (a1) at (-.5,1) {};
    \node[circle,fill,inner sep=1pt,label=right:{|a1|}] (a2) at (.5,1) {};
    \draw[decorate,decoration={snake,amplitude=1}] (a1) -- node[auto,swap] {|α|} (a2);
    \node[circle,fill,inner sep=1pt,label=left:{|(a1,c1)|}] (b1) at (-.5,5) {};
    \node[circle,fill,inner sep=1pt,label=right:{|(a2,c2)|}] (b2) at (.5,5) {};
    \draw[decorate,decoration={snake,amplitude=1}] (b1) -- node[auto]
         {|pair α γ|} (b2);
  \end{tikzpicture}
\end{center}

(The path pairing |pair α γ| will be made precise when we discuss |Σ|
types below.)

\subsection{Implementation}

The above discussion shows that |PathOver C α c1 c2| need not be an
extension of type theory, because it can be implemented, for example, by
|Path{C a2} (transport C α c1) c2|.  However, for engineering reasons,
in Agda, we prefer to define it as an inductive family, because then we
can eliminate on a path over using Agda's support for pattern matching,
which is more convenient that invoking the elimination form directly.
This is justified because the inductive family definition of |PathOver C
α c1 c2| can be implemented as |Path{C a2} (transport C α c1) c2| in a
strong sense, in that its inductive family elimination rule
\begin{code}
PathOver-elim : {A : Type} (C : A → Type) {a1 : A} {c1 : C a1}
  → (C :  {a2 : A} (α : Path a1 a2) (c2 : C a2) 
           → PathOver C α c1 c2 → Type)
  → C a1 id c1 id
  → {a2 : Δ} (α : Path a1 a2) {c2 : C a2}
     (γ : PathOver C α c1 c2)
  → C a2 α c2 γ 
PathOver-elim A {a1}{c1} C b .a1 id .M1 id = b
\end{code}
not only holds, but satisfies its β-reduction rule definitionally.  So
we work with a new inductive family in Agda, but everything we do could
be translated to statements about homogeneous paths using |transport|.  

NOTE: or do hott/agda path-induction into universe

\subsection{Library}

Next, we give a sample of some of the facts about path-overs that are
commonly used.  As a first example, we can compose two path-overs,
yielding a path over the composite (we write |∘o| for composition of
path-overs, and |∘| for composition of homogeneous paths):

\begin{code}
  _∘o_ :  {A : Type} {C : A → Type} {a1 a2 a3 : A}
         {α2 : Path a2 a3} {α1 : Path a1 a2}
         {c1 : C a1} {c2 : C a2} {c3 : C a3}
         (γ2 : PathOver C α2 c2 c3)
         (γ1 : PathOver C α1 c1 c2)
         → PathOver C (α2 ∘ α1) c1 c3
  id ∘o id = id
\end{code}
The proof is immediate by path-over induction, which we notate in Agda
by pattern-matching |γ1| and |γ2| as reflexivity.  

%% For this first example, it is instructive to look at what the
%% corresponding statement is if we reduce path-over to |transport|.  For
%% the same variables, we need
%% \begin{code}
%%          Path (transport C α2 c2) c3 
%%          → Path (transport C α1 c1) c2
%%          → Path (transport C (α2 ∘ α1) c1) c3
%% \end{code}

Next, we can invert a path-over, yielding a path over the inverse in the
base (for the paper, we sometimes elide the quantifiers, with the
convention that the variables are universally quantified with the most
general types):
\begin{code}
  !o : PathOver C α c1 c2 → PathOver C (! δ) c2 c1
  !o id = id
\end{code}

Applying a dependent function to a homogeneous path gives a path over
it:
\begin{code}
apdo :  {A : Type} {C : A → Type} (f : (a : A) → C a)
        {a1 a2 : A} (α : Path a1 a2)
        → PathOver C α (f a1) (f a2)
apdo f id = id
\end{code}
(The same |apdo| is for ``dependent |ap| producing a path-over''.)

Next, we define the pairing of paths discussed above: A path in a
|Σ|-type can be constructed by pairing together a path between the
left-hand sides and a path over it between the right-hand sides:
\begin{code}
pair= :  {A : Type} {B : A → Type} {a1 a2 : A} (α : Path a1 a2) 
         {b1 : A a1} {b2 : A a2} (β : PathOver B α b1 b2)
         → Path (a1 , b1) (a2 , b2)
pair= .id id = id
\end{code}
In fact, this is an equivalence, with inverse given by |ap fst| and
|apdo snd|---these three behave like introduction and elimination rules
for paths in a Σ-type.

We have the equivalence mentioned above between |PathOver| (defined as
an inductive family) and a homogeneous equation using |transport|:
\begin{code}
hom-to-over/left-eqv : {A : Type} {C : A → Type}
  → ∀ {a1 a2} {α : Path a1 a2} → ∀ {c1 c2} 
  → (Path (transport C α a1) a2) ≃ (PathOver C α c1 c2)
\end{code}
In the special case where |α| is |id|, we have that paths over
reflexivity are the same as paths:
\begin{code}
hom-to-over-eqv : {A : Type} {C : A → Type}
            → ∀ {a1} → ∀ {c1 c2 : C a1} 
            → (Path{C a1} c1 c2) ≃ (PathOver C id c1 c2)
\end{code}

Next, we have lemmas characterizing path-overs based on the dependent
type |C|; these are analogous to the rules for |transport| in each
dependent type.  First, a path-over in a constant fibration is the same
as a homogeneous path:

\begin{code}
PathOver-constant-eqv : 
  {A : Type} {C : Type} {a1 a2 : A}
  {α : Path a1 a2} {c1 : C} {c2 : C} 
  → (PathOver (λ _ → C) δ M1 M2) ≃ (Path c1 c2)
\end{code}
Here we write ≃ for type equivalence.  

Second, a path-over in a (function) composition can be re-associated,
moving part of the fibration into the path (the special case where |A|
is |(λ X → X)| is the equivalence between |HEq| and |PathOver| mentioned
above).
\begin{code}
over-o-ap-eqv :  {A B : Type} (C : B → Type) {f : A → B} 
                 {a1 a2 : A} {α : a1 == a2}  → ∀ {c1 c2} →
                 → (PathOver (C o f) α c1 c2) ≃ (PathOver C (ap f α) c1 c2)
\end{code}
This is the path-over equivalent of re-associating between
|transport (C o f) α| and |transport C (ap f α)|.  

\begin{code}
  PathOverΠ-eqv : {Δ : Type} {A : Δ → Type} {B : Σ A → Type}
              → {θ1 θ2 : Δ} {δ : θ1 == θ2} {f : (x : A θ1) → B (θ1 , x)} {g : (x : A θ2) → B (θ2 , x)}
              → Equiv (PathOver (\ θ → (x : A θ) → B (θ , x)) δ f g)
                      (((x : A θ1) (y : A θ2) (α : PathOver A δ x y) → PathOver B (pair= δ α) (f x) (g y)))

  PathOverΠ-NDdomain : {Δ : Type} {A : Type} {B : Δ → A → Type}
              → {θ1 θ2 : Δ} {δ : θ1 == θ2} {f : (x : A) → B θ1 x} {g : (x : A) → B θ2 x}
              →  PathOver (\ θ → (x : A) → B θ x) δ f g 
              == ( (x : A) → PathOver (\ θ → B θ x) δ (f x) (g x))
\end{code}
