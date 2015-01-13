%include agda.fmt

\section{Heterogeneous equality}
\label{sec:heq}

The equality type that we write as |Path{A} a0 a1| is sometimes called
\emph{homogeneous equality}, because it relates two elements |a0| and
|a1| of the same type |A| (where ``same'' here means
definitional/judgemental equality).  McBride~\citep{mcbride00thesis}
introduced a \emph{heterogeneous equality}, which is an equality type
|a:A = b:B| that relates two elements |a:A| and |b:B| which may
have two different types, though it is inhabited only when both
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
induction or |HEq-elim|: keeping the evidence that the equation type
checks ``off to the side'' is equivalent to embedding it in the equation
on either side, and to the more symmetric fourth option.  What we will
argue in this paper is that it is useful to think in terms of ``off to
the side'' abstractions, even though they can be implemented in terms of
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
HEq  (Vec Nat (n + m)) (Vec Nat (m + n))
     (ap (Vec Nat) (+-comm m n)) v1 v2
\end{code}
where |v1 : Vec Nat (n + m)| and |v2 : Vec Nat (m + n)|.  In this case,
both |A| and |B| have the form |Vec Nat -|, and the reason why the two
types are equal is essentially commutativity of addition---but we need
to use use |ap|, which is congruence of equality, to apply |Vec Nat| to
both sides of the commutativity equality.

Heterogeneous equalities of this form can be simplified using a
\emph{factored} hetereogeneous equality type, which separates a context
(like |Vec Nat -|) from an equality on the insides of the context.  This
is called a \emph{path over a path} or \emph{path-over} type (it is
discussed briefly in \citep{uf13hott-book}), and it can be defined as an
inductive family as follows:
\begin{code}
data PathOver  {A : Type} (C : A → Type) {a1 : A} : 
               {a2 : A} (α : Path a1 a2)
               (c1 : C a1) (c2 : C a2) → Type where
  id : {c1 : C a1} → PathOver C id c1 c1
\end{code}
%% data PathOverAPath  {A : Type} (C : A → Type) (a1 : A) : 
%%                (a2 : A) (α : Path a1 a2)
%%                (c1 : C a1) (c2 : C a2) → Type where
%%   idOver : {c1 : C a1} → PathOverAPath C a1 a1 id c1 c1
That is, given a type |A| and two points |a1,a2| connected by a path
|α|, along with a dependent type |C : A → Type|, this type relates an
element of |C a1| to an element of |C a2|.  Because they can typically
be inferred, we make |a1| and |a2| implicit arguments. The constructor
|id| (note the use of constructor overloading) represents
\emph{reflexivity over reflexivity}, and says that any reflexive
equation where α is also reflexivity holds.  Using path-over, the
above example is written
\begin{code}
PathOver (Vec Nat) (+-comm m n) v1 v2
\end{code}
The context |C| is |Vec Nat|, which is morally applied to |n+m| to get
the type of |v1|, to |m+n| to get the type of |v2|, and to |+-comm m n|
to get the proof that the two types are equal.

%% Using implicit arguments (the path α usually provides enough information
%% to infer its endpoints) and constructor overloading (Agda can infer
%% whether |id| is constructing a path or a path-over-a-path, though we
%% will sometimes write |idOver| for clarity), we can shorten this
%% definition to
%% \begin{code}
%% data PathOver  {A : Type} (C : A → Type) {a1 : A} : 
%%                {a2 : A} (α : Path a1 a2)
%%                (c1 : C a1) (c2 : C a2) → Type where
%%   id : {c1 : C a1} → PathOver C id c1 c1
%% \end{code}
%% The example becomes a concise

Because types are elements of a universe, |HEq A B α a1 a2| is the
special case of |PathOver (λ (X : Type) → X) α a1 a2| (though this goes
up a universe size level).  Conversely, |PathOver| can be expressed in
terms of heterogeneous equality using |ap| as above.  Indeed, the
following types are equivalent:

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

We have experimented with two implementations of path-over in two
different Agda libraries.  In one library, it is defined as in the fifth
option above (by path induction into the universe).  In another library,
it is defined as inductive family, which is useful because allows us to
eliminate on a path-over using Agda's support for pattern matching.
Moreover, this implementation does not really require an extension of
the type theory with a new type constructor, because the inductive
family definition of |PathOver C α c1 c2| can be implemented as |Path{C
  a2} (transport C α c1) c2| in a strong sense, in that its inductive
family elimination rule
%% \begin{code}
%% PathOver-elim : {A : Type} (C : A → Type) {a1 : A} {c1 : C a1}
%%   → (C :  {a2 : A} (α : Path a1 a2) (c2 : C a2) 
%%            → PathOver C α c1 c2 → Type)
%%   → C a1 id c1 id
%%   → {a2 : Δ} (α : Path a1 a2) {c2 : C a2}
%%      (γ : PathOver C α c1 c2)
%%   → C a2 α c2 γ 
%% PathOver-elim A {a1}{c1} C b .a1 id .M1 id = b
%% \end{code}
not only holds, but satisfies its β-reduction rule definitionally.
Therefore, assuming that everything in Agda could be translated to
eliminators (following~\citep{jesper}), the eliminator for path-over
could then be replaced by statements about homogeneous paths.

\subsection{Library}

Next, we give a sample of some of the facts about path-overs that are
commonly used.  For the paper, we sometimes elide universal quantifiers,
with the convention that variables are quantified with the most general
types; the proofs proofs are in the companion code.  We write ≃ for type
equivalence.

As a first example, we can compose two path-overs, yielding a path over
the composite (we write |·o| for composition of path-overs, and |·| for
composition of homogeneous paths in diagrammatic order):

\begin{code}
  _·o_ :  {A : Type} {C : A → Type} {a1 a2 a3 : A}
         {α2 : Path a2 a3} {α1 : Path a1 a2}
         {c1 : C a1} {c2 : C a2} {c3 : C a3}
         (γ2 : PathOver C α2 c2 c3) (γ1 : PathOver C α1 c1 c2)
         → PathOver C (α1 · α2) c1 c3
  id ·o id = id
\end{code}
The proof is immediate by path-over induction, which we notate in Agda
by pattern-matching |γ1| and |γ2| as reflexivity.  

Next, we can invert a path-over, yielding a path over the inverse in the
base :
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
(The name |apdo| is for ``dependent |ap| producing a path-over''.)

Next, we define the pairing of paths discussed above: A path in a
|Σ|-type can be constructed by pairing together a path between the
left-hand sides and a path over it between the right-hand sides:
\begin{code}
pair= :  {A : Type} {B : A → Type} 
         {a1 a2 : A} (α : Path a1 a2) 
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
This implies that we have the usual homogeneous path induction for
path-overs that happens to be homogeneous (|PathOver C id c1 c2|):
\begin{code}
path-induction-homo : 
  {A : Type} {C : A → Type} {a1 : A} {c1 : C a1} 
  (P : (x : C a1) → PathOver C id c1 x → Type)
  (C c1 id) {c2 : C a1} (γ : PathOver C id c1 c2) → P c2 γ
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

Second, a path-over in a (function) composition can be re-associated,
moving part of the fibration into the path (the special case where |A|
is |(λ X → X)| is the equivalence between |HEq| and |PathOver| mentioned
above).
\begin{code}
over-o-ap-eqv :  {A B : Type} (C : B → Type)
  {f : A → B} {a1 a2 : A} {α : Path a1 a2}
  {c1 : C a1} {c2 : C a2} → 
  (PathOver (C o f) α c1 c2) ≃ (PathOver C (ap f α) c1 c2)
\end{code}
This is the path-over equivalent of re-associating between |transport (C
o f) α| and |transport C (ap f α)|.  When defining the right-to-left
direction (and proving the corresponding composite), we cannot do
path-over induction on the proof of |(PathOver C (ap f α) c1 c2)|
because it is not a fully general instance of the family.  Instead, we
do path induction on |α|, and then use |path-induction-homo|.

Third, we have rules for each type constructor.  For example for
Π-types, we have
\begin{code}
PathOverΠ-eqv : {A : Type} {B : A → Type} {C : Σ B → Type}
  {a1 a2 : A} {α : Path a1 a2} 
  {f : (x : B a1) → C (a1 , x)} {g : (x : B a2) → C (a2 , x)} → 
     (PathOver (\ a → (x : B a) → C (a , x)) α f g)
  ≃  ((x  : B a1)  (y : B a2) (β : PathOver B α x y) → 
          PathOver C (pair= α β) (f x) (g y))
\end{code}
This is a path-over version of function extensionality; it says that two
functions are equal (over α) if they take two equal arguments
(over α) to two equal results (over both α and β, because |f x : C
(a1,x)| and |g y : C(a2,y)|).  This can be proved using the usual
function extensionality for homogeneous paths.  

\subsection{Example: Circle Elimination}

For the circle type |S¹|, with constructors |base : S¹| and |loop :
Path{S¹} base base|, the elimination rule is
\begin{code}
S¹-elimo :  (C : S¹ → Type) (b : C base) (l : PathOver C loop c c) 
              → (x : S¹) → C x
S¹-elimo C b l base ≡ b
βloop/elimo : Path (apdo (S¹-elimo C b l) loop) l
\end{code}
We write |S¹-elimo| (``|S¹| elimination with path-over'') for circle
elimination, which we will also call circle induction.  To eliminate
from the circle into a dependent type |C|, we give a point |b| in |C
base| as the image of the |base| point, and a path from |c| to itself
\emph{over the loop} as the image of |loop|.  We have a definitional
computation rule for points and a propositional computation rule for
applying the eliminator (using |apdo|) to the |loop|.  By the
equivalence between |PathOver C loop c c| and |Path (transport C loop c)
c|, these rules are equivalent to the usual ones in terms of homogeneous
path.

In the case for |loop|, we will typically ``reduce'' the
|PathOver C loop c c| goal using the type-directed moves described
above. For example, when calculating |π₁(S¹)|~\citep{ls13pi1s1}, circle
induction is used to define a function
\begin{code}
decode : (x : S¹) → Cover x → Path base x
\end{code}
where |Cover|, defined by circle induction, is the universal cover
fibration.  In this case, we apply circle elimination with |C x = Cover
x → Path base x|.  In the case for |base|, we supply a function |loop^ :
Int → Path base base| (which type checks because |Cover base| is |Int|).
In the case for |loop|, |PathOverΠ-eqv| is used to make progress on the
goal, reducing it to
\begin{code}
(x y : Cover base) (β : PathOver Cover loop x y) →
PathOver  (\ p → Path base (fst p)) (pair= loop β)
          (loop^ x) (loop^ y)
\end{code}
Because we are defining a non-dependent function, the fibration in the
result does not mention |snd p|, so using |over-o-ap-eqv| to
reassociate, and then reducing |ap fst (pair= loop β)| to |loop|, we need
to show
\begin{code}
(x y  : Cover base) (β : PathOver Cover loop x y) →
PathOver (\ a → Path base a) loop (loop^ x) (loop^ y)
\end{code}
|Cover| is defined so that |PathOver Cover loop x y| is equivalent to
|Path (x + 1) y|,
%% (using |over-o-ap-eqv|, β-reduction for S¹-elim, and
%% the fact that |PathOver (\ X -> X) (ua e) x y| is the same as the graph of the
%% equivalence |e|), so we need to show
so we need to show
\begin{code}
PathOver (\ a → Path base a) loop (loop^ x) (loop^ (x + 1))
\end{code}
For this, we need a rule for reducing |PathOver| in a |Path| type, which
we discuss next.

%% \begin{code}
%%   PathOverΠ-NDdomain : {Δ : Type} {A : Type} {B : Δ → A → Type}
%%               → {θ1 θ2 : Δ} {δ : θ1 == θ2} {f : (x : A) → B θ1 x} {g : (x : A) → B θ2 x}
%%               →  PathOver (\ θ → (x : A) → B θ x) δ f g 
%%               == ( (x : A) → PathOver (\ θ → B θ x) δ (f x) (g x))
%% \end{code}

