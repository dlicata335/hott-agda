
%include agda.fmt

\section{Squares}
\label{sec:square}

To understand the rule for path-over in a path type, it is helpful
to generalize from the above example to
\begin{code}
PathOver (\ x → Path (f x) (g x)) α β1 β2 
\end{code}
where |f g : A → B| and |α : Path{A} a1 a2| and |β1 : Path (f a1) (g
a1)| and |β2 : Path (f a2) (g a2)|.  The key idea is that this data
naturally fits into a square as follows:

\begin{center}
\begin{tikzpicture}
  \coordinate (ul) at (0,1);
  \coordinate (bl) at (0,0);
  \coordinate (br) at (1,0);
  \coordinate (ur) at (1,1);

  \node[circle,draw,inner sep=1.5pt,label=left:{|f a1|}] (base) at (ul) {};
  \node[circle,draw,inner sep=1.5pt,label=left:{|f a2|}] (base) at (bl) {};
  \node[circle,draw,inner sep=1.5pt,label=right:{|g a1|}] (base) at (ur) {};
  \node[circle,draw,inner sep=1.pt,label=right:{|g a2|}] (base) at (br) {};
  \draw (ul) to node[above] {|ap f α|} (ur);
  \draw (bl) to node[below] {|ap g α|} (br);
  \draw (ul) to node[left] {|β1|} (bl);
  \draw (ur) to node[right] {|β2|} (br);
\end{tikzpicture}
\end{center}

\subsection{Definition}

Given points and paths that form a square
\begin{center}
\begin{tikzpicture}
  \coordinate (ul) at (0,1);
  \coordinate (bl) at (0,0);
  \coordinate (br) at (1,0);
  \coordinate (ur) at (1,1);

  \node[circle,draw,inner sep=1.5pt,label=left:{|a00|}] (base) at (ul) {};
  \node[circle,draw,inner sep=1.5pt,label=left:{|a01|}] (base) at (bl) {};
  \node[circle,draw,inner sep=1.5pt,label=right:{|a10|}] (base) at (ur) {};
  \node[circle,draw,inner sep=1.pt,label=right:{|a11|}] (base) at (br) {};
  \draw (ul) to node[above] {|t|} (ur);
  \draw (bl) to node[below] {|b|} (br);
  \draw (ul) to node[left] {|l|} (bl);
  \draw (ur) to node[right] {|r|} (br);
\end{tikzpicture}
\end{center}
we would like to define a type |Square l t b r|, where an element of
this type represents the inside of such a square.  One possible
definition is as path-over in a path type:
\begin{code}
PathOver (\ (x:A,y:A) → Pair x y) (pair-line t b) l r
\end{code}
where |pair-line| is a non-dependent version of |pair=| for |A × B|,
which takes two homogeneous paths.  
Another is as a disc (path-between-paths) between composites |Path (l ·
b) (t · r)|.  We can also define a new inductive family
dependent on four points, which we make implicit arguments, and four
lines, representing squares:
\begin{code}
data Square {A : Type} {a00 : A} : {a01 a10 a11 : A}
      : Path a00 a01 → Path a00 a10 → 
        Path a01 a11 → Path a10 a11 → Type where 
  id : Square id id id id
\end{code}

All of these types are equivalent:
\begin{enumerate}
\item The inductive family |Square l t b r|
\item |Path (l · b) (t · r)|
\item |PathOver (\ (x:A,y:A) → Path x y) (pair= t b) l r|
\item A definition by path-induction:
\begin{code}
Square l id id r = Path l r
\end{code}
\end{enumerate}
The second definition again satisfies the inductive family elimination
rule with a judgemental β rule, so in Agda we use the inductive family
for convenience but think of it as a derived notion semantically.

\subsection{Library}

Next, we develop some operations on squares.  We have the equivalence
with discs, and the equivalence between path-overs in a path type and
certain squares:

\begin{code}
square-disc-eqv : Square l t b r ≃ Path (l · b) (t · r)
\end{code}

\begin{code}
PathOver-=-eqv : {A B : Type} {f g : A → B}
  {a1 a2 : A} {α : Path a1 a2}
  {β1 : Path (f a1) (g a1)} {β2 : Path (f a2) (g a2)}
  → (PathOver (\ x → Path (f x) (g x)) α β1 β2)
  ≃ (Square β1 (ap f α) (ap g α) β2)
\end{code}
This equivalence includes maps into and out of a path-over in a path
type, which we will write as |in-PathOver=| and |out-PathOver=|; 
we use the
|in-| and |out-| notation analogously for other equivalences.

For a given path, there are horizontal and vertical reflexivity squares,
with reflexivity paths in the other dimension:
\begin{code}
hrefl-square :  {A : Type} {a00 a01 : A} 
  {p : Path a00 a01} → Square p id id p

vrefl-square :  {A : Type} {a00 a01 : A}
  {p : Path a00 a01} → Square id p p id
\end{code}

\begin{center}
\begin{tikzpicture}
  \coordinate (ul) at (0,1);
  \coordinate (bl) at (0,0);
  \coordinate (br) at (1,0);
  \coordinate (ur) at (1,1);
  \coordinate (c) at (0.5,0.5);

  \node[label] (node) at (c) {|hrefl|};
  \draw (ul) to node[above] {|id|} (ur);
  \draw (bl) to node[below] {|id|} (br);
  \draw (ul) to node[left] {|p|} (bl);
  \draw (ur) to node[right] {|p|} (br);
\end{tikzpicture}
\qquad
\begin{tikzpicture}
  \coordinate (ul) at (0,1);
  \coordinate (bl) at (0,0);
  \coordinate (br) at (1,0);
  \coordinate (ur) at (1,1);
  \coordinate (c) at (0.5,0.5);

  \node[label] (node) at (c) {|vrefl|};
  \draw (ul) to node[above] {|p|} (ur);
  \draw (bl) to node[below] {|p|} (br);
  \draw (ul) to node[left] {|id|} (bl);
  \draw (ur) to node[right] {|id|} (br);
\end{tikzpicture}
\end{center}

We can apply a function to a square, yielding a square between the
action of the function on each side:
\begin{code}
ap-square : {A B : Type} (f : A → B) 
  {a00 a01 a10 a11 : A} {l : Path a00 a01} 
  {t : Path a00 a10} {b : Path a01 a11} {r : Path a10 a11}
  → Square l t b r → Square (ap f l) (ap f t) (ap f b) (ap f r)
\end{code}
%% If we think of the square as a disc |s : Path (l · b) (t · r)|, then
%% |ap-square| is like |ap (ap f) s| (iterated |ap|) along with moving |ap
%% f| inside the composities.

We have rules for introducing and eliminating squares in each type.  For
example, for |A × B|, we can pair a square in |A| with a square in |B|
to get a square in |A × B|, whose boundary sides are the pairs of the
sides of the given squares::
\begin{code}
pair-line  : Path{A} a0 a1 → Path{B} b0 b1
           → Path (a0,a1) (b0,b1)

pair-square : 
  Square{A} la ta ba ra → Square{B} lb tb bb rb
  → Square  (pair-line la lb) (pair-line ta tb)
            (pair-line ba bb) (pair-line ra rb) 
\end{code}

Because |Square| is a dependent type, by path induction we can
``retype'' the sides of a square by paths-between-paths:
\begin{code}
whisker-square : {A : Type} {a00 a01 a10 a11 : A} 
  {l l' : Path a00 a01} {t t' : Path a00 a10}
  {b b' : Path a01 a11} {r r' : Path a10 a11}
  (ll : Path l l') (tt : Path t t') (bb : Path b b') (rr : Path r r')
  (s : Square l t b r) → Square l' t' b' r'
\end{code}

\noindent This creates a new square that is the composite of the
original square |s| with these paths:
\begin{center}
\begin{tikzpicture}
  \coordinate (ul) at (0,1);
  \coordinate (bl) at (0,0);
  \coordinate (br) at (1,0);
  \coordinate (ur) at (1,1);

  \draw (ul) arc (180:0:0.5cm) ; 
  \draw (ul) arc (90:270:0.5cm) ; 
  \draw (bl) arc (180:360:0.5cm) ;
  \draw (ur) arc (90:-90:0.5cm); 

  \node at (0.5,0.5) {|s|};
  \draw (ul) to node[above] {|tt|} (ur);
  \draw (bl) to node[below] {|bb|} (br);
  \draw (ul) to node[left] {|ll|} (bl);
  \draw (ur) to node[right] {|rr|} (br);

\end{tikzpicture}
\end{center}

We can compose squares vertically and horizontally:
\begin{code}
  _·-square-v_ : Square l t b r → Square l' b b' r'
    → Square (l · l') t b' (r · r')

  _·-square-h_ : Square l t b r → Square r t' b' r'
    → Square l (t · t') (b · b') r'
\end{code}
For example, |s1 ·-square-h s2| represents the composite
\begin{center}
\begin{tikzpicture}
  \coordinate (ul) at (0,1);
  \coordinate (bl) at (0,0);
  \coordinate (br) at (1,0);
  \coordinate (ur) at (1,1);

  \node at (0.5,0.25) {|s1|};
  \draw (ul) to node[above] {|t|} (ur);
  \draw (bl) to node[below] {|b|} (br);
  \draw (ul) to node[left] {|l|} (bl);
  \draw (ur) to node[right] {|r|} (br);

  \coordinate (ul') at (1,1);
  \coordinate (bl') at (1,0);
  \coordinate (br') at (2,0);
  \coordinate (ur') at (2,1);

  \node at (1.5,0.25) {|s2|};
  \draw (ul') to node[above] {|t'|} (ur');
  \draw (bl') to node[below] {|b'|} (br');
  \draw (ur') to node[right] {|r'|} (br');
\end{tikzpicture}
\end{center}

%% We can also invert two of the sides of a square, flipping the others:
%% \begin{code}
%% !-square-h : Square l t b r → Square r (! t) (! b) l
%% !-square-v : Square l t b r → Square (! l) b t (! r) 
%% \end{code}

Symmetry interchanges the horizontal and vertical sides:
\begin{code}
square-symmetry-eqv : Square l t b r ≃ Square t l r b
\end{code}
\begin{center}
\begin{tikzpicture}
  \coordinate (ul) at (0,1);
  \coordinate (bl) at (0,0);
  \coordinate (br) at (1,0);
  \coordinate (ur) at (1,1);

  \draw (ul) to node[above] {|t|} (ur);
  \draw (bl) to node[below] {|b|} (br);
  \draw (ul) to node[left] {|l|} (bl);
  \draw (ur) to node[right] {|r|} (br);

  \coordinate (ul') at (2,1);
  \coordinate (bl') at (2,0);
  \coordinate (br') at (3,0);
  \coordinate (ur') at (3,1);

  \node at (1.5,0.5) {|≃|};

  \draw (ul') to node[above] {|l|} (ur');
  \draw (bl') to node[below] {|r|} (br');
  \draw (ul') to node[left] {|t|} (bl');
  \draw (ur') to node[right] {|b|} (br');
\end{tikzpicture}
\end{center}

%% The diagonal of a |Square l t b r| can be defined to be the |l · b| or
%% |t · r| composite, or symmetrically by square induction:
%% \begin{code}
%% diag-square : {A : Type} {a00 a01 a10 a11 : A} 
%%   {l : Path a00 a01} {t : Path a00 a10}
%%   {b : Path a01 a11} {r : Path a10 a11}
%%   → Square l t b r → Path a00 a11
%% diag-square id = id
%% \end{code}

%% A connection square is a square
%% \begin{center}
%% \begin{tikzpicture}
%%   \coordinate (ul) at (0,1);
%%   \coordinate (bl) at (0,0);
%%   \coordinate (br) at (1,0);
%%   \coordinate (ur) at (1,1);

%%   \draw (ul) to node[above] {|id|} (ur);
%%   \draw (bl) to node[below] {|p|} (br);
%%   \draw (ul) to node[left] {|id|} (bl);
%%   \draw (ur) to node[right] {|p|} (br);
%% \end{tikzpicture}
%% \end{center}

%% \begin{code}
%% connection :  ∀ {A a0 a1} {p : Path{A} a0 a1}
%%               → Square id id p p 
%% connection id = id
%% \end{code}

Another operation we will need is \emph{Kan
  filling}~\citep{kan55cubical}.  For squares, this says that given any
three sides, we can find a fourth that fits in a square.  For example:
\begin{code}
fill-square-right :  {A : Type} {a00 a01 a10 a11 : A}
  (l : Path a00 a01) (t : Path a00 a10) (b : Path a01 a11)
  → Σ[ r : Path a10 a11] Square l t b r
\end{code}

\begin{center}
\begin{tikzpicture}
  \coordinate (ul) at (0,1);
  \coordinate (bl) at (0,0);
  \coordinate (br) at (1,0);
  \coordinate (ur) at (1,1);

  \draw (ul) to node[above] {|t|} (ur);
  \draw (bl) to node[below] {|b|} (br);
  \draw (ul) to node[left] {|l|} (bl);

  \coordinate (ul') at (2,1);
  \coordinate (bl') at (2,0);
  \coordinate (br') at (3,0);
  \coordinate (ur') at (3,1);

  \node at (1.5,0.5) {→};

  \node at (2.5,0.5) {|fill|};
  \draw (ul') to node[above] {|t|} (ur');
  \draw (bl') to node[below] {|b|} (br');
  \draw (ul') to node[left] {|l|} (bl');
  \draw[dashed] (ur') to node[right] {|r|} (br');
\end{tikzpicture}
\end{center}
Though both the groupoid structure (identity, composition, inverses, the
groupoid laws) and the Kan filling result from path induction, it is
illustrative to construct them directly from each other.  To derive the
Kan filler, we can define the right side |r| to be |! t · l · b|, and
then, as a disc between composites, the required square is a |Path (l ·
b) (t · (! t · l · b))| using the groupoid laws. From the Kan filling we
can define |p · q| as |fst (fill p id q)|, and then use |snd (fill p id
q)| to show the groupoid laws.
%% In the Agda library,
%% we have composition defined directly by path induction, rather than as a
%% filler, but we nonetheless have a path
%% \begin{code}
%% ·-fill : Path (p · q) (fst (fill-right p id q))
%% \end{code}

\subsection{Example: Circle induction, continued}

Returning to the example from Section~\ref{sec:circleexample}, we need a
\begin{code}
PathOver (\ a → Path base a) loop (loop^ x) (loop^ (x + 1))
\end{code}
By |PathOver-=-eqv|, this is the same as a 
\begin{code}
Square  (loop^ x) (ap (\ _ → base) loop)
        (ap (\ a → a) loop) (loop^ (x + 1))
\end{code}
After reducing the |ap|'s using |whisker-square|, we need a
\begin{code}
Square (loop^ x) id loop (loop^ (x + 1))
\end{code}
But |loop^(x+1)| is defined to be |loop^x · loop|, so we need a 
\begin{code}
Square (loop^ x) id loop (loop^ x · loop)
\end{code}
which is the characterization of composition as a Kan filler.

\subsection{Square over a square}

Just as we had a type for a path in a dependent type over a path in the base,
it will be useful to have a type of squares in a dependent type over a square
in the base:
\begin{code}
data SquareOver {A : Type} (B : A → Type) 
  {a00 : A} {b00 : B a00} : {a01 a10 a11 : A} 
  {αl : Path a00 a01} {αt : Path a00 a10}
  {αb : Path a01 a11} {αr : Path a10 a11}
  (s  : Square αl αt αb αr)
  {b01 : B a01} {b10 : B a10} {b11 : B a11}  
  (βl : PathOver B αl b00 b01)
  (βt : PathOver B αt b00 b10)
  (βb : PathOver B αb b01 b11)
  (βr : PathOver B αr b10 b11)
  → Type where
   id : SquareOver B id id id id id
\end{code}
A |SquareOver B f βl βt βb βr| relates four path-overs, each of which
lays over one side of the square |s| (the boundary of |s| and the points
in |B| are implicit arguments). Visually, an element of this type is the
inside of the top square in the following:
\begin{center}
\begin{tikzpicture}[scale=0.65]
  \coordinate (A) at (0,3);
  \coordinate (B) at (2,3);
  \coordinate (C) at (3,2);
  \coordinate (D) at (3,0);
  \coordinate (E) at (2,1);
  \coordinate (F) at (0,1);
  \coordinate (G) at (1,0);
  \coordinate (H) at (1,2);

  \node at (4,2.5) {|B|};
  \node at (4,0.5) {|A|};
  \draw[->] (4,2.25) to node[right]{} (4,0.75);

  \node at (1.5,0.5) {|s|};

  \draw (A) to node[above] {|βt|} (B);
  \draw (B) to node[right] {|βr|} (C);
  \draw (A) to node[left] {|βl|} (H);
  \draw (H) to node[below] {|βb|} (C);

  \draw (F) to node[above] {|αt|} (E);
  \draw (F) to node[left] {|αl|} (G);
  \draw (G) to node[below] {|αb|} (D);
  \draw (E) to node[right] {|αr|} (D);
\end{tikzpicture}
\end{center}

To avoid introducing a new inductive family, we could define square-over
by square induction, saying that a square over |id| is a homogeneous
square.  Alternatively, it can be defined as a higher disc directly,
using several |transport|s.

\subsection{Example: Torus}

The torus is generated by a point constructor, two path constructors,
and a square whose opposite sides are identified:
\begin{code}
a : T
p : Path a a
q : Path a a
f : Square p q q p
\end{code}

A simply-typed function from the torus is defined by giving the image of
each constructor:
\begin{code}
T-rec :  {C : Type} (a' : C) (p' q' : Path a a) (f' : Square p' q' q' p')
         → T → C
\end{code}
The dependent elimination rule is analogous, but the image of each
constructor lays over that constructor:
\begin{code}
T-elim : (C : T → Type) (a' : C a) 
         (p' : PathOver C p a' a') (q' : PathOver C q a' a')
         (f' : SquareOver C f p' q' q' p') 
         (x : T) → C x
\end{code}

For contrast, writing out the type of |T-elim| using homogeneous paths
directly gives
\begin{code}
T-elim : (C : T → Type) (a' : C a) 
  (p' : Path (transport C p a') a')
  (q' : Path (transport C q a') a')
  (f' : Path  (transport  (λ x → Path (transport C x a') a') f 
                ((transport-· C p q) · (ap (transport C q) p') · q'))
              ((transport-· C q p) · (ap (transport C p) q') · p')) 
  → (x : T) → C x
\end{code}
and, in the absence of the square-over abstraction, this proved
difficult to apply.

When we prove that the torus is equivalent to the product of two
circles, we will define functions |c2t| and |t2c|, and then use |T-elim|
to prove |(x : T) → Path (c2t (t2c x)) x|.  This means that the
induction formula |C| will itself be a path type, so for the |f'| goal,
we will need to give a |SquareOver| in a path type.  Just as a path-over
in a path type is a square, a |SquareOver| in a path type is a
3-dimensional cube.



