
%include agda.fmt

\section{Cubes}

\label{sec:cube}

Just as we had a type of squares dependent on four points and four
lines, which make up the boundary of a square, we have a type of cubes
dependent on eight points, twelve lines, and six faces: 

\begin{code}
data Cube {A : Type} {a000 : A} : 
  {a010 a100 a110 a001 a011 a101 a111 : A}
  {p0-0 : Path a000 a010} {p-00 : Path a000 a100}
  {p-10 : Path a010 a110} {p1-0 : Path a100 a110}
  (left : Square p0-0 p-00 p-10 p1-0) 
  {p0-1 : Path a001 a011} {p-01 : Path a001 a101}
  {p-11 : Path a011 a111} {p1-1 : Path a101 a111}
  (right : Square p0-1 p-01 p-11 p1-1) 
  {p00- : Path a000 a001} {p01- : Path a010 a011}
  {p10- : Path a100 a101} {p11- : Path a110 a111}
  (back : Square p0-0 p00- p01- p0-1) 
  (top : Square p-00 p00- p10- p-01) 
  (bot: Square p-10 p01- p11- p-11) 
  (front : Square p1-0 p10- p11- p1-1) 
  → Type where
  id : Cube id id id id id id
\end{code}

%% \begin{center}
%% \begin{tikzpicture}
%%   \coordinate (A) at (0,3);
%%   \coordinate (B) at (2,3);
%%   \coordinate (C) at (3,2);
%%   \coordinate (D) at (3,0);
%%   \coordinate (E) at (2,1);
%%   \coordinate (F) at (0,1);
%%   \coordinate (G) at (1,0);
%%   \coordinate (H) at (1,2);

%%   \draw (A) to node[right] {|p-00|} (H);
%%   \draw (A) to node[above] {|p00-|} (B);
%%   \draw (H) to node[above, near start] {|p10-|} (C);
%%   \draw (B) to node[right]  {|p-01|} (C);

%%   \draw (F) to node[left] {|p-10|} (G);
%%   \draw (F) to node[below, near end] {|p01-|} (E);
%%   \draw (G) to node[below] {|p11-|} (D);
%%   \draw (E) to node[right, near start] {|p-11|} (D);

%%   \draw (A) to node[left] {|p0-0|} (F);
%%   \draw (H) to node[left, near start] {|p1-0|} (G);
%%   \draw (B) to node[right, near end] {|p0-1|} (E);
%%   \draw (C) to node[right] {|p1-1|} (D);
%%   %% \draw (F) to node[above] {|p01-|} (E);
%%   %% \draw (G) to node[below] {|p11-|} (D);
%%   %% \draw (E) to node[right] {|p-11|} (D);
%% \end{tikzpicture}
%% \end{center}

An element of this type represents the inside of a cube 
\begin{center}
\begin{tikzpicture}
  \coordinate (A) at (0,3);
  \coordinate (B) at (2,3);
  \coordinate (C) at (3,2);
  \coordinate (D) at (3,0);
  \coordinate (E) at (2,1);
  \coordinate (F) at (0,1);
  \coordinate (G) at (1,0);
  \coordinate (H) at (1,2);

  \node at (3.5,1) {|right|};
  \node at (-0.5,2) {|left|};
  \node at (1.5,2.5) {|top|};
  \node at (0.5,1.5) {|back|};
  \node at (2.35,1.75) {|front|};
  \node at (0.75,0.75) {|bot|};

  \draw (A) to node[right]  {} (H);
  \draw (A) to node[above] {} (B);
  \draw (H) to node[above, near start] {} (C);
  \draw (B) to node[right] {} (C);

  \draw (F) to node[left] {} (G);
  \draw (F) to node[below, near end] {} (E);
  \draw (G) to node[below] {} (D);
  \draw (E) to node[right, near start] {} (D);

  \draw (A) to node[left] {} (F);
  \draw (H) to node[left, near start] {} (G);
  \draw (B) to node[right, near end] {} (E);
  \draw (C) to node[right] {} (D);
\end{tikzpicture}
\end{center}

We think of a |Cube left right back top bot front| as an equality
between the left and right squares, along the ``tube'' given by the
|back| and |top| and |bot| and |front|.  As usual, we could avoid
introducing a new inductive family by instead defining a cube using
square induction, to say that when the back, top, bottom, and front are
the identity squares, a cube is a three-dimensional path between the
left and the right.

Many of the lemmas about cubes are analogous to (and dependent on) those
for squares.  For example, we can compose two cubes horizontally:
\begin{code}
  _·-cube-h_ : Cube f--0 f--1 f0-- f-0- f-1- f1--
    → Cube f--1 f--2 f0--' f-0-' f-1-' f1--'
    → Cube  f--0 f--2 
            (f0-- ·-square-h f0--') (f-0- ·-square-h f-0-') 
            (f-1- ·-square-h f-1-') (f1-- ·-square-h f1--')
\end{code}

We can apply a function to a cube, to get a cube between the action of
the function on each face square:
\begin{code}
ap-cube : (f : A → B) → Cube left right back top bot front
    → Cube  (ap-square f left) (ap-square f right)
            (ap-square f back) (ap-square f top)
            (ap-square f bot) (ap-square f front)
\end{code}

There are symmetries that switch the dimensions, for example moving the
left side to the top, and rearranging and applying symmetries to the
other faces as necessary:
\begin{code}
cube-symmetry-left-to-top : 
  Cube left right back top bot front
  →  Cube  (square-symmetry back) (square-symmetry front)
           (square-symmetry top) left
           right (square-symmetry bot)
\end{code}

Next, there are Kan filling operations, which say ``any open box has a
lid, and an inside.''  For example, we can create the left side of a
cube from the other five sides:
\begin{code}
fill-cube-left : (right : Square p0-1 p-01 p-11 p1-1)
  (back : Square p0-0 p00- p01- p0-1)
  (top : Square p-00 p00- p10- p-01) 
  (bot : Square p-10 p01- p11- p-11) 
  (front : Square p1-0 p10- p11- p1-1) 
  → Σ[  left : Square p0-0 p-00 p-10 p1-0 ] 
        Cube left right back top bot front
\end{code}

Cubes arise any time a square type occurs inside a path type, or vice
versa.  For example, a square-over in a path type is equivalent to a
cube (we will only need logical equivalence):

\begin{code}
SquareOver-= :
  Cube  (out-PathOver-= q0-) (out-PathOver-= q1-)
        (out-PathOver-= q-0) (ap-square f fa)
        (ap-square g fa) (out-PathOver-= q-1)
  ↔  SquareOver (\ x -> Path (f x) (g x)) fa q0- q-0 q-1 q1-
\end{code}
Similarly, a path-over in a square type can be given by a cube:
\begin{code}
in-PathOver-Square : 
  Cube  f1 f2 
      (out-PathOver-= (apdo p0- δ)) (out-PathOver-= (apdo p-0 δ)) 
      (out-PathOver-= (apdo p-1 δ)) (out-PathOver-= (apdo p1- δ)))
  → PathOver  (\ x -> Square (p0- x) (p-0 x) (p-1 x) (p1- x))
              δ f1 f2
\end{code}

A typical use of cubes is to ``reduce'' squares up to reduction on their
boundaries.  For example, just as there is a path between |ap (g o f) p|
and |ap g (ap f p)|, we would like |ap-square (g o f) s| to be equal to
|ap-square g (ap-square f s)|.  However, the sides of these two squares
differ by the reductions on paths.  Thus, we can phrase this reduction
as a cube, which equates these two squares along the reductions between
their sides:
\begin{code}
ap-o : Square (ap (g o f) p) id id (ap g (ap f p))

ap-square-o : (s : Square l t b r) → 
  Cube  (ap-square (g o f) s) (ap-square g (ap-square f s))
        (ap-o g f l) (ap-o g f t) (ap-o g f b) (ap-o g f r)
\end{code}

\subsection{Example: Torus reduction rules}

The propositional reduction rules for torus recursion |T-rec| can be
phrased as squares and cubes.
\begin{code}
βp/rec : Square (ap (T-rec a' p' q' f') p) id id p'
βq/rec : Square (ap (T-rec a' p' q' f') q) id id q'
βf/rec : Cube  (ap-square (T-rec a' p' q' f') f) f'
               βp/rec βq/rec βq/rec βp/rec 
\end{code}
For |p| and |q| we have the usual paths, rephrased as
horizontally degenerate cubes.  For |f|, we have a cube between the
application of |T-rec| to the face constructor and the provided image
|f'|, along the previous reduction rules.  
