
%include agda.fmt

\section{Torus ≃ Product of Two Circles}
\label{sec:torus}

The main idea of the correspondence between |T| and |S¹ × S¹| is that a
|loop| in the first component of the pair corresponds to |p|, and a
|loop| in the second component to |q|.

\subsection{Torus to circles}

The map from the torus to the circles uses torus recursion:
\begin{code}
t2c : T → S¹ × S¹
t2c = T-rec  (base , base) 
             (pair-line loop id)
             (pair-line id loop)
             (pair-square hrefl-square vrefl-square)
\end{code}
This function sends the point |a| on the torus to the point
|(base,base)|.  As the images of |p| and |q|, we need two elements of
|Path{S¹ × S¹} (base,base) (base,base)|. For |p|, we pair together
|loop| on the left with reflexivity on the right; for |q|, we pair
reflexivity on the left with |loop| on the right.  Next, as the image of
|f|, we need a square 
\begin{center}
\begin{tikzpicture}
  \coordinate (ul) at (0,1);
  \coordinate (bl) at (0,0);
  \coordinate (br) at (1,0);
  \coordinate (ur) at (1,1);

  \draw (ul) to node[above] {|pair-line id loop|} (ur);
  \draw (bl) to node[below] {|pair-line id loop|} (br);
  \draw (ul) to node[left] {|pair-line loop id|} (bl);
  \draw (ur) to node[right] {|pair-line loop id|} (br);
\end{tikzpicture}
\end{center}
which is given by pairing together the squares
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
  \draw (ul) to node[left] {|loop|} (bl);
  \draw (ur) to node[right] {|loop|} (br);
\end{tikzpicture}
\qquad
\begin{tikzpicture}
  \coordinate (ul) at (0,1);
  \coordinate (bl) at (0,0);
  \coordinate (br) at (1,0);
  \coordinate (ur) at (1,1);
  \coordinate (c) at (0.5,0.5);

  \node[label] (node) at (c) {|vrefl|};
  \draw (ul) to node[above] {|loop|} (ur);
  \draw (bl) to node[below] {|loop|} (br);
  \draw (ul) to node[left] {|id|} (bl);
  \draw (ur) to node[right] {|id|} (br);
\end{tikzpicture}
\end{center}

\subsection{Circles to torus}

We define |c2t : S¹ × S¹ → T| to be the uncurrying of a map |c2t' : S¹ →
S¹ → T|.  For intuition, to be inverse to |t2c|, we would like that
|c2t'| behaves as follows when applied (using appropriate |ap|'s, which
we omit here) to constructors:
\begin{code}
c2t' base base = a
c2t' base loop = q
c2t' loop base = p
c2t' loop loop = f
\end{code}
We code matching on two arguments as nested circle eliminations, which
roughly have the form ``|S¹-elim (S¹-elim a q) (S¹-elim p f)|.''  That
is, when the first argument is |base|, we get a function that sends
|base| to |a| and |loop| to |q|; when the first argument is |loop|, we
get a function that sends |base| to |p| and |loop| to |f|.
We now make this precise:
\begin{code}
c2t-square-and-cube :
    Σ[ s : Square  p (ap (S¹-rec a q) loop)
                   (ap (S¹-rec a q) loop) p]
    Cube s f hrefl-square βsquare βsquare hrefl-square
c2t-square-and-cube = (fill-cube-left _ _ _ _ _)

c2t' : S¹ → S¹ → T
c2t' = S¹-rec  (S¹-rec a q) 
               (λ≃ (S¹-elimo _ p 
                 (in-PathOver-= (fst c2t-square-and-cube))))
\end{code}
The match on the first argument is a simply-typed circle recursion, so
we need a point and a loop in |S¹ → T|.  The point is again defined by
circle recursion, sending |base| to |a| and |loop| to |q|.  The loop
must be a |Path{S¹ → T} (S¹-rec a q) (S¹-rec a q)|, which, by
(homogeneous) function extensionality, is equivalent to |(x : S¹) → Path
(S¹-rec a q x) (S¹-rec a q x)|.  Using circle elimination, we need a
|Path{T} base base| (because |S¹-rec a q base ≡ a|), which we take to be
|p|, and then a |PathOver (\ x → Path (S¹-rec a q x) (S¹-rec a q x))
loop p p|. Applying |PathOver-=-eqv| to reduce a path-over in a path
type to a square, we need a square |s| with the type given as the first
component of |c2t-square-and-cube|.  But |(ap (S¹-rec a q) loop)|
reduces (propositionally) to |q|, and the square we want is the |f|
constructor for the torus composed with this propositional reduction.
Writing
\begin{code}
βsquare : Square (ap (S¹-rec a q) loop) id id q
\end{code}
for the reduction, it turns out to be convenient to obtain the necessary
square using Kan filling, because then we also get a cube relating |s|
to |f| along the reduction (and along reflexivity for the |p|
positions).

\subsubsection*{Reduction rules}
Next, we prove propositional reduction rules for |c2t'| on the
constructors, elaborating on the informal versions given above.  On
points, |c2t' base base| is indeed judgementally equal to |a|.  The more
precise version of the next two equations is
\begin{code}
ap (λ x → c2t' x base) loop = p
ap (λ y → c2t' base y) loop = q
\end{code}
Proving these equations will involve reducing circle eliminations on the
|loop| constructor, so they will only hold propositionally.

For the final equation, we first need to clarify how to apply |c2t'| to
the |loop| in both positions.  For any curried function |f : A → B → C|
and paths |α : Path{A} a a'| and |β : Path{B} b b'|, there is a square
\begin{center}
\begin{tikzpicture}[scale=2]
  \coordinate (ul) at (0,1);
  \coordinate (bl) at (0,0);
  \coordinate (br) at (1,0);
  \coordinate (ur) at (1,1);

  \node (uln) at (ul) {{|f a b|}};
  \node (bln) at (bl) {{|f a' b|}};
  \node (urn) at (ur) {{|f a b'|}};
  \node (brn) at (br) {{|f b b'|}};
  \draw[->] (uln) to node[left] {|ap (λ x → f x b) α|} (bln);
  \draw[->] (uln) to node[above] {|ap (λ y → f a y) β|} (urn);
  \draw[->] (bln) to node[below] {|ap (λ y → f a' y) β|} (brn);
  \draw[->] (urn) to node[right] {|ap (λ x → f x b') α|} (brn);
\end{tikzpicture}
\end{center}
defined by the iterated application of |f| to |α| and |β|:
\begin{code}
apdo-ap f α β =
  out-PathOver-= (apdo (λ y → ap (λ x → f x y) α) β)
\end{code}
To see that this type checks, for any |y|, the term |ap (λ x → f x y) α|
has type |Path (f a y) (f a' y)|, so applying this to |β| gives a
\begin{code}
PathOver  (\ y → Path (f a y) (f a' y)) β
          (ap (λ x → f x b) α) (ap (λ x → f x b') α)
\end{code}
and turning this path-over into a square gives the result.  
The specific case of |apdo-ap c2t' loop loop| is a square

\begin{center}
\begin{tikzpicture}[scale=2]
  \coordinate (ul) at (0,1);
  \coordinate (bl) at (0,0);
  \coordinate (br) at (1,0);
  \coordinate (ur) at (1,1);

  \draw (ul) to node[left] {|ap (λ x → c2t' x base) loop|} (bl);
  \draw (ul) to node[above] {|ap (λ y → c2t' base y) loop|} (ur);
  \draw (bl) to node[below] {|ap (λ y → c2t' base y) loop|} (br);
  \draw (ur) to node[right] {|ap (λ x → c2t' x base) loop|} (br);
\end{tikzpicture}
\end{center}
and note that the path reduction rules above equate the sides of this
square the sides of |f|.

Thus, the desired propositional reduction rules for |c2t'| are
\begin{code}
c2t'-β :  Σ[ βl2 : Square (ap (λ y → c2t' base y) loop) id id q ]
          Σ[ βl1 : Square (ap (λ x → c2t' x base) loop) id id p ]  
            Cube (apdo-ap c2t' loop loop) f βl1 βl2 βl2 βl1
\end{code}
This says that we want two squares for ``|c2t' base loop|'' and ``|c2t'
loop base|'', and then a cube along these squares for the reduction on
``|c2t' loop loop|''.  It will be important below that this cube's top
equals its bottom and front equals its back.

We could proceed by defining |βl2| (as |βsquare| from above, for
example) and |βl1| and then trying to find an appropriate cube for the
third component.  However, there is a simpler way: The only property we
need of the |βl1| and |βl2| squares is that they exist and fit into the
cube above.  Moreover, it turns out that we can define the cube goal in
such a way that it determines suitable |βl1| and |βl2|!  In Agda,
unification fills in |βl2| and |βl1| from the definition of the cube.

To define a cube whose left side is |(apdo-ap c2t' loop loop)| and whose
right side is |f|, we compose six cubes horizontally, whose middle sides
are as follows:
\begin{code}
    apdo-ap c2t' loop loop
≡   out-PathOver= 
       (apdo (\ y → (ap (\ x -> c2t' x y) loop)) loop)
□=  out-PathOver= 
       (apdo (\ y → (ap (\ f -> f y) (ap c2t' loop))) loop)
□=  out-PathOver= (apdo (\ y → (ap (\ f -> f y) 
       (λ≃ (  S¹-elimo _ p 
         (in-PathOver-= (fst c2t-square-and-cube)))))) loop)
□=  out-PathOver= (apdo 
       (S¹-elimo _ p 
         (in-PathOver-= (fst c2t-square-and-cube))) loop)
□=  out-PathOver= (in-PathOver-= (fst c2t-square-and-cube))
□=  fst c2t-square-and-cube
□=  f
\end{code}
We think of this as an equation chain between these eight squares, but
the proof of each step is really a cube, rather than a homogeneous path.
In order, the justifications for the steps are (0) by definition, (1)
un-fusing |ap (\ x -> c2t' x y) loop| to |ap (\ f → f y) (ap c2t'
loop)|, (2) reducing |c2t'| (which is a circle recursion) on |loop|, (3)
reducing |ap (\ f → f y)| on a function extensionality, (4) reducing
|S¹-elimo| on the loop, (5) collapsing the two sides of the |PathOver-=|
equivalence, and (6) using |snd c2t-square-and-cube|.  Thus, we do what
looks like an equational proof that the square |(apdo-ap c2t' loop
loop)| ``equals'' the square |f|, but each step may also contribute to
the back-top-bottom-front tube that connects the boundaries of these
two squares.  For example, step (6) using |snd c2t-square-and-cube|
contributes |βsquare| on the top and bottom.

The curious reader may find the the complete Agda proof in the appendix
(Figure~\ref{fig:ts1s1-full}). The important point is that the term is
simply a horizontal composition of cubes, which correspond to steps (1)
through (6) above.  The sides of the cube are represented by the |_|'s,
which are filled in by unification.  This works because each of the
cubes used in steps (1) through (6) have the property that their front
is equal to their back and their top is equal to their bottom, so |βl1|
and |βl2| can be defined to be the composites of these sides, and the
overall cube has the required boundary.

%% \begin{figure*}
%% \begin{code}
%% c2t'-β = _ , _ , 
%%   out-SquareOver-= (apdo-by-equals _ _ loop (λ≃ (\ y -> ap-o (λ f → f y) c2t' loop))) ·-cube-h
%%   out-SquareOver-= (apdo-by-equals _ _ loop 
%%      (λ≃ (\ y -> ap (ap (λ f → f y)) (βloop/rec (rec T.a T.q) (λ≃ c2t-loop-homotopy))))) ·-cube-h
%%   out-SquareOver-= (apdo-by-equals _ _ loop (λ≃ (\ y -> (Π≃β c2t-loop-homotopy)))) ·-cube-h
%%   degen-cube-h (ap PathOver=.out-PathOver-= (βloop/elimo _ T.p (PathOver=.in-PathOver-= (fst c2t-square-and-cube)))) ·-cube-h
%%   degen-cube-h (IsEquiv.β (snd PathOver=.out-PathOver-=-eqv) _) ·-cube-h 
%%   (snd c2t-square-and-cube)
%% \end{code}
%% \caption{|c2t'| reduction}
%% \label{fig:c2t'}
%% \end{figure*}

\subsection{Torus to circles to torus}

Next, we need to show
\begin{code}
t2c2t : (x : T) → Path (c2t (t2c x)) x
\end{code}
We proceed by torus induction.  In the case for |a|, the result holds
definitionally.  After a bit of massaging (using |PathOver-=| to mediate
between a path-over in a path type and a square; collapsing round-trips
of the |PathOver-=| equivalence; using |in-SquareOver-=| to create a
square-over from a cube; using |cube-symmetry-left-to-top| to put the
important faces on the left-right sides), the remaining goals are
\begin{code}
p-case : Square  (ap (λ z → c2t (t2c z)) p) id 
                 id (ap (λ z → z) p)
q-case : Square  (ap (λ z → c2t (t2c z)) q) id
                 id (ap (λ z → z) q)
f-case : Cube  (ap-square (λ z → c2t (t2c z)) f) 
               (ap-square (λ z → z) f)
               p-case q-case q-case p-case
\end{code}
This simply says that we need to check the composite on each of the
constructors, where the case for |f| is a cube along the cases for |p|
and |q|.  Once again, we can solve the |f| case and let that determine
the |p| and |q| cases.  The |f| case is a horizontal composition of
cubes whose middle faces are as follows:
\begin{code}
    ap-square (λ z → c2t (t2c z)) f
□=  ap-square c2t (ap-square t2c f)
□=  ap-square c2t (pair-square hrefl-square vrefl-square)
□=  apdo-ap c2t' loop loop 
□=  f
□=  ap-square (\ z → z) f
\end{code}
That is, we (1) un-fuse the |ap-square| using |ap-square-o|, (2) reduce
|t2c| (defined by torus recursion) on the |f| constructor, (3) change an
|ap-square| into an |apdo-ap|, (4) use the |c2t'-β| cube for |apdo-ap
c2t' loop loop|, and (5) expand |ap-square| with the identity function.
The proof is again given as a series of horizontal composites of cubes,
and the boundary of this cube solves the |p| and |q| cases:
\begin{code}
p-case = _
q-case = _
f-case =   ap-square-o c2t t2c f ·-cube-h
           ap-cube c2t βfcube ·-cube-h
           apdo-ap-cube-hv c2t' loop loop ·-cube-h 
           snd (snd c2t'-β) ·-cube-h 
           ap-square-id! f
\end{code}

In step (3), we use a cube 
\begin{code}
apdo-ap-cube-hv : Cube
      (ap-square (uncurry f) (pair-square (hrefl p) (vrefl q)))
      (apdo-ap f p q) 
      (ap-id-snd-square f p) (ap-id-fst-square f q) 
      (ap-id-fst-square f q) (ap-id-snd-square f p)
\end{code}
This lemma is an analogue of currying for applying a function to a pair
of paths: |apdo-ap f p q| (which is like ``|f p q|'') is the same as
square-applying |uncurry f| to the pair of |p| (as a horizontally
trivial square) and |q| (as a vertically trivial square).  The remaining
sides equate |ap (uncurry f) (pair-line id q)| with |ap (f a) q| and
similarly for the second component.  

In step (5), we use a |Cube s (ap-square (\ x → x) s) ...| whose
remaining sides are the paths between |ap (\ x → x) p| and |p|.

\subsection{Circles to torus to circles}

Finally, we check the other composite:
\begin{code}
c2t2c : (x y : S¹) → Path (t2c (c2t' x y)) (x , y)
\end{code}
The outer structure of the proof consists of nested circle inductions,
together with uses of function extensionality, |PathOver-=| and
|in-PathOver-Square|, some massaging (reducing an |S¹-elimo| on |loop|
and a round-trip of |PathOver=|), and (for convenience) a use of
|cube-symmetry-left-to-top|.  After applying these lemmas, the remaining
goals are
\begin{code}
loop1-case : Square  (ap (λ x → t2c (c2t' x base)) loop) id 
                     id (ap (λ x → x , base) loop)
loop2-case : Square  (ap (λ y → t2c (c2t' base y)) loop) id 
                     id (ap (\ y → base , y) loop)
looploop-case :
  Cube  (apdo-ap (\ x y → t2c (c2t' x y)) loop loop)
        (apdo-ap (\ x y → x , y) loop loop)
        loop1-case loop2-case loop2-case loop1-case
\end{code}
That is, we need to check that the theorem holds for when the composite
is applied to |loop base| and |base loop| and |loop loop|.  Once again,
we can solve the |loop loop| case and let that determine the others.
The reduction in question is a horizontal composite of cubes with the
following middle faces
\begin{code}
    apdo-ap (\ x y → t2c (c2t' x y)) loop loop
□=  ap-square t2c (apdo-ap c2t' loop loop)
□=  ap-square t2c f
□=  pair-square hrefl-square vrefl-square
□=  ap-square (\ x -> x) 
       (pair-square hrefl-square vrefl-square)
□=  apdo-ap _,_ loop loop
\end{code}

The justifications are (1) un-fuse the |apdo-ap| of a composition of a
functions (a lemma analogous to |ap-square-o|), (2) use |c2t'-β| from
above, (3) reduce the |t2c| torus elimination on |f|, (4) expand
|ap-square (\ x → x)| and (5) use |apdo-ap-cube-hv| to mediate between
an |ap-square| and a |apdo-ap|.  The proof is the composite of
these five cubes, and |loop1-case| and |loop2-case| are inferred by
unification:
\begin{code}
loop1-case = _
loop2-case = _
looploop-case =
  apdo-ap-o t2c c2t' loop loop ·-cube-h
  ap-cube t2c (snd (snd c2t'-β)) ·-cube-h
  βfcube ·-cube-h 
  ap-square-id! _ ·-cube-h 
  apdo-ap-cube-hv _,_ loop loop
\end{code}
