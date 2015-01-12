
%include agda.fmt

\section{Squares}
\label{sec:square}

To see the rule for path-over in a path fibration, it is helpful to generalize from the above example to
\begin{code}
PathOver (\ x -> Path (f x) (g x)) α β1 β2 
\end{code}
where for this to be well-typed, we need
\begin{code}
{A B : Type} {f g : A → B}
{a1 a2 : A} {α : Path a1 a2}
{β1 : Path (f a1) (g a1)}
{β2 : Path (f a2) (g a2)}
\end{code}
(In general |B| might depend on |A| and |f| and |g| might be dependently
typed, but the simply-typed case is a helpful to consider.)
The key idea is that this data naturally fits into a \emph{square} as follows:

[picture]

Thus, to reduce the path-over, we would like a type of squares.

\subsection{Definition}

We could simply define the type of squares with sides |left|, |right|,
|top|, |bottom| to be a path-over in the identity type:
\begin{code}
PathOver (\ (x:A,y:A) → Pair x y) (pair= top bottom) left right
\end{code}

Another way to represent a square is as a disc between composities: a
square with sides |left| |right| |top| and |bottom| and be represented
as a 2-dimension path |Path (left · bottom) (top · right)| (or,
equivalently, any other arragement of this equation, such as |Path bot
(! left · top · right)|).

We can also define a new inductive family (dependent on four points and
four lines) representing squares:
\begin{code}
data Square {A : Type} {a00 : A} : {a01 a10 a11 : A}
      : Path a00 a01 → Path a00 a10 → 
        Path a01 a11 → Path a10 a11 → Type where 
  id : Square id id id id
\end{code}

All of these types are equivalent:
\begin{itemize}
\item |Path (left · bottom) (top · right)|
\item |Square left top bottom right|
\item |PathOver (\ (x:A,y:A) → Path x y) (pair= top bottom) left right|
\item A definition by path-induction:
\begin{code}
Square left id id right = Path left right
\end{code}
\end{itemize}

Moreover, the first definition satisfies the inductive family
elimination rule, including a judgemental β rule, so we can treat the
inductive family definition as a derived notion.  We do this in Agda,
again so that we can use the inductive family elim via pattern matching.

\subsection{Library}

Next, we develop some operations on squares.  We have the equivalences
mentioned above between squares and discs and squares and path-overs:

\begin{code}
square-disc-eqv : Square l t b r ≃ Path (l · b) (t · r)
\end{code}

\begin{code}
out-PathOver-=-eqv : {A B : Type} {f g : A → B}
  {a1 a2 : A} {α : Path a1 a2}
  {β1 : Path (f a1) (g a1)} {β2 : Path (f a2) (g a2)}
  → (PathOver (\ x -> Path (f x) (g x)) α β1 β2)
  ≃ (Square β1 (ap f α) (ap g α) β2)
\end{code}

For a given path, there are horizontal and vertical reflexivity squares,
with reflexivity paths in the other dimension:
\begin{code}
hrefl-square :  {A : Type} {a00 a01 : A} {p : Path a00 a01}
                → Square p id id p
vrefl-square :  {A : Type} {a00 a01 : A} {p : Path a00 a01}
                → Square id p p id
\end{code}

We can apply a function to a square, yielding a square between the
action of the function on each side:
\begin{code}
ap-square : {A B : Type} (f : A → B) {a00 a01 a10 a11 : A} 
  {l : Path a00 a01} {t : Path a00 a10}
  {b : Path a01 a11} {r : Path a10 a11}
  (s   : Square l t b r)
  → Square (ap f l) (ap f t) (ap f b) (ap f r)
\end{code}
If we think of the square as a disc |s : Path (l · b) (t · r)|, then
|ap-square| is like an iterated |ap|, |ap (ap f) s|, along with moving
|ap f| inside the composities.

We have rules for introducing and eliminating squares in each type.  For
example, for |A × B|, we can pair a square in |A| with a square in |B|
to get a square in |A × B|, whose boundary sides are the pairs of the
sides of the given squares (|pair-line| is the non-dependent version of
|pair=| from above; it takes two homogeneous paths):
\begin{code}
pair-line  : Path{A} a0 a1 → Path{B} b0 b1
           → Path (a0,a1) (b0,b1)

pair-square : 
  (sa : Square{A} la ta ba ra)
  (sb : Square{B} lb tb bb rb)
  → Square  (pair-line la lb) (pair-line ta tb)
            (pair-line ba bb) (pair-line ra rb) 
\end{code}

Because |Square| is a dependent type, we can ``adjust'' the
sides of a square by a path between paths:
\begin{code}
  whisker-square : {A : Type} {a00 a01 a10 a11 : A} 
    {l l' : Path a00 a01} {t t' : a00 a10}
    {b b' : Path a01 a11} {r r' : Path a10 a11}
    → Path l l' → Path t t' → Path b b' → Path r r'
    → Square l t b r
    → Square l' t' b' r'
\end{code}

More generally, we can compose squares vertically and horizontally
(which is like ``adjusting'' one side of a square by another
square):
\begin{code}
  _·-square-v_ : Square l t b r → Square l' b b' r'
    → Square (l · l') t b' (r · r')

  _·-square-h_ : Square l t b r → Square r t' b' r'
    → Square l (t · t') (b · b') r'
\end{code}
%% FIXME change notation?

We can also invert two of the sides of a square, flipping the others:
\begin{code}
!-square-h : Square l t b r → Square r (! t) (! b) l
!-square-v : Square l t b r → Square (! l) b t (! r) 
\end{code}

Some operations on cubes that come up in cubical sets will be useful,
such as symmetry, diagonals, and connections.  Symmetry interchanges the
axes of a square, switching the horizontal and vertical sides:
\begin{code}
square-symmetry-eqv : Square l t b r ≃ Square t l r b
\end{code}

The diagonal of a |Square l t b r| can be defined to be the |l · b| or
|t · r| composite, or symmetrically by square induction:
\begin{code}
diag-square : {A : Type} {a00 a01 a10 a11 : A} 
  {l : Path a00 a01} {t : Path a00 a10}
  {b : Path a01 a11} {r : Path a10 a11}
  → Square l t b r → Path a00 a11
diag-square id = id
\end{code}

A connection is a square with reflexivity on two sides that meet at at a
corner, and a given line on the other two coincident sides:
\begin{code}
connection : ∀ {A a0 a1} {p : Path{A} a0 a1} → Square id id p p 
connection id = id
\end{code}

Another operation we will need is \emph{Kan filling}~\citep{kan1950s}.
For squares, this says that given any three sides of a cube, we can find
a fourth that fits in a square.  For example: 
\begin{code}
fill-right :  {A : Type} {a00 a01 a10 a11 : A}
  (l : Path a00 a01) (t : Path a00 a10) (b : Path a01 a11)
  → Σ[ r : Path a10 a11] Square l t b r
fill-right id id id = (id , id)
\end{code}
The filling is defined by repeated path induction.  Though both the
groupoid structure (identity, composition, inverses, the groupoid laws)
and the Kan filling result from path induction, we can also construct
them directly from each other.  For example, to derive the Kan filler,
we can define |r| to be |! t · l · b|, and then, as a disc between
composites, the required square is a |Path (l · b) (t · (! t · l · b))|
using the groupoid laws.  Conversely, from the Kan filling we could
define |p · q| as |fst (fill p id q)|, and then |snd (fill p id q)|
is used to show the groupoid laws.  

For historical reasons, in the Agda library, we have composition defined
directly by path induction, rather than as a filler, but we nonetheless
have a path
\begin{code}
comp-fill : {A : Type} {x y z : A} (p : Path x y) (q : Path y z)
          → Path (p · q) (fst (fill-right p id q))
\end{code}



\subsection{Example: Circle induction, continued}

Returning to the example from the previous section, we were looking for a
\begin{code}
PathOver (\ a → Path base a) loop (loop^ x) (loop^ (x + 1))
\end{code}
By |out-PathOver-=-eqv|, this is the same as a square
\begin{code}
Square (loop^ x)
       (ap (\ _ → base) loop)
       (ap (\ a → a) loop)
       (loop^ (x + 1))
\end{code}
After reducing the |ap|'s using |whisker-square|, we need a
\begin{code}
Square (loop^ x) id loop (loop^ (x + 1))
\end{code}

The function |loop^| is defined so that |loop^(x+1) ≡ loop^x · loop|, so we need a square
\begin{code}
Square (loop^ x) id loop (loop^ x · loop)
\end{code}
which is exactly the characterization of composition as a Kan filler
given above.  

\subsection{Square over a square}

Just as we had a type for a path in a fibration over a path in the base,
it will be useful to have a type of squares in a fibration over a square
in the base.  As an inductive family, this is defined as:
\begin{code}
data SquareOver {A : Type} (B : A → Type) {a00 : A} 
  {b00 : B a00} : {a01 a10 a11 : A} 
  {αl : Path a00 a01} {αt : Path a00 a10}
  {αb : Path a01 a11} {αr : Path a10 a11}
  (s  : Square αl αt αb αr)
  {b01 : B a01} {b10 : B a10} {b11 : B a11}  
  (βl : PathOver B αl b00 b01) (βt : PathOver B αt b00 b10)
  (βb : PathOver B αb b01 b11) (βr : PathOver B αr b10 b11)
  → Type where
    id : SquareOver B id id id id id
\end{code}
A square-over |SquareOver B f βl βt βb βr| relates four path-overs,
each of which lays over one side of the square |s|:

[picture]

To avoid introducing a new inductive family, we could define square-over
by square induction, saying that a square over |id| is just a
homogeneous square.  Alternatively, it can be defined as a higher disc
directly, using a bunch of |transport|s.  

\subsection{Example: Torus}

The torus is generated by a point constructor, two path constructors,
and a square whose opposite sides are identified:
\begin{code}
a : T
p : Path a a
q : Path a a
f : Square p q q p
\end{code}

To give a simply-typed function from the torus into something else, you
need to give the image of each constructor:
\begin{code}
T-rec :  {C : Type} (a' : C) (p' q' : Path a a)
         (f' : Square p' q' q' p')
         → T → C
\end{code}

The full elimination rule is analogous, but the image of each
constructor lays over the constructor itself:
\begin{code}
T-elim : (C : T → Type) (a' : C a) 
         (p' : PathOver C p a' a') (q' : PathOver C q a' a')
         (f' : SquareOver C f p' q' q' p') 
         → (x : T) → C x
\end{code}

For constrast, writing out the type of |T-elim| using homogeneous paths
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
This proved hard to work with directly, using the ususal collection of
lemmas for paths.

When we prove that the torus is equivalent to the product of two
circles, we will define functions |c2t| and |t2c|, and then use |T-elim|
to prove |(x : T) → Path (c2t (t2c x)) x|.  This means that the
induction formula |C| will itself be a path type, so for the |f'| goal,
we will need to give a |SquareOver| in a path type.  Just as a path-over
in a path type is a square, a |SquareOver| in a path type is a
3-dimensional cube, so we need one more dimension to our library.



