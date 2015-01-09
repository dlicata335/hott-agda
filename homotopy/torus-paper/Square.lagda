
%include agda.fmt


\section{Squares}

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
After reducing the |ap|'s using |whisker-square|, we need
\begin{code}
Square (loop^ x) id loop (loop^ (x + 1))
\end{code}

The function |loop^| is defined so that |loop^(x+1) ≡ loop ∘ loop^x|, so we need a square
\begin{code}
Square (loop^ x) id loop (loop ∘ loop^ x)
\end{code}
which is exactly the characterization of composition as a Kan filler.  
