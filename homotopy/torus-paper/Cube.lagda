
%include agda.fmt

\section{Cubes}

Just as we had a type of squares dependent on four points and four
lines, which make up the boundary of a square, we have a type of cubes
dependent on eight points, twelve lines, and six faces: 

\begin{code}
data Cube {A : Type} {a000 : A} : 
  {a010 a100 a110 a001 a011 a101 a111 : A}
  {p0-0 : Path a000 a010}
  {p-00 : Path a000 a100}
  {p-10 : Path a010 a110}
  {p1-0 : Path a100 a110}
  (left : Square p0-0 p-00 p-10 p1-0) 

  {p0-1 : Path a001 a011}
  {p-01 : Path a001 a101}
  {p-11 : Path a011 a111}
  {p1-1 : Path a101 a111}
  (right : Square p0-1 p-01 p-11 p1-1) 

  {p00- : Path a000 a001}
  {p01- : Path a010 a011}
  {p10- : Path a100 a101}
  {p11- : Path a110 a111}
  (back : Square p0-0 p00- p01- p0-1) 
  (top : Square p-00 p00- p10- p-01) 
  (bot: Square p-10 p01- p11- p-11) 
  (front : Square p1-0 p10- p11- p1-1) 
  → Type where
  id : Cube id id id id id id
\end{code}

The reason we have chosen to write |Cube left right back top bot front|
is that we think of a cube as an equality between the left and right
squares, along the "tube"
