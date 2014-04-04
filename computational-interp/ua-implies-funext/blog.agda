The fact, proved by Voevodsky, that univalence implies function
extensionality, has always been a bit mysterious to me---the proofs that
I have seen have all seemed a bit non-obvious and fiddly, and I have
trouble re-inventing or explaining them.  Moreover, there are questions
about how this fact fits into a general conception of type theory: Why
does adding an axiom about one type (the universe) change what is true
about another type (functions)? How does this relate to other instances
of this phenomenon, such as the fact that a universe is necessary to
prove injectivity/disjointness of datatype constructors, or a univalent
universe is necessary to calculate path spaces of higher inductives?

In this post, I will describe a new proof that univalence implies
function extensionality that is less mysterious to me.  The proof uses
many of the same ingredients as existing proofs, but also requires a
couple of extra assumptions: It works for simple function types <tt>A →
B</tt> assuming definitional eta rules for functions and for Σ-types. It
works for Π-types assuming additionally that the "β-reduction" rule for
univalence holds definitionally.  I'd argue that some of the complexity
of the existing proofs results from working around the absence of these
extra definitional equalities.  Moreover, the proof technique also can
be used for positive types, such as coproducts, and for
higher-inductives---indeed, the proof of UA-implies-funext described
here is quite similar to Mike's original calculation of π1(S1), using
the total-space-of-the-cover-is-contractible argument.  At the end, I
will say a little about why the proof technique described here seems
necessary for function extensionality, but for coproducts and
higher-inductives we can use the encode-decode method.

<!--more-->

Relative to something like simplicial sets, one of the surprising things
about the HoTT axiomatization of ∞-groupoids is that what looks like a
statement about the points of a type often will determine what happens
at higher dimensions. For example, for product types <tt>A * B</tt>, the
point-level pairing and projection functions determine the path-level
structure (a path in a product is a pair of paths), and the
path-between-path-level structure (a path between pairs-of-paths is a
pair of paths-between-paths), and so on. Function extensionality is
another example of the same phenomenon: with univalence, the point-level
abstraction and application determine the path-level structure (for any
two functions, the type of paths between them is the same as the type of
homotopies/pointwise equalities), and the path-between-path structure (a
path between homotopies is again given pointwise), and so on. Let's
consider non-dependent functions, and by function extensionality I mean
the fact that thee is an equivalence

<code>funext : {A B : Type} (f g : A → B) → (f == g) == ((x : A) → f x == g x)
</code>
(where <tt>==</tt> is the identity type, with constructor <tt>id</tt>) such that, for any <tt>f</tt>
<code>
fst (funext f f) (id{_}{f}) == (λ x → id{_}{f x})
</code>
<tt>funext</tt> says that the paths in a function type are (equivalent
to) a function type, so there are "λ" and "application" operations on
paths in a function type. The "λ" operation, which goes from <tt>(x : A)
→ f x == g x</tt> to <tt>(f == g)</tt>, is the direction that is not
present in standard intensional type theory.  The computation rule says
that <tt>funext</tt> takes reflexivity to the function that returns
reflexivity; it is easy to see that this implies the formulation in the
book: a path induction implies that <tt>fst (funext f g) α == happly
α</ttt>.

Univalence-implies-funext says that the existence of the "λ" operation
on paths is somehow a consequence of the point-level operations on
function types (λ-abstraction and application), together with
univalence: we don't need to put in a new path-level "λ" and
"application" as axioms; they're already there.  To see why, it helps to
focus not on the identity type <tt>x == y</tt>, but the total path space
<code>
Paths A = Σ ((x,y) : A × A). x == y
</code>
One of the consequences of path induction is that there is an
equivalence (hence equality) between the total path space of <tt>A</tt>
and <tt>A</tt> itself:
<code>
contract-Paths≃ : Paths A ≃ A
</code>
From left-to-right, we can send <tt>((x,y),p)</tt> to <tt>x</tt>. From
right-to-left, we can send <tt>x</tt> to <tt>((x,x),id)</tt>. One
round-trip is definitionally the identity, and the other is the identity
by path induction. Then univalence says that this equivalence determines
an equality. Intuitively, up to homotopy, having two points connected by
a path is the same as just having one point.

<tt>contract-Paths≃</tt> helps explain why point-level operations
determine path-level operations: whatever operations we have on
<tt>A</tt> can be translated, by <tt>contract-Paths≃</tt>, to operations
on <tt>Paths A</tt>. 

As a bit of notation, let's write 
<code>
Homotopies : Type → Type → Type
Homotopies A B = (Σ ((f,g) : (A -> B) × (A → B)). (x : A) → f x == g x)
</code>
for the type of homotopies packaged together with their endpoints.  

Then the essence of this proof that univalence-implies-function
extensionality is the following chain of equivalences (writing ≃ for
equivalence):

<pre>   Paths (A → B)
≃ A → B          [by contract-Paths at A -&gt; B]
≃ A → (Paths B)  [by contract-Paths at B,
                     applied in the context (A → -)]
≃ Homotopies A B  [rearrange]
</pre>

The first line is the type of pairs <tt>((f : A -&gt; B, g : A -&gt;
B),p: f == g)</tt>---paths in a function type packaged together with
their endpoints.  The bottom line is the type of pairs ((f,g), h : (x :
A) → f x == g x)---homotopies packaged together with their endpoints.
Thus, this calculation says that, when packaged together with their
endpoints, the type of pointwise homotopies between functions is the
same as the type of paths between functions. 

The first steps is just an application of <tt>contract-Paths≃</tt>.
The second step is where univalence comes in: 
I am fond of saying that the reason univalence is a
sensible principle to add to type theory is that any
<tt>transport/ap</tt> along a use of univalence in a <em>known</em>
fibration/function can be reduced; but without function extensionality,
this is not actually true. In particular, without univalence or function
extensionality, you can't prove that if <tt>A</tt> is equivalent to
<tt>B</tt> then <tt>X -&gt; A</tt> is equivalent to <tt>X -&gt;
B</tt>---that the function type preserves equivalence in its codomain
(Lemma 4.9.2 in the book). With univalence (but without funext), an
equivalence <tt>e : Equiv A B</tt> determines a path <code> ap (\ A'
-&gt; (X -&gt; A')) (ua e) : (X -&gt; A) == (X -&gt; B) </code> and
therefore an equivalence between <tt>X → A</tt> and <tt>X →;
B</tt> (moreover, the forward direction is post-composition with
<tt>p</tt>, as in the book.).  This is exactly the justification for the
"applied in context <tt>A -&gt; -</tt>" part of the above
calculation. The <tt>→</tt> type is a map <em>out of</em> the
universe, and thus, univalence "adds" a new fact about function types
that is not present in non-univalent type theory: that <tt>→</tt>
preserves equivalences. (This is why I've changed my mind from an my
initial reaction that univalence should be "orthogonal" to function
types: the function types in question involve the universe that
univalence is asserting something about.)

Another way to see what's going on here is to try to write this
equivalence directly: It's easy enough to write maps from <tt>A → B</tt>
to <tt>A → Paths B</tt> and back.  But when you go to prove that they
compose to the identity in the <tt>f : (A → Paths B) ⊢ m1(m2 f) </tt>,
you want to do a path induction, but the path that you need to do
induction on is "stuck" under the function type.  Function types are not
invertible on the left, so you can't do this in regular intensional type
theory, because the <tt>A → -</tt> is in the way.  But univalence tells
you that the function type constructor preserves equivalences, so you
can use this to do path induction under the <tt>→</tt>.  This is the
difference between UA-implies-funext and a positive type like coproducts
or higher-inductives: in the latter case, the analogue of <tt>A → Paths
B</tt> <em>is</em> left-invertible, so we can move it out of the way and
do the path induction without appealing to univalence.  More on this below.  

The proofs of UA-implies-funext that I have seen have all used this
lemma (Lemma 4.9.2 in the book), but it has always been a bit mysterious
to me why it comes up, or how you would think to consider it. For me, at
least, the idea of translating operations on <tt>A</tt> to and from
operations on <tt>Paths A</tt> is a nice way to motivate it.

Read from bottom to top (which is the direction of function
extensionality that doesn't exist in raw intensional type theory), this
calculation says that a pointwise homotopy can be translated, through
<tt>A -&gt; B</tt>, to a path between functions. So the "λ" for
<tt>Paths (A -&gt; B)</tt>, which lets you turn a pointwise homotopy
into a path, is really coming from the point-level λ in <tt>A -&gt;
B</tt>, translated along <tt>contract-Paths</tt>.

Finally, to match the formulation of function extensionality in Section
2.9 of the HoTT book, we should also ask for the computation rule

<code> funext-comp : {A B : Type} (f : A → B) → coe (funext f f) id == (λ x → id)
</code>
(where <tt>coe : A == B -&gt; A -&gt; B</tt>) but I haven't checked this
yet (It seems like it should be true, but that it will require
<tt>funext</tt> to prove it... which seems a bit odd.)

Relationship to negatives: Assuming a universe closed under enough
stuff, one can similarly determine the higher structure of a coproduct
type <tt>A+B</tt>, or of higher inductives.
