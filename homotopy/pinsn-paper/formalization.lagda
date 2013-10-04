
%include agda.fmt

\section{Formalization}

The calculation of $\pi_n(S^n)$ described in Sections~\ref{sec:pinsn}
and \ref{sec:encode-decode} is in |homotopy/PiNSN.agda|; it is
about 250 lines of code.  The loop space library described in
Section~\ref{sec:loopspace} is in 
|lib/loopspace/|; it is about 1500 lines of code.  The proof of
$\pi_n(S^n)$, including specifying the lemmas it uses from the loop
space library, took a few days.  The loop space library then took a
couple of weeks to complete, working for perhaps 4 hours per day.

The formalization has one cheat, which is that it takes place in an Agda
homotopy type theory library that uses type:type as a terser form of
universe polymorphism than Agda's.  More recent homotopy type theory
libraries use Agda's universe polymorphism instead of type:type, and we
believe that the proof could be ported to such a library.  

Agda does not provide very much proof automation for this proof: the
bulk of the proof is manual equational calculations with the loop space
operations.  However, with an improved computational
understanding of homotopy type theory, some of these calculation steps
might be definitional equalities.  

That said, Agda was quite useful as a proof checker, and for telling us
what we needed to prove next.  The terms involved in the calculations
get quite long, so it would be difficult to do these calculations, or to
have confidence that they were done correctly, without the use of a
proof checker.

It is worth describing one new device that we developed for
this proof, which is a combination of a mathematical and a engineering insight. 
Often in this proof, we are manipulating paths that have the form 
|p ∘ q ∘ ! p| (|q| conjugated by |p|),  
where |q| is thought of as ``the actual path of interest'' and |p| is some
``coercion'' or ``type cast'' that shows that it has some desired type.
Early in the development of the proof, we got stuck, because manipulating
these coercions explicitly gets quite cumbersome.  

The engineering insight is that, if we define a function |adj p q| that
returns |p ∘ q ∘ !p|, but make it \emph{abstract} (i.e. hide its
definition), then Agda can fill in in terms of the form
|adj _ q| in the middle of an equational calculation by unification.  By stating the
coercions at the beginning and end of the proof, and using lemmas that
propagate this information without explicitly mentioning it, we need not
state the coercions at each step of the proof.  Though |adj p q| is
abstract, we export a propositional equality equating it to |p ∘ q ∘
!p|, so that we can use this technique in the intermediate steps of a
calculation; the overall theorem is the same. 

The mathematical insight is that, for an element |p| of a
doubly-iterated identity type (i.e. when |p| is at least a path between paths), for any coercions |q|
and |q'| of the same type, |(q ∘ p ∘ ! q) = (q' ∘ p ∘ !q')|.  This is a
consequence of the higher homotopy groups being abelian.  

Combining these two insights, we can let Agda infer the coercions as we
proceed through the steps of the proof, and then, at the end, when we
need the inferred coercion to turn out to be a specific one, we simply
apply the lemma.  As a practical matter, this technique for managing
these coercions was essential to our being able to complete this proof.  

For example, here is a snippet of an equational deduction without
applying the technique:

\begin{code}
adjust (ap^-id n (\ f -> f x){f}) (ap (\ f -> apl n f x) (adjust (λl-id n) (ap (λl n) (λ≃ a)))) ≃〈 ... 〉
adjust (ap^-id n (\ f -> f x){f}) (ap (\ f -> apl n f x) (adj _ (ap (λl n) (λ≃ a)))) ≃〈 .. 〉
adj (ap^-id n (λ f₁ → f₁ x)) (ap (\ f -> apl n f x) (adj _ (ap (λl n) (λ≃ a)))) ≃〈 ... 〉
adj (ap^-id n (λ f₁ → f₁ x) ∘ ap (λ f' → apl n f' x) (λl-id n)) (ap (\ f -> apl n f x) (ap (λl n) (λ≃ a))) ≃〈 ... 〉
adj (ap^-id n (λ f₁ → f₁ x) ∘ ap (λ f' → apl n f' x) (λl-id n)) (ap (λ f → apl n (λl n f) x) (λ≃ a)) ≃〈 ... 〉
adj ((ap^-id n (λ f₁ → f₁ x) ∘ ap (λ f' → apl n f' x) (λl-id n)) ∘ ap≃ (! (β n (λ x₁ → id^ n)))) (ap (λ f → f x) (λ≃ a)) ≃〈 ... 〉
adj ((ap^-id n (λ f₁ → f₁ x) ∘ ap (λ f' → apl n f' x) (λl-id n)) ∘ ap≃ (! (β n (λ x₁ → id^ n)))) (a x) ≃〈 ... 〉
adj id (a x) ≃〈 ! (adj-id _) 〉
a x ∎
\end{code}
%%%%%
Here is the same snippet, where we use the technique and replace the
first argument to |adj| with |_|:

\begin{code}
adjust (ap^-id n (\ f -> f x){f}) (ap (\ f -> apl n f x) (adjust (λl-id n) (ap (λl n) (λ≃ a)))) ≃〈 ... 〉
adjust (ap^-id n (\ f -> f x){f}) (ap (\ f -> apl n f x) (adj _ (ap (λl n) (λ≃ a)))) ≃〈 ... 〉
adj _ (ap (\ f -> apl n f x) (adj _ (ap (λl n) (λ≃ a)))) ≃〈 ... 〉
adj _ (ap (\ f -> apl n f x) (ap (λl n) (λ≃ a))) ≃〈 ... 〉
adj _ (ap (λ f → apl n (λl n f) x) (λ≃ a)) ≃〈 ... 〉
adj _ (ap (λ f → f x) (λ≃ a)) ≃〈 ... 〉
adj _ (a x) ≃〈 ... 〉
adj id (a x) ≃〈 ... 〉
a x ∎
\end{code}
%
Moreover, if we did not appeal to the fact that any two coercions give equal results,
it is unclear how we would even prove, between the second-to-last and
third-to-last lines, that 
\begin{code}
((ap^-id n (λ f₁ → f₁ x) ∘ ap (λ f' → apl n f' x) (λl-id n)) ∘ ap≃ (! (β n (λ x₁ → id^ n)))) = id
\end{code}
The inferred coercion (the left-hand-side of this equation) uses
several loop space lemmas that are defined by induction on |n|, and it
is unclear how to prove that they cancel each other.
