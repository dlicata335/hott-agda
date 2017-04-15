% Setup {{{

  % Imports and Styling {{{
  \RequirePackage{amsmath}
  \documentclass[11pt,final]{westhesis} % add "final" flag when finished
  \def\textmu{}

  %include agda.fmt
  \usepackage{natbib, fullpage, textgreek, bussproofs, epigraph, color, float,
              enumerate, url, xcolor, graphicx, hyperref, listings, xfrac}
  \hypersetup{pdftex, backref = true, colorlinks = true, allcolors = {blue}}
  \usepackage{ dsfont }
  \setcounter{tocdepth}{4}
  \setcounter{secnumdepth}{4}
  \renewcommand{\hscodestyle}{\small}
  % }}}

  % Editorial commands {{{
  \newcommand{\Red}[1]{{\color{red} #1}}
  \newcommand{\nop}[0]{} % used to reconcile vim folds and latex curly braces
  \newcommand{\task}[1]{{\color{red} TASK: #1}}
  \newcommand{\tocite}[1]{{\color{red} [cite #1]}\xspace}
  %  }}}

  % Math and code commands {{{
  \renewcommand{\paragraph}[1]{\bigskip\textbf{#1}}
  \newcommand{\figrule}{\begin{center}\hrule\end{center}}
  \newcommand{\set}[1]{\left\{#1\right\}}
  % }}}

  % Unicode chars not supported by lhs2TeX {{{
  \DeclareUnicodeCharacter{738}{$^\text{s}$}
  \DeclareUnicodeCharacter{7503}{$^\text{k}$}
  \DeclareUnicodeCharacter{739}{$^\text{x}$}
  \DeclareUnicodeCharacter{7504}{$^\text{m}$}
  \DeclareUnicodeCharacter{8338}{$_\text{o}$}
  \DeclareUnicodeCharacter{8339}{$_\text{x}$}
  \DeclareUnicodeCharacter{11388}{$_\text{j}$}
  \DeclareUnicodeCharacter{8709}{$\varnothing$} % overwriting \emptyset
  \DeclareUnicodeCharacter{8984}{$\shamrock$}
  \DeclareUnicodeCharacter{10626}{$\col$}
  \DeclareUnicodeCharacter{65307}{$;$}
  % }}}
% }}}

% Title, Abstract, TOC {{{

\title{A Formal Verification of Courcelle's Theorem}
\author{Emily Black}
\advisor{Daniel R. Licata}
\department{Mathematics and Computer Science}
\submitdate{April 2017}
\copyrightyear{2017}
\pagestyle{chapsec}

\makeindex
\begin{document}

\begin{acknowledgements}
THANK YOU DAN!!!
\end{acknowledgements}

\begin{abstract}
This is the abstract.
\end{abstract}

\frontmatter
\maketitle
\makededication
\makeack
\phantomsection
\addcontentsline{toc}{section}{Abstract}
\makeabstract
\phantomsection
\addcontentsline{toc}{section}{Table of Contents}
\tableofcontents
\mainmatter
% }}}

\section{Introduction}
\par Wouldn't it be lovely if NP hard graph problems weren't NP hard? Perhaps this was what Bruno Courcelle was thinking when he came up with his eponymous theorem. Courcelle's Theorem is a very general algorithm which tries to wriggle out of the trap of NP-hardness. On a high level, the theorem states that if you ask certain kinds of questions about certain kinds of graphs, you can get a sort of linear answer. The qualifications on the questions, graphs, and linear-ness of the answer are quite large; the theorem is unfortunately no magic trick.
\par This work is a formal verification of the algorithm given in Courcelle's Theorem. The verification is done in Agda, a dependently typed programming language based on Haskell, that is often used a proof-checker. This work is also an earnest attempt to bring together the areas of programming languages and theory.
\par The introduction will give the formal statement of the theorem and the mathematical definitions required to understand the theorem. Then we will move to a brief, intuitive sketch of why the theorem is true, but we will delve into the proof with more detail later on. We will cover related work and some applications of Courcelle's theorem, and then head into the formalized definitions in Agda with their explanations, how the pieces of the algorithm fit together on a more detailed level, and finally the work that is left to be done in this project.
\par We begin our dive into the details of Courcelle's Theorem: what kinds of questions can we ask, on what kinds of structures, and what sort of a linear algorithm do we get? The more formal statement of the theorem is as follows: Any problem that can be expressed in monadic second order logic can be decided in fixed-parameter tractable linear time on a structure of bounded treewidth.
\par The kinds of questions we can ask are those expressible in Monadic Second Order Logic, or \textbf{MSO}. MSO allows us to quantify over objects and sets, but not over any relations that are not unary. For example, if we modeled edges in a graph by a binary relation $E(x,y)$ where $x$ and $y$ are vertices, we could not ask the question: $\forall E(x,y)$  is there an element $z, z \neq y$ and $x \neq z,$ such that $E(y, z)$ or $E(x, z)$?  This is because we would be quantifying over all edges, which here we depict as a binary relation.
\par MSO manages to express quite a few NP hard problems: k-colorability, k-vertex cover, k-dominating set, all for fixed k, to name a few. (Put in the MSO for these problems here?) There are also extensions of MSO, such as ExtendedMSO and LinMSO (CITE!), that allow for linear optimizations of problems expressible in MSO, for example minimum vertex cover and dominating set. These have also been proven to be decided on graphs of bounded treewidth in fixed-parameter tractable linear time. Note, we cannot ask about **is this right??** Hamiltonian cycles with MSO logic, because?..
\par \textcolor{red}{NOTE: Do I need a more formal def of MSO here, like they have in the game theory paper, building up from the beginning?}

\par The kinds of structures (a graph is a type of structure) that we can ask MSO questions about are graphs of bounded treewidth. Treewidth is a measure of the extent to which a graph is "tree-like". If a graph has bounded treewidth, then all of its information can be encoded in a tree in a finite fashion.
In order to formally understand treewidth, we first have to understand tree decompositions. We define tree decompositions as follows:
\par A tree decomposition of a graph $G=(V, E)$ is a pair $(T, X)$ where T is a tree and X is a a family of sets indexed by the vertices of T, such that
\begin{enumerate}
\item $\bigcup X_{i} = V $
\item $\forall e \in E, \exists i $ such that the vertices incident on e are present together $X_{i}$
\item If $i, j, k$ are nodes of T such that $i$ is on a path between $j$ and $k$, then $(X_{j} \cap X_{k}) \subset X_{i}. $
\end{enumerate}
The sets of vertices, $X_{i}$, are called bags. The width of a tree decomposition is the size of the largest bag $X_{i}$ minus one. The \textbf{treewidth} of a graph is the minimum width over all possible tree decompositions.
\par Note that every finite graph $G$ has finite treewidth, because a tree decomposition of a finite graph is a tree of one node, with a bag $X_{i}$ containing all vertices of G within it, so the treewidth is no greater than the number of nodes in the graph. However, as we will soon see, using this tree decomposition would render Courcelle's Theorem useless. Finding the treewidth of a graph is an NP-hard problem, and the version of Courcelle's Theorem that I have verified assumes that it is given a tree-decomposition of a graph as an input. However, there is no need for that tree decomposition to be entirely optimal; it will just increase the time the algorithm takes slightly. There are a few good heuristic algorithms for finding the treewidth of a graph, which can find a ?-approximation in ??? time. However, the algorithm verified in this paper pays no attention to this part of the process, though others have taken a different approach.
\par We can see that a tree decomposition of a graph is an encoding of a graph into a tree: it preserves all the information of the original graph within it. It has all of the vertices by the first condition, it keeps track of all of the edges by the second condition, \textcolor{red}{and the third condition ensures that ???what is the third condition good for??.}
\par Finally, we come to the condition on linear-ness:  the algorithm we get for deciding an MSO question on a graph of bounded treewidth is fixed-parameter tractable linear, or FPT linear. An FPT linear algorithm is linear with respect to the size of the input, in our case, the graph, but with an exponential constant proportional to other parameters, in our case, the encoding of the MSO question, $\phi,$ and the treewidth $\omega.$ Unfortunately, this exponential constant is very large. In fact, unless P=NP, the constant cannot be upper bounded by an iterated exponential of height bounded by $\phi$ and $\omega$.
\par Bringing these definitions together, we can now understand the formal statement of Courcelle's Theorem:
\par Let P be an MSO problem and $\omega$ be a positive integer. There is an algorithm $A$ and a function $f : \textbf{N} \times \textbf{N}  \rightarrow \textbf{N}$ such that for every graph $G = (V, E)$ of order $n:= |V|$ and treewidth at most $\omega, A$ solves $P$ on input $G$ in time $f(||\phi||, \omega)  \cdot n,$ where $\phi$ is the MSO formula defining $P$ and $||\phi||$ is its length. Furthermore, unless $P=NP$, the function $f$ cannot be upper bounded by an iterated exponential of bounded height in terms of $\phi$ and $\omega$. (Taken directly form game theoretic approach)

\par Upon reading about this ghastly constant, it may seem that the possibility of practical usage of Courcelle's Theorem is quite small. However, not all hope is lost. There is work being done on making Courcelle?s theorem usable, as will be discussed slightly later on. First, we give an intuitive sketch of why this theorem may be true.
\par But then we say, we don't actually use that approach to implement the algorithm because all of those nasty constants. The problem with the automata approach is that in practice, many of the states of the tree automaton generated are never used (cite). There are a few different ways to circumvent this issue; they all involve some version of creating what you need as you go. This can be done by creating your state-transition function "on-the-fly", giving the name fly-automata. Alternatively, this can be done by scrapping the idea of automata all together, which is what the implementation in \textbf{Courcelle's Theorem: A Game Theoretic Approach by Kneiss and other people} does. This paper uses a game theoretic method, which takes the details of the actual input graph given into account, so that the algorithm only stores and uses the information it needs.
\par then OUTLINE OF GAME THEORY ALGO? which I'll need help with!
\cite{tom7}
\section{Related Work and Applications}
\par -include ALL of the papers we read over the summer. Create a set of things to read. Mention the sources, in a sentence say what's in them. So-and-so does applications to blah, collect for future research.
\par Talk about MONA tool, fly-automata? and applications like Graph Minors, phylogenetics, databases?
\section{Definitions}
\subsection{Structures}
\par The version of Courcelle's Theorem that is verified in this paper generalizes beyond graphs as the input object to the algorithm. We really show that any MSO sentence can be decided on a \textbf{structure} of bounded treewidth in FPT-linear time. In order to define structures, we have to introduce some other concepts first.
\par A \textbf{symbol}  $S$ is an object with an arity, $arity(S)\geq 0$. If a symbol has arity 0, then it is a $constant$, if it has arity greater than 0, it is a $relation$.
\par A \textbf{signature} $\Sigma$ is a finite set of symbols. ~And a $structure$ $\mathds{A}$ over a signature $\Sigma$ is an interpretation of the symbols of $\Sigma$ from a given set.~
\par A \textbf{structure} $\mathds{A}$ is a tuple $\mathds{A} = ( A, (R^{\mathds{A}})_{R\in rel(\Sigma)}, (c^{\mathds{A}})_{c\in constants(\Sigma)})$, where $A$ is a finite set called the universe of $\mathds{A}$, and $R^{\mathds{A}}$ and $c^{\mathds{A}}$ are interpretations of the relations and constants in $\Sigma$ using the elements of $A$. More precisely, $R^{\mathds{A}} \subset A^{arity(R)},$ and $c^{\mathds{A}}$ is either an element of $A$, or $c^{\mathds{A}}$=nil.
\par It may be useful to think of the signature as a mold your pour clay into, where clay is a finite set. Or, you can think of symbols in the signature as placeholders that are waiting to be filled by elements of a set. We illustrate this with the example of graphs. A possible signature for graphs is $\Sigma_{G} = Edge(x,y)$, where edge is a binary relation that determines which vertices have an edge in between them. This signature is not a graph itself. An actual graph would be a structure $\mathds{G}$ over the graph signature $\Sigma_{\mathds{G}}$ with a set, $V$, of vertices, $\mathds{G}= (V , Edge(x,y)^{\mathds{G}})$.   $Edge(x,y)^{\mathds{G}} \subset V \times V$ is an interpretation of the Edge(x,y) relation that specified all of the vertices that had an edge between them for that specific graph. Note that you could have a different graph $\mathds{G}'$ using the same set V, but if you used a different subset of $V \times V$ for the interpretation of the edge relation, because this graph would have different edges.
\par Necessary to understanding the code is the idea of an expansion of a structure. Suppose $\Sigma$ is a signature, and $\{ R_{1}, ... R_{l}, c_{1}, ... c_{m}\}$ is a set of symbols, each of which is not in $\Sigma$. Then $\Sigma '$ = ${ \Sigma, R_{1}, ... R_{l}, c_{1}, ... c_{m}}$ is an expansion of $\Sigma$. Then, if $\mathds{A}$ is a $\Sigma$-structure, and $\mathds{A}'$ is a $\Sigma '$-structure, such that $(R^{\mathds{A}})=(R^{\mathds{A}'})$ for all relations symbols $R \in \Sigma$, and $c^{\mathds{A}}= c^{\mathds{A}'}$ for all $c \in \Sigma$, we say $\mathds{A}'$  is a $\Sigma '$-expansion of $\mathds{A}$. Suppose we have a $\Sigma$-structure $\mathds{A}$, and suppose that  $\Sigma ' = \{ \Sigma, c_{1}\}$. Also suppose we have an element $u_{1} \in (A \cup {nil})$. Then we can write the $\Sigma ' $-structure $\mathds{A}'$ as $\mathds{A}' = (\mathds{A}, u_{1})$, to show that $\mathds{A}'$ is a $\Sigma ' $-expansion of $\mathds{A}$, and that $u_{1}$ is the  interpretation for the new symbol $c_{1}$. Similarly, if $\Sigma ' = \{ \Sigma, R_{1}\}$ for some relation symbol $R_{1}$, and we have a set $U_{1} \subset A^{arity(R)}$, then we could write a $\Sigma '$-expansion of $\mathds{A}$ as $\mathds{A}' = (\mathds{A}, U_{1})$. We will see this in the Agda code.
\par We designed our algorithm to respect the idea of structures as inputs, but in this particular implementation, we tailored it to expect graphs as input. In the non-extended form of MSO we are using in this work, one cannot decided problems on graphs quantify over edges, since the edge relation is binary. In order to remedy this, we instead think of a graph as a set with two different types of elements: nodes and edges. This way, we can quantify over edges, since they are simply constants in the signature rather than a binary relation. However, including edges as elements of the underlying set of a structure $\mathds{G}$ instead of as a binary relation has the implication that edges and nodes are indistinguishable, which can pose problems. For example, suppose you want to have a graph $\mathds{G}_{red}$ that has a special set of of red nodes. Then there would be a unary relation in this graph's signature, $Red(x)$, and an interpretation in the structure, $Red(x)_{\mathds{G}_{red}} \subset G_{red}$, that specified which elements of the underlying set $G_{red}$ were the red vertices. However, the problem here is that some of these "red vertices" might actually be edges, since vertices and edges in the underlying set are indistinguishable to the relation. So how do we make sure that only vertices are allowed in this set?
\par We fix this problem in the code by introducing the data type Tp, which has an edge constructor and a node constructor. We then require in our datatype for symbols, Sigthing, that constants (constructor $i$) specify which kind of set elements they want, nodes or edges, by carrying a Tp with them. Relations (constructor $r$) specify whether they want a node or edge for each argument, by carrying a list of Tp with them. This solves the problem illustrated above because the relation $Red(x)$ would really be a one-element list (node::[]).  Another, related reason why we introduce Tp is to make sure that when we have quantifiers in a formula, we specify whether that quantifier is for edges or for nodes, in order to ensure that we have as small a search space as possible.   \textcolor{red}{is this right?}
\begin{code}
  data Tp : Type where
    node : Tp
    edge : Tp

  data SigThing : Type where
    i : Tp → SigThing
    r : List Tp → SigThing
\end{code}
\par Now we have our Agda definition of a signature: a list of SigThings, i.e. a list of symbols. And, a list is finite by definition, so we satisfy the requirement that the signature is a finite set of symbols. We have two functions on signatures, which allows us to extend them: the function ,i allows us to add another constant onto our signature, and the function ,r allows us to add another relation onto our signature. These functions take a signature and either a constant or a relation, and return a signature which is the original signature appended the constant.
\begin{code}
  Signature = List SigThing

   _,i_ : Signature → Tp → Signature
  Σ ,i τ = i τ :: Σ

  _,r_ : Signature → Args → Signature
\end{code}
\par Coming up with a definition for a structure was a little bit more complicated, since there are a few more moving parts. Recall the definition of structure above: A structure $\mathds{A}$ is a tuple $\mathds{A} = ( A, (R^{\mathds{A}})_{R\in rel(\Sigma)}, (c^{\mathds{A}})_{c\in constants(\Sigma)})$, where $A$ is a finite set called the universe of $\mathds{A}$, and $R^{\mathds{A}}$ and $c^{\mathds{A}}$ are interpretations of the relations and constants in $\Sigma$ using the elements of $A$. In order to represent this in Agda, we needed to define what the underlying set would be. A set is a collection of elements, so before we could define sets, we had to define what sort of elements would be making up these collections. We defined the objects in our space, the elements of our sets, our clay that would fill our signatures, to be Individs (short for individuals). An individ takes a Tp, i.e. data of whether it is a node or an edge, and returns a type. This type happens to be string in our implementation, but one could change the code to model the set elements as any kind of structure one might like.
\begin{code}
 Individ : Tp → Type
  Individ node = String
  Individ edge = String

 Args : Type
  Args = List Tp

  Individs : Args → Type
  Individs [] = Unit
  Individs (τ :: τs) = Individs τs × Individ τ
\end{code}
\par Now that we have our objects, we can define sets of objects. Our notion of set is called a Subset (because set is a reserved word in Agda), and we defined Subset as a predicate on elements (Individ) of a certain type. So, edge elements and node elements can have different stipulations that determine whether or not they are in a given set. In case the difference between Tp and Individ is confusing, think of a Tp $\tau$ as a label for a certain slot in a signature that says what $type$ of thing can go in it, and an Individ of type $\tau$ is the thing that goes in. \textcolor{red}{is there a more intuitive way of explaining "predicate on elements of certain type?"}
\begin{code}
 Subset = (τ : Tp) → Individ τ → Type
 DecidableSub : (S1 : Subset) → Type
 DecidableSub S1  = ∀ {τ} (x : Individ τ) → Dec (S1 τ x)
\end{code}
\par For now, our construction Subset does not guarantee that the set is finite as is required in the definition of a structure. We anticipate revising this once we see what we need in the rest of the proof--- we will definitely add the conditions of finiteness and decidableness to the subset, but there may be other qualities that we require that are as of yet unseen. Adding these qualifications to the subset is a trivial task, we would simply add a bit more data that we could abstract away and leave the code unchanged, so please pay this small detail no mind. And, after defining subsets, we defined IndividS, which is simply an Individ together with the data that it's in a specified subset.
\begin{code}
 IndividS : Subset → Tp → Type
  IndividS A τ = Σ \ (x : Individ τ) → A τ x

  IndividsS : Subset → Args → Type
  IndividsS A [] = Unit
  IndividsS A (τ :: τs) = IndividsS A τs × IndividS A τ
\end{code}
\par We also defined a datatype OC, with constructors open and closed, that signifies whether a structure is open or closed, i.e. whether the structure has constants that are interpreted as nil, or not.

\begin{code}
data OC : Type where
    Open : OC
    Closed : OC
\end{code}

\par Then, combining subsets, OC, and signatures, we defined something called a StructureS, which we build on to finally define a structure.
Think of the StructureS as the part of the structure tuple that consists of all the interpretations of the signature.
A StructureS is a datatype that requires data saying whether it is open or closed (OC), a subset, and a signature.
Now would be a useful time to review the notion of expansions of structures given a slightly above this definition.
StructureS has four constructors: empty, an expansion with an element of the underlying set (IndividS),
an extension with a nil (this mandates that the StructureS be open),
and an extension with a set (corresponding to a relation tuple).
Note that the expansion constructors return a StructureS over an expanded signature,
adding a constant symbol of type $\tau$ in the $,is$ and $,none$ cases, and adding a relation symbol in the $,rs$ case.
We then create the type Structure, which requires an OC and a Signature, and consists of a product of a subset and a StuctureS
that goes with that subset, i.e. a tuple of a set, and interpretations of a given signature from that set, which is exactly what
a structure is defined to be mathematically.
\begin{code}
data StructureS : OC → Subset → Signature → Type where
     []      : ∀ {oc A} → StructureS oc A []
     _,is_   : ∀ {oc A Σ τ} → StructureS oc A Σ → IndividS A τ → StructureS oc A (Σ ,i τ)
     _,none  : ∀ {oc A Σ τ} → StructureS oc A Σ → StructureS Open A (Σ ,i τ)
     _,rs_   : ∀ {oc A Σ τs} → StructureS oc A Σ → (IndividsS A τs → Type) → StructureS oc A (Σ ,r τs)
\end{code}
\subsection{Restrictions}
\par Suppose we have a structure $\mathds{A} = ( A, (R^{\mathds{A}})_{R\in rel(\Sigma)}, (c^{\mathds{A}})_{c\in constants(\Sigma)})$. We can restrict this structure to a smaller subset $A_{1} \subset A$, and call this structure $\mathds{A}[A_{1}]$. In this new structure, we insist that we actually only have the set elements in $A_{1}$, and so we only have the constant and relation interpretations that are contained entirely inside $A_{1}$. Mathematically, given a structure $\mathds{A}$ and a set $A_{1} \subset A$, the restriction of $\mathds{A}$ to $A_{1}$, $\mathds{A}[A_{1}]$, is a structure with universe $A_{1}$,  $(R^{\mathds{A}[A_{1}]})= R^{\mathds{A}} \cap A_{1}^{arity(R)}$, and $c^{\mathds{A}[A_{1}]} = c^{\mathds{A}} if c^{\mathds{A}} \in A_{1},$ and become interpreted as nil otherwise.
\par In Agda, we encode this notion by a helper function restrictionS on StructureS's, and from that we build restriction on Structures. Note that in our helper function restrictionS, we ask for a proof that the subset we restrict to is decidable; when we fix our notion of subset this will no longer be necessary. The code is relatively straightforward and there is no need to go through it in detail; essentially this code checks each IndividS that interprets a constant in the signature in the StructureS A1', and if it is not in the restriction subset S1, it replaces this interpretation with a nil. And it only includes relation tuples that are entirely within $S1$. HELP HERE!!
\begin{code}
 restrictionS : ∀ {Σ} {oc1} {A1} (A1' : StructureS oc1 A1  Σ) (S1 : Subset) → DecidableSub S1 → Sub S1 (A1) →  StructureS Open S1 Σ
  restrictionS [] S1 dec sb = []
  restrictionS (A1' ,is x) S1 dec sb with dec (fst x)
  ... | Inl inS = restrictionS A1' S1 dec sb ,is (fst x , inS)
  ... | Inr out = restrictionS A1' S1 dec sb ,none
  restrictionS (A1' ,none) S1 dec sb = restrictionS A1' S1 dec sb ,none
  restrictionS (A1' ,rs U) S1 dec sb = restrictionS A1' S1 dec sb ,rs (λ v → U (promoteIndividsS sb v))
\end{code}
\par The code for restriction simply attaches the appropriate subset, S1, to the restricted interpretations given by restrictionS.
\begin{code}
  restriction : ∀ {Σ} {oc1} (A1 : Structure oc1  Σ) (S1 : Subset) → DecidableSub S1 → Sub S1 (fst A1) →  Structure Open Σ
  restriction (A1' , struc) S1 dec sb = S1 , restrictionS struc S1 dec sb
\end{code}
\subsection{Tree Decompositions}
\par Recall our definition of tree decompositions above. The formal definition that we based our code off of is more general than the definition given above, because the game-theoretic algorithm works over all structures that do not have constants, (called relational structures) and not simply over graphs. The definition for a tree decomposition of an arbitrary relational structure is as follows:
\par A tree decomposition of a structure $\mathds{A}$ over signature $\Sigma$ is a tuple $(\textbf{T}, X)$, where $\textbf{T}=(T,F)$ is a rooted tree and $X=(X_{i})_{i \in T} $ is a collection of subsets $X_{i} \subset A$, (where A is the underlying subset of $\mathds{A}$) such that
\begin{enumerate}
\item $\bigcup X_{i} = A $
\item $\forall$  $p$-ary relation symbols $R \in \Sigma,$ and all $(a_{1}, a{2}, ....a_{p}) \in R^{\mathds{A}} \exists i \in T$ such that $(a_{1}, a_{2}, ....a_{p})  \subset X_{i}$, and
\item If $i, j, k$ are nodes of T such that $i$ is on a path between $j$ and $k$ in $\textbf{T}$, then $(X_{j} \cap X_{k}) \subset X_{i}. $
\end{enumerate}
\par Furthermore, in the algorithm that the game theoretic paper outlines, they use only a type of tree decompositions called nice tree decompositions. Nice tree decompositions are directed, and every edge is directed away from the root. Nice tree decompositions have exactly four types of nodes: leaves, forget nodes, introduce nodes, and join nodes. A leaf $i$ in nice tree decomposition has an empty bag, i.e. $X_{i}=\emptyset$. A forget node is a node $i$ that has exactly one child, $j$, and there exists some $a \in A$ $X_{i}=X_{j}/{a}$. An introduce node is a node $i$ that has exactly one child, $j$, and there exists some $a \in A, a \notin X_{j}$ such that $X_{i}=X_{j}\cup {a}$. A join node is a node $i$ with exactly two children, $j$ and $k$, where $X_{i}=X_{j}=X_{k}$. We say that node $i$ is below node $j$ if there is a path from $i$ to $j$ in $T$.
\par Finally, keep this idea in mind: for every node $i$ of a nice tree decomposition of a $\Sigma$-structure $\mathds{A}$, let $A_{i} = \bigcup_{(j \text{ below } i)} X_{j}$. See that $A_{i} \subset A$. Then for every node $i$, we can associate with $i$ a substructure $\mathds{A}[A_{i}]$, i.e. a restriction of $\mathds{A}$ to $A_{i}$.
\par In Agda, we modeled a nice tree decomposition as a datatype with four constructors, Empty, Delete, Intro, and Join, one for each type of node. Each node carries two subsets with it; its bag (X) and the set of all elements in all bags at and below it (B). More precisely, at node $i$, $B= \bigcup_{n=i \text{or n below} i} X_{n}$. We will prove that this is the case after we give an explanation of each constructor.
\begin{code}
data TreeDecomp : Subset →  Subset → Type where
      Empty : TreeDecomp empty empty
      Delete : ∀ {τ} (X : Subset) (B : Subset) (x : Individ τ)
                    → TreeDecomp (union X (singleton {τ = τ} x)) B
                    → TreeDecomp X B
      Intro : ∀ {τ} (X : Subset) (B : Subset) (x : Individ τ)
                  → (xnew : (Sub (singleton {τ = τ} x) (complement B)))
                  →  ( ∀ {τs} → (xs : IndividsS (fst A) τs)
                              (inBandx : allin τs (union B (singleton {τ = τ} x)) (nosubset τs (fst A) xs))
                  → (xinxs : indIninds τ τs x (nosubset τs (fst A) xs))
                           (rel : r τs ∈ Σ ) (relholds : get rel A xs)
                  → (allin τs (union X (singleton {τ = τ} x)) (nosubset τs (fst A) xs)))
                  → TreeDecomp X B
                  → TreeDecomp (union X (singleton {τ = τ} x)) (union B (singleton {τ = τ} x))
      Join : ∀  (X : Subset) (B1 B2 : Subset)
              → (containment1 : Sub X (intersection B1 B2))
              → (containment2 : Sub (intersection B1 B2) X)
              → ( ∀ {τs} → (xs : IndividsS (fst A) τs) (inBsunion : allin τs (union B1 B2)
                         (nosubset τs (fst A) xs)) (rel : r τs ∈ Σ )
                          (relholds : get rel A xs)
             → (Either (allin τs B1 (nosubset τs (fst A) xs)) (allin τs B2  (nosubset τs (fst A) xs))))
             → TreeDecomp X B1
             → TreeDecomp X B2
             → TreeDecomp X (union B1 B2)

\end{code}
\par The empty constructor is the leaf node, it has an empty set for its bag and an empty set for the elements below.
\par The delete constructor, i.e. the forget node, takes a tree decomposition of a bag $Xs \cup x$ and a set B of elements below, and returns a tree decomposition with just the bag X and the same set B of elements below. \textcolor{red}{is this the right way to explain it?}
\par The Intro constructor, for the introduce node, requires a few additional pieces of information. Firstly, it needs a proof (xnew) that the element ($x$) being introduced is indeed new; i.e. it is an element of the complement of $B$, the set of objects below the Intro node in the tree decomposition. Secondly, it needs a proof showing that for all relations $R$ that have tuples made up exclusively of x and and elements of $B$, that all of the elements in these tuples are in fact contained in $X \cup {x}$. This is in order to satisfy the second and  third conditions of the definition of tree decompositions. To illustrate this, consider some introduce node $i$. Suppose the second proof were false, i.e. there exists some tuple $p$ consisting exclusively elements of $B$ and $x$ such that $p \notin X_{i}$. Recall that the second condition of a tree decomposition requires that every tuple of every relation be in some bag $X_{j}$. We know by the first required proof that x is not in B, so any relation containing x, including $p$, must be either in $X_{i}$ or some $X_{j}$ above $X_{i}$. So since $p\notin X_{i}$, $p$ must be in some some $X_{j}$ above $X_{i}$. Suppose one of the elements $b \in B$, $b \in p$ from some bag $X_{h}$, with $h$ below $i$ in $T$. Suppose $b \notin X_{i}$. Then $b$ must be in $X_{j}$, since $b \in p$. Then, by condition three of tree decompositions, since there is a path between $X_{h}$ and $X_{j}$ through $X_{i}$,  $(X_{h} \cap X_{j}) \subset X_{i}. $  This means that $b \in X_{i}$. But this is a contradiction, so it must in fact every tuple consisting entirely of elements of $B$ and $x$ must be contained in $X_{i}$.
\par Finally, we come to the Join constructor. First, note that for the join constructor, the bags $X_{i}=X_{j}$ for the nodes $i , j$ being joined, but the $B_{i}, B_{j}$, the sets of all elements in all bags below $i$ and $j$ respectively, may not necessarily be the same. In fact, they likely are not. The Join constructor in Agda requires two proofs, (written as three since we did not make equality for sets): that $X=B_{i} \cap B_{j}$, and that for all relation-tuples in $B_{i} \cup B_{j}$, either the entire relation tuple is in $B_{i}$ or it is in $B_{j}$. In other words, there is no relation tuple in $B_{i} \cup B_{j}$ that contains elements from both $B_{i}\setminus B_{j}$ and $B_{j}\setminus B_{i}$.
The first proof is required to maintain condition three of tree decompositions. Suppose there is some join node $i$, which joins nodes $j$ and $k$ where $\exists x \in X_{i}$ such that $x \notin B_{j} \cap B_{k}$. However, note that $X_{i}=X_{j}=X_{k}$, so $x \in X_{j} \subset B_{j}$, and $x \in X_{k} \subset B_{k}$, so $ x \in B_{j} \cap B_{k}$, and we have reached a contradiction. So $X_{i}=X_{j}=X_{k} \subset B_{j} \cap B_{k}$.
Suppose $\exists b \in B_{j} \cap B_{k}$ such that  $b \notin X_{i}$. Now, since $b \in B_{j}$, there is some node $m$ below $j$ such that $b$ is in $X_{m}$. And, since $b \in B_{k}$, there is some node $l$ below $k$ such that $b$ is in $X_{l}$. Since node $i$ joins nodes $j$ and $k$, there is a path between $m$ and $l$ through node $i$. Therefore, by condition three, $X{m} \cap X_{l} \subset X_{i}$. So $b$ must be in $X_{i}$. However, we assumed the opposite, so we have reached a contradiction. Therefore  $B_{j} \cap B_{k} \subset X_{i}$.
Putting these two proofs together, we see it must be that $B_{j} \cap B_{k} = X_{i}$.
\par The second proof is necessary to preserve the second and third condition of tree decompositions. Suppose that there exists some relation tuple $r \in R^{\mathds{A}} $ such that $r \in B_{j} \cup B_{k}$, and $r \notin B_{j}$ and $r \notin B_{k}$. That is, there exists some $b_{j} \in r$ such that  $ b_{j} \in B_{j} \setminus B_{k}$ and some $b_{k} \in r$ such that $b_{k} \in B_{k} \setminus B_{j}$. Then by condition two of tree decompositions, there must be some node $m$ in the tree decomposition such that $r \in X_{m}$. However, since r contains elements not in $B_{j}$ and elements not in$ B_{k}$, node $m$ must be above both $j$ and $k$. And since $r \notin B_{j} \cap B_{k} = X_{i}$, $ r \notin X_{i}$ as well. So $m$ must be above $i$. However, there is some node $a$ below node $j$ such that $b_{j} \in bag X_{a}$. And, there is be a path between node $a$ and node $m$, and it must go through node $i$. Therefore, $b_{j} \in X_{a} \cap X_{m} \subset X_{i}$. A symmetric argument can be used to show that $b_{k} \in X_{i}$. Therefore, $b_{j}, b_{k} \in X_{i} = B_{j} \cap B_{k}$. However, we assumed this was not the case; therefore we have reached a contradiction, and so it must be that for all relation-tuples in $B_{i} \cup B_{j}$, either the entire relation tuple is in $B_{i}$ or it is in $B_{j}$.
\par Now we run through a proof of that fact that for all nodes $i$, $B= \bigcup_{n=i \text{or n below} i} X_{n}$. We do this by showing that this property holds at each constructor.
\par We prove by induction. For the base case, we have that if node $i$ is an Empty, then it has $\bigcup_{n=i \text{or n below} i} X_{n} = \emptyset$ since the bag at a leaf is empty by definition, and there are also no nodes below a leaf. Then since $B=\emptyset$ as well, we have $\bigcup_{n=i \text{or n below} i} X_{n} = B$, as desired.
\par Now we run through our inductive steps, one for each constructor. Consider a node $i$. Firstly, suppose $i$ is a delete node. By definition, we know that the node directly below $i$, call it $i-1$, had $X_{i-1} = X_{i} \cup x$ for some $x$. And, we know that $B_{i-1}=B_{i}$. By our inductive hypothesis, we have that $B_{i-1}= \bigcup_{n=i-1 \text{or n below} i-1} X_{n}$. Note that $\bigcup_{n=i \text{or n below} i} X_{n} = (\bigcup_{n=i-1 \text{or n below} i-1} X_{n}) \cup X_{i} $. But since $X_{i-1} = X_{i} \cup x$, then $X_{i} \subset X_{i-1}$, $X_{i}$ brings in nothing new. So $\bigcup_{n=i \text{or n below} i} X_{n} = \bigcup_{n=i-1 \text{or n below} i-1} = B{i}$, as desired.
\par Suppose $i$ is an introduce node. Then by definition, $X_{i}= X_{i-1} \cup {x}$ for some $x \notin B_{i-1}$, and $B{i}= B_{i-1} \cup {x}$. By induction, we have that $B_{i-1} = \bigcup_{n=i-1 \text{or n below } i-1} X_{n}$. Note that $\bigcup_{n=i \text{or n below } i} X_{n}= \bigcup_{n=i-1 \text{or n below } i-1} X_{n} \cup X_{i}$. But note that this is simply $B_{i-1} \cup {x}= B{i}$, as desired.
\par Suppose $i$ is a join node; suppose it joins nodes $j$ and $k$. By definition, we have $B{i}=B{j} \cup B{k}$, and we have $X=B{j} \cap B{k}$. By the inductive hypothesis, we have that $B{j}= \bigcup_{n=j \text{or n below } j} X_{n}$, and $B{k}= \bigcup_{n=k \text{or n below } k} X_{n}$. Note that $\bigcup_{n=i \text{or n below } i} X_{n} = B_{j} \cup B_{k} \cup X_{i}$. However, since $X=B{j} \cap B{k}$, this is simply $B_{j} \cup B_{k} $. Therefore, $\bigcup_{n=i \text{or n below } i} X_{n} =B_{j} \cup B_{k}= B{i}$, as desired.
\subsection{MSO Formulas}
\par Now we come to the definition for an MSO formula in Agda. First, we give a more formal definition of MSO than we did in the introduction. A question formulated in MSO is referred to as an MSO sentence. We define $MSO(\Sigma)$, the set of all MSO sentences over a given signature $\Sigma$, as follows:
\begin{itemize}
\item $\forall$ p-ary relations $R$ and constants $c_{1}, c_{2}, ... c{p} \in \Sigma, R(c_{1}, c_{2}, ... c{p}) \in MSO(\Sigma).$ These are the atomic formulas.
\item \textcolor{red}{QUESTION: WHAT ABOUT x1=x2 and other stuff like that???}
\item If $\phi, \psi$ are in $MSO(\Sigma)$, then $\neg \phi, \phi \vee \psi, \phi \wedge \psi,$ are all in $MSO(\Sigma).$
\item If $\phi \in MSO(\Sigma \cup {c})$ for some constant c, then $\forall c \phi$ and $\exists c \phi$ are in $MSO(\Sigma).$
\item If $\phi \in MSO(\Sigma \cup {R})$ for some \textbf{unary} relation symbol R, then $\forall R \phi$ and $\exists R \phi$ are in $MSO(\Sigma).$ Note that the unary here is the "monadic" part of MSO: we are only allowed to quantify over sets.
\end{itemize}
\par Here is our code below, followed by an explanation:
\begin{code}
 data Terms (Σ : Signature) : List Tp → Type where
    []   : Terms Σ []
    _,t_ : ∀ {τ τs} → (i τ) ∈ Σ → Terms Σ τs → Terms Σ (τ :: τs)

  data Formula (Σ : Signature) : Type where
    ∀i ∃i : (τ : Tp) → Formula (Σ ,i τ) → Formula Σ
    ∀p ∃p : (τ : Tp) → Formula (Σ ,r (τ :: [])) → Formula Σ
    _∧_ _∨_ : Formula Σ → Formula Σ → Formula Σ
    ⊤ ⊥ : Formula Σ
    R ¬R : ∀ {τs} → (r τs) ∈ Σ → Terms Σ τs → Formula Σ
\end{code}
\par Our encoding of formulas Agda follows the definition above pretty straightforwardly. The first constructor corresponds to the exists case of a formula: it takes a $\phi \in MSO(\Sigma \cup {c})$ for some constant $c$, ($c$ here is depicted a SigThing of type $\tau$, added onto $\Sigma$ implied in (E ,i $\tau)$ and turns it into a formula in $MSO(\Sigma).$ The second constructor does a similar thing with relations, except it makes the restriction that the added relation can only take one argument, i.e. it must be a set. This is done in the code by specifying that the R in $MSO(\Sigma \cup {R})$ does not have an arbitrary list of argument types $\tau$s but rather a one-element list of argument types, $r$ ($\tau$ :: []).  The third constructor corresponds to creating ands and ors out of smaller formulas, as in the definition. Then, we add the atomic formulae true and false, i.e. $\top$ and $\perp$.
\par Now we come to the most interesting case for the code, the atomic relation formulas. We introduce a datatype called Terms in order to make the definition work. Terms has two constructors, $[]$ (empty) and ,t (add one term). In the add one term case, we see that Terms$ \Sigma$ $\tau$s makes sure that there are symbols in sigma that have type $\tau$ for all $\tau \in \tau$s. In other words: recall that a signature $\Sigma$ is a list of symbols, or placeholders, each of a certain type $\tau$. Terms ensures that there are actually placeholders in $\Sigma$ that want elements of type $\tau$ for every $\tau \in \tau$s. \textcolor{red}{IS THIS RIGHT? THIS IS NECESSARY FOR THE RELATION CONSTRUCTOR BECAUSE.....?}
\par Note that we do not create a not constructor. Instead, we have a function $*(\phi)$ that takes a formula $\phi$ to its negation, i.e. the dual.
\par At this point, we have defined the most basic, fundamental building blocks of Courcelle's Theorem, and their interpretations in Agda. Now let's build upon them, and make the definitions required to prove the theorem.
\subsection {Isomorphisms of Structures}
\par Now that we understand what structures are, we need to define a notion of isomorphism between structures. The mathematical definition for isomorphisms between structures, taken again from the game theory paper, is as follows:
\par Two structures $\mathds{A}$ and $\mathds{B}$ are isomorphic if they are over the same signature $\Sigma$ and there is a bijection $ h: A \rightarrow B$ between the underlying sets $A$ and $B$, such that
\begin{itemize}
\item $\forall$ constants $c \in \Sigma, c^{\mathds{A}}$=nil if and only if $c^{\mathds{B}}$=nil.
\item $h(c^{\mathds{A}})=c^{\mathds{B}}$ for all constants $c \in \Sigma$.
\item $\forall p$-ary relation symbols $R$ in $\Sigma$ and $a_{1}, a_{2}, ... a{p} \in A$,  \\ $(a_{1}, a_{2}, ... a{p}) \in R_{\mathds{A}}$ if and only if $(h(a_{1}), h(a_{2}), ... h(a{p})) \in R_{\mathds{B}}$.
\end{itemize}
\par In order to formalize this notion of isomorphism, which we call iso, in Agda, we make a helper function, preserves, which defines a function f that satisfies the conditions of $h$ above--except the condition that f is a bijection. Then we build our definition of iso off of this f, essentially saying than an isomorphism between two structures A1 and A2 is a function f with the evidence that preserves A1 A2 f holds, and also f has an appropriate inverse.
\begin{code}
preserves :  ∀ {Σ oc1 oc2} (A1 : Structure oc1 Σ) (A2 : Structure oc2 Σ)
               (f : ∀ {τ} → IndividS (fst A1) τ → IndividS (fst A2) τ ) → Type
  preserves (A1 , []) (A2 , []) f = Unit
  preserves (A1 , s1 ,is x) (A2 , s2 ,is xx)  f = preserves (A1 , s1) (A2 , s2) f × (fst (f x) == fst xx)
  preserves (A1 , s1 ,is x) (A2 , s2 ,none)  f = Void
  preserves (A1 , s1 ,none) (A2 , s2 ,is x) f = Void
  preserves (A1 , s1 ,none) (A2 , s2 ,none)  f = preserves (A1 , s1) (A2 , s2)  f
  preserves (A1 , s1 ,rs U1) (A2 , s2 ,rs U2)  f = Σ (λ (p : preserves (A1 , s1) (A2 , s2)  f)
                                                       → (v : IndividsS A1 _ ) → U1 v
                                                       → U2 (mapIndividS f v))
\end{code}
\par Let's see how the function $f : (\text{elements of the set } A1) \rightarrow (\text{elements of the set } A2)$ in preserves satisfies all but the bijection conditions of the function h above. We prove that this by induction over the structures $\mathds{A}1$ and $\mathds{A}2$ that f relates, which corresponds to the proof in the code.
\par As a base case, we have that both $\mathds{A}1$ and $\mathds{A}2$  are empty structures, i.e. they are structures over an empty signature, so all of the conditions of $h$ are satisfied vacuously.
\par Now we begin our inductive steps. First, we have the case where $\mathds{A}1$ = $(A1 , s1 ,is x)$and $\mathds{A}2$ =  $(A2 , s2 ,is xx)$, i.e. both structures are extensions with an Individ. %Individs?
By the inductive hypothesis, we have that there is a function f between $(A1 , s1)$ and  $(A2 , s2)$, such that it upholds all of the conditions of $h$. Then we extend this function $f$ to a function $f'$ that keeps all of f the same, and also maps the new Individ, the extension x, in  $\mathds{A}1$ to the extension xx in $\mathds{A}2$. This satisfies the first property, because by induction $f$ satisfies all the conditions of h; and then this new assignment satisfies the first property because it sends an interpreted element to an interpreted element. (In case it is not clear, the "none" extensions in the structure correspond to a constant being interpreted as nil, and the extensions with Individ correspond to a constant being interpreted by a set element. Broadly, each structure extension corresponds to interpreting a new symbol of a signature.) $f'$ satisfies the second condition of $h$, that $h(c^{\mathds{A}})=c^{\mathds{B}}$ for all constants $c \in \Sigma$: again, by our inductive hypothesis, we only have to pay attention to the assignment of f(x) = xx. Since $\mathds{A}1$ and  $\mathds{A}2$ are mandated to have the same signature, they must be filling in the same constant, call it $c_{i}$, of their signature with this extension. By sending f(x) = xx, we then are sending $c^{\mathds{A}}_{i} \rightarrow c^{\mathds{B}}_{i}$ under $f'$. (The "fst" stuff is just to isolate the set element portion of an IndividS from the information of what set it belongs to---don't worry about it).   \textcolor{red}{is this explanation correct??}
$f'$ satisfies the third condition of $h$ by the inductive hypothesis, because no new relations are added to the signature at this step.  \textcolor{red}{is this  correct?? I feel like no.} Is it more like... all relation tuples that do not contain $c_{i}$ satisfy this property by the inductive hypothesis. Now that we also have $c^{\mathds{A}}_{i} \rightarrow c^{\mathds{B}}_{i}$ under $f'$, any relation symbol R that contains $c_{i}$ will also have this property (????).
\par Now we consider the case where one structure, WLOG suppose $\mathds{A}1$, is extended with a nil (none) and $\mathds{A}2$ is not. This is a violation of condition one of isomorphism above, so we do nothing in this case: Void simply means false, or impossible. %In this case, we do not extend f in order for $f$ to satisfy the first condition of $h$.
\par Now, consider the case where both $\mathds{A}1$ and $\mathds{A}2$ are extended with nils. Then we say that our extension $f' = f$, and this satisfies condition one of two structures being isomorphic, and the two conditions of $h$, by the inductive hypothesis.
\par Finally, we get to the case where we extend each structure by a relation tuple, U1 and U2. In this case, we keep $f$ the same, but we require a proof that that the third condition holds for the relation tuples $U1 = R^{\mathds{A}1}_{i}$ and  $U2 = R^{\mathds{A}2}_{i}$. Then the proof that this case upholds all the necessary conditions of isomorphism, besides the fact that $f$ is not a bijection, is similar to the proof for extensions with constants above.
\par You might ask, why are there not instances of where one structure extends with a relation and another with a constant or a nil? This is because the structures are mandated to have the same signature. \textcolor{red}{is this explanation correct??}
\begin{code}
  iso : ∀ {Σ oc1 oc2} (A1 : Structure oc1 Σ) (A2 : Structure oc2 Σ) → Type
  iso A1 A2 = Σ \ (f : ∀ {τ} → IndividS (fst A1) τ → IndividS (fst A2) τ ) → preserves A1 A2 f × (∀ τ → IsEquiv (f {τ})))
\end{code}
\par Finally, we get to the actual Agda definition for an isomorphism between two structures $\mathds{A}1$ and $\mathds{A}2$. iso in Agda is a product type of the function $h$ between set elements of $A1$ and $A2$ such that preserves A1 A2 f, i.e. that f satisfies all the conditions that preserves outlines; and a proof that f has an inverse. (This is the "IsEquiv" function.) So, we see that the Agda construction of isomorphism satisfies all the necessary properties. The helper function, preserves, ensures that  $\forall$ constants $c \in \Sigma, c^{\mathds{A}}$=nil if and only if $c^{\mathds{B}}$=nil by returning void when this condition is not satisfied; and it ensures $f(c^{\mathds{A}})=c^{\mathds{B}}$ for all constants $c \in \Sigma$ and $\forall p$-ary relation symbols $R$ in $\Sigma$ and $a_{1}, a_{2}, ... a{p} \in A$, $(a_{1}, a_{2}, ... a{p}) \in R_{\mathds{A}}$ if and only if $(f(a_{1}), f(a_{2}), ... f(a{p})) \in R_{\mathds{B}}$ by the way it grows the function $f$ upon the IndividS and relation extensions.  And iso adds the condition that $f$ must be a bijection.
\subsection {Compatibility}
\par Although we do not explicitly code a notion of compatibility, or compatible structures in Agda, it is a definition that mathematically underlies other concepts we will encode. Two $\Sigma$-structures $\mathds{A}_{1}$ and $\mathds{A}_{2}$ are compatible if:
\begin{itemize}
\item For all constants $c_{i}$ such that $c^{\mathds{A}_{1}}_{i} \neq$ nil and $c^{\mathds{A}_{2}}_{i} \neq$ nil, then $c^{\mathds{A}_{1}}_{i} = c^{\mathds{A}_{2}}_{i} $
\item The identity function is an isomorphism between $\mathds{A}_{1}[A_{1} \cap A_{2}]$ and $\mathds{A}_{2}[A_{1} \cap A_{2}]$.
\end{itemize}
\subsection{Union of Structures}
\par For reasons that will become clear later, we define a notion of union over two structures $\mathds{A}1$ and $\mathds{A}2$. If two $\Sigma$-structures $\mathds{A}1$ and $\mathds{A}2$ are compatible, we let the $\Sigma$-structure  $\mathds{A}1 \cup \mathds{A}2$ be defined as follows. $\mathds{A}1 \cup \mathds{A}2$ has
\begin{itemize}
\item An underlying set $A:=A_{1} \cup A_{2}$
\item interpretations $R^{A_{1} \cup A_{2}} := R^{A_{1}} \cup R^{A_{2}}$ for all relation symbols $R \in \Sigma$,
\item for constants $c \in \Sigma$, $c^{A_{1} \cup A_{2}} = c^{A_{i}}$ if $c \in interpreted(A_{i})$ for some $i \in {1,2}$, otherwise $c^{A_{1} \cup A_{2}} =$ nil.
\end{itemize}
\subsection{Games}
\par The paper that we base our implementation off of uses games, instead of automata, or fly-automata, etc, to determine if a given MSO sentence holds on a given structure. Model checking games, or MC games, are based off of pebble games, which we define below.
\par [A pebble game $G = (P, M P_{0}, P_{1}, p_{0})$ between two players, say Player 0 and Player 1, consists of a finite set $P$ of positions, two disjoint sets $P_{0}, P_{1} \subset P$ which assign positions to the two players, an initial position $p_{0} \in P$, and an acyclic binary relation $M \subset P \times P$, which specifies the valid moves in the game. (I.e., how to get from one position to another). We only allow moves \textit{from} positions assigned positions assigned to one of the two players, i.e. we require $p \in P_{0} \cup P_{1} \forall (p, p') \in M$. On the other hand, we do allow that positions without outgoing moves are assigned to players. Let $|G| := |P|$ be the size of $G$. At each round of play $i$,  $ 1 \leq i \leq l$, the player assigned to position $p_{i}$ has to pick a valid next position, i.e. a $p_{i+1}$ such that $(p_{i}, p_{i+1}) \in M$. %For $p \in P$, we let $next_{G}(p)={p'
A play of $G$ is a maximal sequence $(p_{0},...,p_{l})$ of positions $p_{0},...,p_{l} \in P_{0} \cup P_{1}$, such that $(p_{i}, p_{i+1}) \in M$, i.e. all positions adjacent in the sequence have a valid move between them. Since M is acyclic, such a play is finite, is said to have $l$ rounds and end in position $p_{l}$. If $p_{l} \in P_{0}$, Player 1 wins, and if $p_{l} \in P_{1}$, Player 0 wins. If $p_{l} \notin P_{0}\cup P_{1}$ then the game is a draw. The object of the game is to force the opposite player into a place where they cannot move. A player is said to have a winning strategy on a game $G$ if and only if they can win the game on every play, no matter what the choices of the other player. Player $i$ has a winning strategy on a game $G$ if and only if
\begin{itemize}
\item $p_{0} \in P_{i}$ and there is a move $(p_{0}, p_{1}) \in M$, for some choice of $p_{1}$ such that Player $i$ has a winning strategy on $subgame_{G}(p_{1})$, or
\item $p_{0} \in P_{1-i}$ and Player $i$ has a winning strategy on $subgame_{G}(p_{1})$ for all valid choices of $p_{1}.$
\end{itemize}
\par A game $G$ is said to be determined if either one of the players has a winnings strategy, otherwise $G$ is undetermined. The game returns either some indication either player 1 or player 2 has a winning strategy, or a proof that the game is a draw.] (all from game theory paper, more or less)
\subsubsection{Model Checking Games}
\par MC games are pebble games specific to a given formula and structure. In the case of MC games, we call one player the falsifier, who wants to show that the formula is false on the given structure, and one player the verifier, who wants to show that the formula is true on the given structure. A model checking game $MC(\mathds{A}, \phi) =  (P, M P_{f}, P_{v}, p_{0})$, over a $\Sigma$-structure $\mathds{A}$ that fully interprets $\Sigma$, and $\phi \in MSO(\Sigma)$, is defined by induction over $\phi$ as follows: we define $p_{0} = (\mathds{A}[\overline{c}^\mathds{A}], \phi)$, where $\overline{c}$ = {all constants $c \in \Sigma$}.
\begin{itemize}
\item If $\phi$ is an atomic formula , i.e. $R(a_{1}, a_{2}, ... a{p})$ or $\neg R(a_{1}, a_{2}, ... a{p})$ for some $R \in \Sigma, (a_{1}, a_{2}, ... a{p}) \in A^{p}$, then $MC(\mathds{A}, \phi) =  (p_{0}, \emptyset, P_{f}, P_{v}, p_{0})$, and $p_{0} \in P_{f}$ if the atomic formula is true (which will make$ P_{f}$, the falsifier, lose) and $p_{0} \in P_{v}$ if the atomic formula is false (which will make$ P_{v}$, the verifier, lose).
\item If $\phi$ is an existential formula,
\item \textcolor{red}{rest of definition.... do you want me to copy the whole thing here? I feel so weird copying.}
\end{itemize}
\par The Agda formulation of MC games is an operation on structures and formulas we call  "$\vdash c$", or "closed truth". Note that instead of "$\vdash c$" being a game, we simply say that for a structure (A , SA) and a formula $\phi$ $(A , SA) \vdash c\phi$ holds if the verifier of an MC game $MC((A, SA), \phi)$ has a winning strategy. If the falsifier has a winning strategy, $(A , SA) \vdash c\phi$ fails. So, in our code, we take the game-theoretic element out of the algorithm; we simply model a structure very similar to the definition of game given in the code. Other than this, however, the code, below, follows the definition of MC games pretty exactly.
\par We have to trudge through some background code before we can give the definition of "$\vdash c$" directly. We define three helper functions, Value, get, and gets, which help us pick out actual elements from the underlying set to fill our symbols with when needed, i.e. when we need to check that $(c^{\mathds{A}}_{1}, ...c^{\mathds{A}}_{1}) \in R^{\mathds{A}}$ for some atomic formula $R(c_{1}...c_{m})$, or that $(c^{\mathds{A}}_{1}, ...c^{\mathds{A}}_{1}) \notin R^{\mathds{A}}$ for $\neg R(c_{1}...c_{m})$, as the definition for MC games specifies.
\begin{code}
 Value : Subset → SigThing → Type
  Value A (i τ) = IndividS A τ
  Value A (r τs) = (IndividsS A τs → Type)
\end{code}
\par Value takes a Subset, usually the underlying set of the structure in question, and a SigThing, i.e. a symbol. In the case that you give it a constant symbol, it returns the interpretation of that symbol. In the case that you give it a relation symbol, it gives you a function that checks to see if a given tuple of the correct type is in the relation.
\begin{code}

  get : ∀ {Σ} {st : SigThing}
      → st ∈ Σ
      → (A : Structure Closed Σ)
      → Value (fst A) st
  get i0 (A , (_ ,is a)) = a
  get i0 (A , (_ ,rs rel)) = rel
  get (iS i1) (A , SA ,is _) = get i1 (A , SA)
  get (iS i1) (A , SA ,rs _) = get i1 (A , SA)
\end{code}
\par Now, get takes a SigThing (symbol) in a signature, a closed structure on that same signature, and returns one of the outputs of Value, listed above. In the case that the structure is extended with a
\begin{code}
  gets : ∀ {Σ} {τs : List Tp}
       → Terms Σ τs
       → (A : Structure Closed Σ)
       → IndividsS (fst A) τs
  gets [] A = <>
  gets (x ,t xs) A = (gets xs A) , (get x A)
\end{code}
\par gets takes Terms $\Sigma$ $\tau$, i.e. a tuple of constant symbols in $\Sigma$, a closed structure, and it returns a tuple of set elements from the underlying set of the structure that are of the correct type.
\par Finally, we can come to our code for closed truth! $\vdash c$ requires a $\Sigma$-structure (A , SA) and $\Sigma$-formula $\phi$.  The input $\Sigma$-structure needs to be closed (recall the datatype OC defined way above: this means, as is required in the definition of MC games, that no constants in $\Sigma$ are interpreted as nil in $\mathds{A}$).
\begin{code}
 _⊩c_ : ∀ {Σ} → Structure Closed Σ → Formula Σ → Type
  (A , SA) ⊩c ∀i τ φ = (a : IndividS A τ) → (A , (SA ,is a)) ⊩c φ
  (A , SA) ⊩c ∃i τ φ = Σ \ (a : IndividS A τ) → (A , (SA ,is a)) ⊩c φ
  (A , SA) ⊩c ∀p τ φ = (P : Unit × IndividS A τ → Type) → (A , (SA ,rs P)) ⊩c φ
  (A , SA) ⊩c ∃p τ φ = Σ \ (P : Unit × IndividS A τ → Type) → (A , (SA ,rs P)) ⊩c φ
  A ⊩c (φ1 ∧ φ2) = A ⊩c φ1 × A ⊩c φ2
  A ⊩c (φ1 ∨ φ2) = Either (A ⊩c φ1) (A ⊩c φ2)
  A ⊩c ⊤ = Unit
  A ⊩c ⊥ = Void
  A ⊩c (R rel xs) = get rel A (gets xs A)
  A ⊩c (¬R rel xs) = (get rel A (gets xs A)) → Void
\end{code}
\par We now show that $\phi$ $(A , SA) \vdash c\phi$ holds if the verifier of an MC game $MC((A, SA), \phi)$ has a winning strategy. We start from the trivial cases: $A \vdash c \top$ and $A \vdash c \perp$. Recall that $\top$ is the special game upon which the verifier always has a winning strategy, and $\perp$ is a similar thing for the falsifier. In our code, $A \vdash c \top$ is defined to be Unit, which is equivalent to true in our code, and $A \vdash c \perp$ is set to Void, which means that $A \vdash c \perp$ is false, it does not hold. So we see on these simple cases, $A \vdash c \phi$ holds only if the verifier has a winning strategy.
\par Now we move onto existentials and universal formulas over constants. If $\phi = \forall c \psi$, for some constant symbol $c$, then in order for $(A , SA) \vdash c\phi$, $(A , (SA \space ,is \space a)) \vdash c\psi$ needs to hold for all $a \in A$ (for all a : IndividS A $\tau$). This corresponds to the fact that in order for the verifier to have a winning strategy on $MC(\mathds{A},\forall i \psi)$ there needs to be a winning strategy on $MC(\mathds{A_{a}},\psi)$ for all $a \in A$, where $\mathds{A_{a}}$ is the $(\Sigma, c)$ extension structure of $\mathds{A}$. (since on universal formulas, the falsifier would go first).
\par Now consider the case where the formula is atomic, i.e. $R(c_{1}, c_{2}, ... c_{p})$ or $\neg R(c_{1}, c_{2}, ... c{p})$ for some $R \in \Sigma$. In the first case, in order for the verifier to win, the formula needs to be true, i.e. that $(c^{\mathds{A}}_{1}, ...c^{\mathds{A}}_{1}) \in R^{\mathds{A}}$. And, in order for the verifier to win, this step needs to be the turn of the falsier, so that the falsifier gets trapped. Since we have done away with the notion of playing a game, we just keep the condition that the formula is true, i.e. $(c^{\mathds{A}}_{1}, ...c^{\mathds{A}}_{1}) \in R^{\mathds{A}}$. The corresponding (R rel xs) constructor in the code is exactly a proof that $(c^{\mathds{A}}_{1}, ...c^{\mathds{A}}_{1}) \in R^{\mathds{A}}$. Firstly, rel is a set that corresponds to a relation and xs corresponds to the tuple of nullary constants $(c_{1}, ... c_{m})$.
gets xs A is an individsS, i.e. a list of set elements of A which interpret the constant symbols specified in $xs$, and get rel A (gets xs A) checks to make sure that this list of set elements is actually inside rel, the interpretation of the relation symbol R in A. So, get rel A (gets xs A) holds only if, indeed,  $(c^{\mathds{A}}_{1}, ...c^{\mathds{A}}_{1}) \in R^{\mathds{A}}$, and so $A \vdash c$ (R rel xs) only holds if this is true. A similar argument works for the negation case, but with the constructor only holding if the elements are not in R.
\par If $\phi = \exists c \psi$, for some constant symbol $c$, then in order for $(A , SA) \vdash c\phi$, there needs to exist some $a \in A$, i.e. some a : IndividS A $\tau$, such that $(A , (SA \space ,is \space a)) \vdash c\psi$. (The $\Sigma  a \rightarrow$ in the code corresponds to "exists an a such that"). This, in turn, corresponds to the fact that in order for the verifier to have a winning strategy on $MC(\mathds{A},\exists c \psi)$, there needs to be just one $a \in A$, one next move, such that the verifier has a winning strategy on the subgame $MC(\mathds{A_{a}},\psi)$. A very similar explanation works with the cases $\phi \in  {\forall R \psi, \exists R \psi}$ where R is written in the code as p.
\par In the case where $\phi = \psi1 \wedge \psi2$, the falsifier would go first, so the verifier needs winning strategies on both subgames, i.e. $(A , SA) \vdash c \psi1 \wedge \psi2$ requires that both $(A , SA) \vdash c \psi1$ and $(A , SA) \vdash c \psi 2$.
\par %first define general notion of games as moves and tokens; without formulas and structure
%Then define the MC game for a formula and a structure
\subsubsection{EMC Games}
\par Model checking games are all well and good, but some structures have nils in them, and MC games do not accept that. More pointedly, MC games on their own do not possess the qualities that we need them to have in order for them to be useful in giving an algorithm for Courcelle's Theorem. The reason why this is demands some explanation of what the overarching algorithm looks like, which we will go into more detail about later but merits some explanation now. Essentially, in order to prevent exponential blow up for the algorithm at every quantifier (as occurs on the automata implementation of Courcelle's Theorem), we never want to check a quantifier over the entire set of nodes and edges in a graph. Instead of looking at the whole graph at once, the algorithm in Kneiss et. al. looks at in pieces: for a structure $\mathds{A}$, the pieces are the restrictions $\mathds{A}[A_{i}]$ associated with each node of the tree decomposition. (Recall that for a node $i$ of a tree decomposition, we let $A_{i}=\bigcup_{j \text{at or below } i} X_{j}$, and $\mathds{A}[A_{i}]$ is the restriction of $\mathds{A}$ to that subset.) The algorithm that we use to prove Courcelle's theorem traverses the given tree decomposition bottom up, checking to see if the formula holds on $\mathds{A}[A_{i}]$ for each node, starting at the empty leaves, and adding a little bit of the set at a time.
\par This may sound like malarkey: first of all, these subsets do not fully interpret the signature, and secondly, how do we know if there is a winning strategy on one of these smaller games that it propagates to a winning strategy on the overall game? To satisfy the first point, we need games that can handle nil assignments, which is the first handy property of EMC games. Additionally, consider the idea that, if you can satisfy an equation with a structure full of nil assignments, you can satisfy that equation on a structure with any interpretations for those nil assignments, because the elements that are interpreted as nil are not doing anything consequential if they don't prevent the MSO formula from being satisfied. So having a winning strategy on some game made with a restricted structure, chock full of nils as it may be, should propagate to having a winning strategy on the full game, since giving specific values to constants that weren't affecting the formula anyway is not going to change anything. But even with this fact, we still have to come up with a way of propagating the winning strategy upward, of seamlessly transitioning from a game on a restricted structure to a game on the a larger restriction, or the whole structure.
\par Consider the fact that for each node $i$ in a tree-decomposition $T$ of a structure $\mathds{A}$, while we have  $A_{i}=\bigcup_{j \text{at or below } i} X_{j}$, we can also consider $A \setminus A_{i} := B_{i}$, the set of everything in A not yet taken into account by the tree decomposition. This set is often called, illustratively, the future of $A_{i}$. Just as we can restrict $\mathds{A}[A_{i}]$, we can define a structure $\mathds{A}[B_{i}]$. Recalling our notion of the union of two structures from earlier, see that at any node $i$, $\mathds{A}=\mathds{A}[A_{i}] \cup \mathds{A}[B_{i}]$. So, the condition we want is that, if we have a winning strategy on a game for $\mathds{A}[A_{i}]$ and $\phi$, then we want to propagate this to a winning strategy on $\mathds{A}[A_{i}] \cup \mathds{A}[B_{i}] $ and $\phi$. Thankfully, Kneiss et. al. created EMCs with the property that are well-defined on taking the union of structures (provided the structures are compatible).
\par To summarize, Kneis et. al. developed another form of model checking game, which does allow structures with nils, and is well defined over taking unions of compatible structures, i.e. if there is a winning strategy for a game over $\mathds{A}$ and $\phi$, that translates to a winning strategy on $\mathds{A} \cup \mathds{B}$ and $\phi$ for two compatible structures $\mathds{A}$ and $\mathds{B}$.  In the Kneiss et. al. paper, an EMC is defined to keep track of what bag of the tree decomposition it is on. We found this unnecessary in the code, but provide the original definition here for clarity.
\par [An extended model checking game $EMC(\mathds{A}, X, \phi) = (P, M P_{f}, P_{v}, p_{0})$, over a $\Sigma$-structure $\mathds{A}$, a set X $\subset$ A, and $\phi \in MSO(\Sigma)$, is defined over induction over the structure of $\phi$ as follows. Let $p_{0} = (\mathds{A}[\overline{c}^\mathds{A} \cup X], \phi)$, where again $\overline{c}$ = {all constants $c \in \Sigma$}. If $\phi$ is an atomic formula, then $EMC(\mathds{A}, X, \phi) = ({p_{0}}, \emptyset, P_{f}, P_{v}, p_{0})$, where $p_{0} \in P_{f} $ if and only if there are no nils in the relation tuple and the formula is true; i.e. if the formula is $R(c_{1}, c_{2}, ... c_{p})$ or $\neg R(c_{1}, c_{2}, ... c{p})$ for some $R \in \Sigma$, then each $c^{\mathds{A}}_{i}$ in $(c^{\mathds{A}}_{1}, ...c^{\mathds{A}}_{1})$ must not be nil, and the formula is actually true, i.e.  $(c^{\mathds{A}}_{1}, ...c^{\mathds{A}}_{1}) \in R^{\mathds{A}}$. Again, as explained for MC games, this will make the verifier win. Alternatively, $p_{0} \in P_{v}$ if the tuple $(c_{1}, c_{2}, ... c_{p})$ is fully interpreted, and the atomic formula is false (which will make$ P_{v}$, the verifier, lose).
\par If $\phi \in {\psi_{1} \wedge \psi_{2}, \psi_{1} \vee \psi_{2}, \exists R \psi, \forall R \psi} $ for some relation R, then EMC games are defined exactly the same as MC games above.
\par If $\phi \in {\exists c \psi, \forall c \psi}$ for some constant $c$, then the definition for an EMC game is almost exactly the same as that of an MC game, except that we also add the possibility of extending our structure $\mathds{A}$ with a nil, not just elements of $A$. That is, we let $\mathds{A_{u}}$ be the $(\Sigma, c)$ expansion of $\mathds{A}$ as before, but this time we let either $c^{A_{u}} = u \in A$ OR  $c^{A_{u}}= nil.$ Let $EMC(\mathds{A}_{u}, X, \psi) = (P_{u}, M_{u}, P_{u,f}, P_{u,v}, p_{u})$ be the corresponding EMC game over $\mathds{A_{u}}, \psi$ as before. Then, $EMC(\mathds{A}, X, \phi) = (P, M P_{f}, P_{v}, p_{0})$ where
\begin{itemize}
\item $P = {p_{0}} \cup \bigcup_{u \in A\cup {nil}} P_{u}$
\item $M = \bigcup_{u \in A\cup {nil}} (M_{u} \cup {p_{0}, p_{u})}$
\item  $P_{f} = {P_{f}'} \cup \bigcup_{u \in A\cup {nil}} P_{f,u}$, where $P_{f}'= {p_{0}}$ iff $\phi = \forall c \psi$ and $\emptyset $otherwise, and similarly
\item  $P_{v} = {P_{v}'} \cup \bigcup_{u \in A\cup {nil}} P_{v, u}$, where $P_{v}'= {p_{0}}$ iff $\phi = \exists c \psi$ and $\emptyset$ otherwise] (paraphrased from Kneiss et all)
\end{itemize}
\par The way that we model EMC games in the code is through a datatype "$\vdash$ o", or open truth. Similar to our definition of closed truth above, we do away with the notion of a game and players, and just outline "$\vdash o$" so that for a structure $\mathds{A}$ and a formula $\sigma$, $\mathds{A} \vdash o \Sigma$ if and only if there is a winning strategy for the verifier on an EMC game $EMC(\mathds{A}, X, \phi)$. Before we can get to this definition, however, we have to explain some of the code leading up to it.
\begin{code}
 ValueOpen : Subset → SigThing → Type
  ValueOpen A (i τ) = Maybe (IndividS A τ)
  ValueOpen A (r τs) = (IndividsS A τs → Type)

  getOpen : ∀ {Σ oc} {st : SigThing}
      → st ∈ Σ
      → (A : Structure oc Σ)
      → ValueOpen (fst A) st
  getOpen i0 (A , (_ ,is a)) = Some a
  getOpen i0 (A , (_ ,rs rel)) = rel
  getOpen i0 (A , (_ ,none)) = None
  getOpen (iS i1) (A , SA ,is _) = getOpen i1 (A , SA)
  getOpen (iS i1) (A , SA ,rs _) = getOpen i1 (A , SA)
  getOpen (iS i1) (A , SA ,none) = getOpen i1 (A , SA)


  getsOpen : ∀ {Σ oc} {τs : List Tp}
       → Terms Σ τs
       → (A : Structure oc Σ)
       → Maybe (IndividsS (fst A) τs)
  getsOpen [] A = Some <>
  getsOpen (x ,t xs) A  with  (getsOpen xs A) | (getOpen x A)
  ... | Some vs | Some v = Some (vs , v)
  ... | _ | _ = None
\end{code}
\par Similar to our code for closed truth, we define ValueOpen, getOpen, and getsOpen, which perform almost the same functions that Value, get, and gets do, except that they all take into account the fact that for open truth/EMC games, we could be dealing with open structures, which may contain nils. So, ValueOpen, instead of returning an set element that is an interpretation when given a nullary constant, gives either None (for nil) or Some v (for some set element). This propagates through getOpen and getsOpen: getOpen .... \textcolor{red}{HELP}. getsOpen, similar to gets, when given terms (a tuple of constant symbols) and a structure, returns a tuple of elements that interpret the constant symbols--except that, if even one of the symbols is not interpreted, it returns a None value instead of a tuple of set elements.
\par Differing from what we did for closed truth, we defined predicates on formulae that determined whether a given formula was existential $(\phi = \exists R \psi, \exists c \psi, \psi_{1} \vee \psi_{2})$ universal $(\phi = \forall R \psi, \forall c \psi, \psi_{1} \wedge \psi_{2})$, or an atomic relation ($R$ or $\neg R$ for some arity(R)-tuple of constants).
\begin{code}
 data isE {Σ : Signature} : Formula Σ → Type where
    isEexistsi : ∀ {τ} {φ : Formula (i τ :: Σ )} → isE (∃i τ φ)
    isEexistsr :  ∀ {τ} {φ : Formula (r (τ :: []) :: Σ )} → isE (∃p τ φ)
    isEor :  ∀ {φ1 φ2 : Formula Σ } → isE (φ1 ∨ φ2)
    isEfalse : ∀ {φ : Formula Σ } → isE ⊥

  data isU {Σ : Signature} : Formula Σ → Type where
    isUforalli : ∀ {τ} {φ : Formula (i τ :: Σ )} → isU (∀i τ φ)
    isUforallr : ∀ {τ} {φ : Formula (r (τ :: []) :: Σ )} → isU (∀p τ φ)
    isUand :  ∀ {φ1 φ2 : Formula Σ } → isU (φ1 ∧ φ2)
    isUtrue :  ∀ {φ : Formula Σ } → isU ⊤

  data isR {Σ : Signature} : Formula Σ → Type where
    isr : ∀ {τs} {r : r τs ∈ Σ} {xs} → isR (R r xs)
    isnotr : ∀ {τs} {r : r τs ∈ Σ} {xs} → isR (¬R r xs)
\end{code}
\par Based on these different types of formulae, we defined a notion of a branch, of which there are universal branches and existential branches. Think of a branch as an edge between two nodes in a game: it keeps track of which formula and structure you are traveling from and towards. (For as you go through a game, your formula and structure shrinks). So if there is a node (i.e. a position in the definition above) %is this right??
$(\mathds{A}, \phi)$ where one possible next move is to $(\mathds{A} ', \phi ')$, then there will be a branch "branch $\mathds{A}$ $\phi$  $\mathds{A} '$ $\phi '$" to in the game to show that, as we will see further below in our definition of game.  %is this right?
Included below is only the universal branch code, as the existential branch code is quite similar.
\begin{code}
data ubranch {Σ1 : Signature} : ∀ {Σ2 : Signature} {oc1 oc2} (A1 : Structure oc1 Σ1) (φ1 : Formula Σ1)
                                  (A2 : StructureS oc2 (fst A1) Σ2) (φ2 : Formula Σ2) → Type where
    ufstb : ∀ {oc} {A1 : Structure oc Σ1} → {φ1 φ2 : Formula Σ1} → ubranch A1 (φ1 ∧ φ2) (snd A1) φ1
    usndb : ∀ {oc} {A1 : Structure oc Σ1} → {φ1 φ2 : Formula Σ1} → ubranch A1 (φ1 ∧ φ2) (snd A1) φ2
    uforallb : ∀ {oc} {τ} {A1 : Structure oc Σ1} → {φ : Formula (i τ :: Σ1 )} (a : IndividS (fst A1) τ)
                                                 → ubranch A1 (∀i τ φ) ( (snd A1) ,is a) φ
    uforallnil : ∀ {oc} {τ} {A1 : Structure oc Σ1} → {φ : Formula (i τ :: Σ1 )}
                                                   → ubranch A1 (∀i τ φ) ((snd A1) ,none) φ
    uforallr : ∀ {oc} {τ} {A1 : Structure oc Σ1} → {φ : Formula (r (τ :: []) :: Σ1 )} (r : IndividsS (fst A1) (τ :: []) → Type)
                                                 → ubranch A1 (∀p τ φ) ( (snd A1) ,rs r) φ
\end{code}
\par And from notions of existential and universal branches, we get an overarching branch type: it has one constructor for branches from existential formulas (ebr) , and one constructor for branches from universal formulas (ubr). We don't need a constructor for atomic formulas because there will never be a branch from an atomic formula, only a branch to one.
\begin{code}
data branch {Σ1 : Signature} : ∀ { Σ2 : Signature} {oc1 oc2} (A1 : Structure oc1 Σ1) (φ1 : Formula Σ1)
                                 (A2 : StructureS oc2 (fst A1)  Σ2) (φ2 : Formula Σ2) → Type where
    ebr : ∀ {Σ2} {oc1 oc2} {A1 : Structure oc1 Σ1} {φ1 : Formula Σ1} {A2 : StructureS  oc2 (fst A1) Σ2} {φ2 : Formula Σ2}
            → isE φ1 → ebranch A1 φ1 A2 φ2 → branch A1 φ1 A2 φ2
    ubr : ∀ {Σ2} {oc1 oc2} {A1 : Structure oc1 Σ1} {φ1 : Formula Σ1} {A2 : StructureS oc2 (fst A1) Σ2} {φ2 : Formula Σ2}
            → isU φ1 → ubranch A1 φ1 A2 φ2 → branch A1 φ1 A2 φ2
\end{code}
\par Finally, we can look at the code for open truth, our Agda encoding of an EMC game. It has four constructors: provesu (for proving universal formulas), provese (for proving existential formulas), provesbase and provesnotbase (both for atomic formulas). As noted when we explained closed truth and MC games, we take the game element out of the EMC game. We model EMC games with a datatype "$\vdash o$" such that for a structure $\mathds{A}$ and a formula $\phi$, $\mathds{A} \vdash o \phi$ if and only if there is a winning strategy for the verifier on an EMC game $EMC(\mathds{A}, X, \phi)$.
\begin{code}
data _⊩o_ {oc : _} {Σ : _} (A : Structure oc Σ) : Formula Σ → Type where
    provesu : {φ : Formula Σ}
            → isU φ
            → (∀ {Σ' oc'} {A' : StructureS oc' (fst A) Σ'} {φ'} → ubranch A φ A' φ' → (fst A , A') ⊩o φ')
            → A ⊩o φ
    provese : ∀ {Σ' oc'} {A' : StructureS oc' (fst A) Σ'} {φ : Formula Σ} {φ'}
            → isE φ
            → ebranch A φ A' φ' → (fst A , A') ⊩o φ'
            → A ⊩o φ
    provesbase : ∀ {τs} {rel} {xs : Terms _ τs} vs → ((getsOpen xs A) == (Some vs)) → (getOpen rel A) (vs) → A ⊩o (R rel xs)
    provesnotbase : ∀ {τs} {rel} {xs : Terms _ τs}
                  → (vs : _) → ((getsOpen xs A == (Some vs)))
                  → ((getOpen rel A) (vs) → Void)
                  →  A ⊩o (¬R rel xs)
\end{code}
\par Let's see how works. Consider the provesbase case in the code, which corresponds to the place in the EMC definition where the formula is $R(c_{1}, ...c_{m})$ for some relation symbol $R$ in $\Sigma$. In the mathematical definition, in order for the verifier to win in this case, the atomic formula needs to actually be correct, and it should be the falsifier's turn. Since we have taken the notion of players in the game out, we only need the proof that the atomic formula is true. And this is exactly what the provesbase constructor is: a proof that the formula holds. Given a tuple, vs, of elements in the underlying set (i.e. vs : IndividsS $A$ $\tau s$) ((getsOpen xs A) == (Some vs)) is a proof that the xs, i.e. the tuple $(c_{1}, ...c_{m})$ in the formula $R(c_{1}, ...c_{m})$ is actually interpreted as this tuple of set elements vs, i.e. there are no nils. We can see this because getsOpen takes a list of constant symbols (Terms $\Sigma \tau s$) and a structure, and makes sure that each of those symbols is interpreted on that structure (i.e. returns "Some v" in ValueOpen). \textcolor{red}{(Or is it that  ((getsOpen xs A) == (Some vs)) ensures that all of the elements in the given tuple at that node are interpreted, i.e. not nil, because getsOpen takes a list of constant symbols (Terms $\Sigma \tau s$) and a structure, and makes sure that each of those symbols is interpreted on that structure (i.e. returns "Some v" in ValueOpen).?} Then, (getOpen rel A) (vs) checks to make sure that vs, the actual tuple of elements of A (the IndividsS-A-$\tau$s), is actually in $R^{\mathds{A}}$. We see this because getOpen will return a ValueOpen for this relation rel on A, i.e. a function that checks if a given tuple is in a given relation, and so in (getOpen rel A) (vs) we are using that given function to check if $vs \in R^{\mathds{A}}$. A similar proof will show that the provesnotbase constructor is a proof that $\neg R(c_{1}, ...c_{m})$ holds, i.e. $(c^{\mathds{A}}_{1}, ...c^{\mathds{A}}_{m}) \notin R^{\mathds{A}}$. The only real difference is that in the provesnotbase constructor, the ((getOpen rel A) (vs) $\rightarrow$ Void) signifies that the tuple vs is not in $R^{\mathds{A}}$.
\par Now let's consider the provesu constructor. This maps to the case in the definition where we have any universal formula: $\phi \in {\forall c \psi, \forall R \psi, \psi_{1} \wedge \psi_{2}}$. The provesu constructor is a proof that
\begin{enumerate}
\item The formula is universal (IsU $\phi$)
\item For all $\Sigma '$-structures $\mathds{A}'$ with the same underlying set as $\mathds{A}$, and all $\Sigma '$-formulas $\phi '$, if there's a branch (a ubranch, since we're in the universal case) between $\mathds{A}$, $\phi$ and $\mathds{A}'$ $\phi '$, then $\mathds{A}' \vdash o \phi '$
\end{enumerate}
\par Note that depending on what exact formula $\phi$ is, the ubranches from $\phi$ will branch to different  $\mathds{A}'$, $\phi '$-- we don't make a separate constructor for each case. But if, for example, the formula was $\forall c \psi$ for some constant $c$, then there would be a ubranch for $\mathds{A_{a}}$ for all $a \in A$, where $\mathds{A_{a}}$ is a $\Sigma , c$ extension of $\mathds{A}$ with c interpreted as $a$ for all $a \in A$. This corresponds to a winning strategy for the verifier because, since the falsifier gets to choose the next move on a universal quantifier, the verifier needs a winning strategy on every subgame that the falsifier could move to. We interpret this as $\mathds{A}' \vdash o \phi '$ for every possible $mathds{A}'$, $\phi '$ we can branch to from $\mathds{A}$, $\phi$.
\par A very similar explanation to the one above works for the provese constructor. In this case, we just need to show that the formula is existential, and that $\mathds{A}' \vdash o \phi '$ for one possible $mathds{A}'$, $\phi '$ we can branch to from $\mathds{A}$, $\phi$. This corresponds to the verifier having a winning strategy on a corresponding EMC game because since the verifer gets to choose the next move on existentials, we only need to find one subgame that the verifier can win, i.e. where  $\mathds{A}' \vdash o \phi '$. Again, the specific subgames that are checked depend on the ebranch constructor. We also have a definition,  $ \vdash o $false, which takes a structure and a formula as before and shows that the formula is false on that structure. This corresponds to a falsifier having a winnings strategy on an analogous EMC game, and we define it as a  $ \vdash o $ that proves the negation of the formula given.
\subsection{Reduced Games}
\par As described above, the algorithm used to prove Courcelle's theorem in the Kneiss paper runs through an entire EMC game on each node of the tree decomposition, and propagating undecided games upward through the tree decomposition until we have enough data to come to a definitive answer as to whether or not the formula holds on the given structure. In order to further reduce the time of the algorithm, we want to be running games as efficiently as possible. In order to do this, we want to keep as few possible next positions (analogously in our code, as few branches) as possible. This way, we have fewer places to move to at each step, and so our game becomes much smaller. \textcolor{red}{better beginning of explanation? In order to keep this process and fast as possible, we would like to keep track of only the necessary information as we propagate games upward. If we are able to achieve a winning or losing strategy on a game at a given node, we want to exit the algorithm there since we've found out answer. If our game is undecided, we still don't have to keep all information that is available to us: for example, if our formula is universal, we don't have to keep track of all of the different subgames that prove the formula true.}
\par With this in mind, we introduce another game-like structure in the Agda code, which will become the underlying type for something called a reduced game, which will keep track of only the information from any given game that we absolutely need. The explanation for all of this will come later, but because of the way the code is structured, we will introduce a constructor called $\vdash s$, which we call a "raw game tree", now.
\begin{code}
 data _⊩s_ {oc : _} {Σ : _} (A : Structure oc Σ) (φ : Formula Σ) : Type where
    leaf : (isR φ) → A ⊩s φ
    node : (bs : Branches A φ)
         → (∀ {Σ'} {oc'} {A' : StructureS oc' (fst A) Σ'} {φ'} b
         → (branchto A' φ' b) ∈ bs → ((fst A , A') ⊩s φ'))
         → A ⊩s φ
\end{code}
\par A $\vdash s$ is a game that is either atomic, or has a certain set of branches, although which branches is not specified. That is, it does not require the exact set of subgames/outward branches that opentruth or closed truth require. We enclose the code below. See that a $\vdash s$ is a datatype with two constructors, leaf and node. The leaf constructor is simply a proof that the formula is atomic; there are no outward branches, i.e. subgames. The node constructor is a product type, consisting of (1) of a list of branches (bs) from the given structure A and formula $\phi$ (i.e. the game position that has structure A and formula $\phi$), and (2) a proof that for all structure, formula pairs $A', \phi '$ (i.e. positions) that any branch $bi \in bs$ points toward, $A' \vdash s \phi'$. We can also think of (2) as a function that takes a branch b, a proof that b is in the list of branches of some gametree gt, and returns a gametree on the structure that b branches towards.
\par Note the difference between opentruth, closedtruth and gametrees: as mentioned earlier, there are no specifications on the branches of a gametree---unlike for the open truth and closed truth datatypes, if the formula $\phi = \psi_{1} \wedge \psi_{2}$, there is no requirement in a gametree that there be a branch for both $\psi_{1}$ and $\psi_{2}$. There's just some unspecified list of branches; and what goes in that list will become clear later.
\par Continuing from the conversation above about throwing out unnecessary information in games, how do we decide which next positions (or branches) to keep and which ones to throw away? To help answer this question, we introduce a concept of \textbf{equivalent games}.
\subsubsection{Position Equivalence}
\par Consider a game $EMC(\mathds{A}, X, \phi)$. Two positions $p_{1}, p_{2}$ are position-equivalent, denoted by $p_{1} \cong p_{2}$ if and only if
\begin{itemize}
\item $p_{1} = (\mathds{H}_{1}, X, \phi)$ and $p_{2} = (\mathds{H}_{2}, X, \phi)$ for some formula $\phi$ and set $X \subset \mathds{H}_{1} \cap \mathds{H}_{2}.$
\item There is an isomorphism $h : H_{1} \rightarrow H_{2}$ such between $\mathds{H}_{1}$ and $\mathds{H}_{2}$, such that $h(a)=a$ for all $a \in X$.
\end{itemize}
\par Let's take a look at the Agda encoding of position equivalence. We define position equivalence with two functions, positionequiv' and positionequiv. We discuss positionEquiv first--it may be helpful to look back at the definition and explanation of the function iso (for isomorphism between structures) above, or otherwise just accept that iso called on two structures gives us an isomorphism between them. Also note that$constants(\mathds{A_{i}})$ is the set of elements of $A_{i}$ that were used as interpretations of constants in $\mathds{A_{i}}.$ (The code is below). positionEquiv takes two structures, A1 and A2, the bag X that they share, proof that $X \subset A1$ and $X \subset A2$  (so that $X \subset A1 \cap A2$), proof that X is decidable (which will go away when we change our definition of subset). positionEquiv holds on these inputs if there is a function $h$ that satisfies iso $\mathds{A}_1[X \cap constants(\mathds{A_{1}})]$ $\mathds{A}_2[X \cap constants(\mathds{A_{2}})]$, i.e. is an isomorphism between $\mathds{A}_1[X \cap constants(\mathds{A_{1}})]$ $\mathds{A}_2[X \cap constants(\mathds{A_{2}})]$, such that $\forall x \in X,$ $h(x) = x$. All of the little functions such as subLUB, constantsDec, unionDec, and promoteIndividS are all just little fixes to convince Agda that everything is the correct type, in the correct subset, etc. (For example, unionDec is a proof that the union of two decidable sets is decidable.) We won't go into these functions, but if the reader is curious, the source code is attached.
\begin{code}
positionEquiv : ∀ {Σ oc1 oc2} (A1 : Structure oc1 Σ) (A2 : Structure oc2 Σ)
                  (X : Subset)  (XinA1 : Sub X (fst A1)) (XinA2 : Sub X (fst A2))
                → DecidableSub X
                → Type
  positionEquiv A1 A2 X X⊆A1 X⊆A2 decX = Σ \ (h : iso (restriction A1 (union (constants A1) X)
                                                                   (unionDec {S1 = constants A1} {S2 = X} (constantsDec A1) decX) (subLUB (constantSub A1) X⊆A1))
                                                      (restriction A2 (union (constants A2) X)
                                                                   (unionDec {S1 = constants A2} {S2 = X} (constantsDec A2) decX) (subLUB (constantSub A2) X⊆A2)))
                                         → ∀ {τ} (x : IndividS X τ) → fst h (promoteIndividS (subINR {A = constants A1} {B = X}) x) ==
                                                      promoteIndividS (subINR {A = constants A2} {B = X}) x
\end{code}
\par Now we must show why this code is a sufficient definition for positionEquiv above--certainly, at first glance, it seems like it may fall short because we don't have an isomorphism over the entire structure but only the structure restricted to those elements that have been interpreted as constants and the relevant bag, X. But note that this is simply a difference in labeling, not of content. Recall that the position $p_{0}$ of a game $EMC(\mathds{A}, X, \phi) =  (P, M P_{f}, P_{v}, p_{0})$ is defined as $p_{0} = (\mathds{A}[\overline{c}^\mathds{A} \cup X], \phi)$, where $\overline{c}$ = {all constants $c \in \Sigma$}. Note that the structure at a position is by definition the overall structure restricted to the set elements that are interpreted as constants along with the relevant bag $X$. However, in the Agda code, we don't have a specific type for positions, we just have $\vdash c$ and $\vdash o$ which look like trees with branches between structures, with the entire structure as a label for each node. So, we take this restriction to $\mathds{A}[\overline{c}^\mathds{A} \cup X]$ only when we define position equivalence, to make it match the mathematical definition, where this restriction is implicit. So, the mathematical definition and the code in fact have the same requirements.
\par Quickly, we include our code for positionEquiv'; this does exactly the work that positionEquiv does except it changes the accepted input type slightly so that it works more seamlessly with the rest of the code.
\begin{code}
  positionEquiv' : ∀ {Σ oc1 oc2} (A1 : Structure oc1 Σ) (A2 : Structure oc2 Σ) → fixed (fst A1) (fst A2)  → Type
  positionEquiv' A1 A2 (X , (X⊆A1 ,  X⊆A2) ,  decX )  = positionEquiv A1 A2 X X⊆A1  X⊆A2 decX
\end{code}
\subsubsection{Game Equivalence}
\par We say that two games $G_{1}= (P_{1}, M_{1}, p_{1}), G_{2}= (P_{2}, M_{2}, p_{2})$ are equivalent, denoted $G_{1} \cong G_{2}$, if $p_{1} \cong p_{2}$, and there is a bijection $\pi :$ subgames($G_{1}$) $\rightarrow$ subgames($G_{2}$), such that  $G' \cong \pi (G)$ $\forall G' \in$ subgames($G_{1})$.
\par Now, let's look at our code for proving that two games are equivalent. We have two functions, gameEquiv and gameEquiv' defined mutually, that do this job. These functions rely on a helper definition, BranchBijection. BranchBijection, which is enclosed below, does exactly what it sounds like: it is the proof of a bijection between two sets of branches. (The type Branches is simply a list of branches, which we defined earlier).
\begin{code}
 BranchBijection : {Σ : Signature} {oc1 oc2 : _} (A1 : Structure oc1 Σ) (A2 : Structure oc2 Σ) (φ : Formula Σ)
                                                 → Branches A1 φ → Branches A2 φ → Type
 BranchBijection A1 A2 φ branches1 branches2 =
                  ∀ {Σ' φ'} →
                    Equiv (Σ (λ oc' → Σ (λ (A' : StructureS oc' (fst A1) Σ') → Σ \ b → (branchto A' φ' b) ∈ branches1)))
                          (Σ (λ oc' → Σ (λ (A' : StructureS oc' (fst A2) Σ') → Σ \ b → (branchto A' φ' b) ∈ branches2)))

\end{code}
\par BranchBijection takes two structures $\mathds{A}_1$, $\mathds{A}_2$, a formula $\phi$, and the list of branches that come out of each structure. BranchBijection holds on these elements if there is a bijection between the set of structures $\bigcup_{i}\mathds{A}_{1,i}$ that  $\mathds{A}_{1}$ branches to, and the set of structures $\bigcup_{i} \mathds{A}_{2,i}$ that $\mathds{A}_{2}$ branches to. The type of the result of BranchBijection is a product type of a function from $\bigcup_{i}\mathds{A}_{1,i}$ to  $\bigcup_{i} \mathds{A}_{2,i}$, and a proof that that function is a bijection, i.e. and inverse function  $\bigcup_{i} \mathds{A}_{2,i}$ to $\bigcup_{i}\mathds{A}_{1,i}$. (This comes from the "Equiv" in the code; but we won't go into an explanation of that).
\par Now we come to the gameEquiv' and gameEquiv functions themselves. gameEquiv takes two $\Sigma$-structures, $\mathds{A}_{1}$ and $\mathds{A}_{2}$, a $\Sigma$-formula $\phi$, a game tree for $\phi$ on $\mathds{A}_{1}$ and $\phi$ on $\mathds{A}_{2}$, and a bag $X$ (this is the "fixed (fst A1) (fst A2)"). gameEquiv holds on these inputs if positionEquiv' holds for the two structures and the bag (f is the bag in the code), and gameEquiv' holds on all the inputs as well.
\begin{code}
 gameEquiv : ∀ {Σ oc1 oc2} (A1 : Structure oc1 Σ) (A2 : Structure oc2 Σ) (φ : Formula Σ) → A1 ⊩s φ → A2 ⊩s φ → fixed (fst A1) (fst A2) → Type --f didn't have the same type but it worked??
    gameEquiv A1 A2 φ g1 g2 f =  positionEquiv' A1 A2 f × gameEquiv' A1 A2 φ g1 g2 f

    gameEquiv' : ∀ {Σ oc1 oc2} (A1 : Structure oc1 Σ) (A2 : Structure oc2 Σ) (φ : Formula Σ) → A1 ⊩s φ → A2 ⊩s φ → fixed (fst A1) (fst A2) → Type
    gameEquiv' A1 A2 φ (leaf x1) (leaf x2) f = Unit
    gameEquiv' A1 A2 φ (leaf x1) (node bs x2) f = Void
    gameEquiv' A1 A2 φ (node bs1 x1) (leaf x2) f = Void
    gameEquiv' A1 A2 φ (node bs1 x1) (node bs2 x2) f = Σ (λ (b : BranchBijection A1 A2 φ bs1 bs2) →
                                                            ∀ {Σ' oc'} {A' : StructureS oc' (fst A1) Σ'} {φ'} bi →
                                                            (brnchi : branchto A' φ' bi ∈ bs1) →
                                                            gameEquiv ((fst A1) , A') ((fst A2) , (fst (snd (fst b (_ , A' , bi , brnchi))))) φ' (x1 bi brnchi)
                                                            (x2 _ (snd (snd (snd (fst b (_ , A' , bi , brnchi))))))
                                                            f)
\end{code}
\par gameEquiv' does most of the work of the recursive calls. It takes the same input as gameEquiv, but here we case on the constructors of the two game trees. If the game trees are both leaves, there are no subgames (i.e. structures that are branched to) and so no recursive calls are needed, the subgames are equivalent vacuously, and gameEquiv' returns Unit, or True. If one gametree is a leaf and the other is a node, there is no possible way for them to be equivalent, so gameEquiv returns Void, or false. Now the interesting case: both gametrees are nodes. Then, gameEquiv' A1 A2 $\phi$ $A1 \vdash s \phi$ $A2 \vdash s \phi$ X holds if there exists a BranchBijection $b$ between the list of branches in the A2, $\phi$ gametree and the list of branches in the $A2, \phi$ gametree, such that for all structures A' (with underlying set A1) and formulas $\phi$' that A1 and $\phi$ branches to, gameEquiv A' b(A') $\phi$' A'$\vdash s \phi^{'}$  b(A')$\vdash s \phi^{'}$ X holds. Through mutual recursion, the two functions determine if two games are equivalent, with gameEquiv keeps on checking the initial positions are equivalent and gameEquiv' keeps sending the correct subgames to gameEquiv to check for position equivalence.
\par %Let's see how this happens in more detail: "$ \Sigma (\lambda$ (b : BranchBijection A1 A2 $\phi$ bs1 bs2) $\rightarrow$" means "there exists a BranchBijection b such that"; " $\forall$ {?' oc'} {A' : StructureS oc' (fst A1) ?'} {?'} bi ?" means "for all branches bi such that";  "(brnchi : branchto A' ?' bi ? bs1), i.e. there is a proof, brnchi, that $bi \in bs1$, the set of branches of the first gametree of input, and gameEquiv
\par If two games are equivalent, they will have the same outcome. \textcolor{red}{what do I do to back this up?} Certainly, for each game $G$, we only need to keep one representative of each equivalence class of  subgames($G$) modulo $\cong$. Additionally, note that for any game $G$, we can discard the subgames where the opposing player, which in our case will always be the falsifier, wins. There is no use in checking a path that is known to fail.  \textcolor{red}{what do I do to back this up?}
\par Reduced Games
\par With this in mind, we give a definition of a \textbf{reduced game}. A reduced $EMC$ game $G$ over a $\Sigma$-structure $\mathds{A}$ and a $\Sigma$-formula $\phi$ is defined by induction as follows:
\begin{itemize}
\item If $\phi$ is an atomic formula, then the reduced game is defined exactly as a regular EMC game.
\item If $\phi$ is not an atomic formula, then all subgames $G'$ of $G$ must be undecided, and further, $\forall G_{1}' \in $ subgames($G$), $\nexists G_{1}'  \in $ subgames($G$) such that $G_{1}' \cong G_{2}'$. That is, all subgames come from distinct equivalence classes in the $\cong$ relation.
\end{itemize}
\par It may be more instructive to think about how to turn an $EMC$ into a reduced $EMC$ than to simply ponder over the definition. Given an EMC, Kneiss et. al. describe an algorithm for making a reduced $EMC$ $G_{red}$ as follows: if the formula in the game is atomic, treat the reduced EMC game as a regular EMC game. Otherwise, recursively compute all of the reduced subgames of the original EMC, and:
\begin{itemize}
\item If the formula is universal, and there is a subgame $G'$ where the falsifier has a winning strategy, then return that the falsifier won. % $\perp$ (i.e., the statement not being true) then return $\perp$ (i.e. that the formula does not hold over the given structure).
If the falsifier does not have a winning strategy on any subgame, then we define the set of subgames of $G{red}$, subgames($G_{red}$) = ($G'_{1}$, ..$G'_{n}$) such that $\forall i$ $G_{i}$ is undecided, and there does not exist a $j$ such that $G_{i} \cong G_{j}$.
\item If the formula is existential, and there is a subgame $G'$ where the verifier has a winning strategy, then return that the verifier won. If the verifier does not have a winning strategy on any subgame, then we define the set of subgames of $G{red}$, subgames($G_{red}$) = ($G'_{1}$, ..$G'_{n}$) such that $\forall i$ $G_{i}$ is undecided, and there does not exist a $j$ such that $G_{i} \cong G_{j}$.
\end{itemize}
\par So, a reduced game $G$ is a game that has not been decided yet, but that retains as little information as possible in order to speed up the overall algorithm. It may seem counterintuitive that we can throw away so much information and still get the same answer as an EMC game, which is what we would like. Let's think about this a bit. Certainly, we want a game that is undecided, because otherwise we can simply leave the entire algorithm and say we've found that the formula is either true or not true on the structure. Once we've established that the game is undecided, however, still not all information is necessary: for example, if our formula is universal, we don't have to keep track of all of the different subgames that prove the formula true. It doesn't help the future of the algorithm to keep track of the fact that one particular interpretation of symbols satisfied the formula, because all it's looking for is one interpretation that does not satisfy the formula. If one subgame in a universal formula returns true, we breathe a sigh of relief and then discard it, and focus on the games that are undecided. Similarly, if a formula is existential, we don't have to keep track of the subgames that end up being false--because we are just looking for one satisfying interpretation of variables. If the reader can accept this, then all that is left to be convinced of is that the result of a reduced game on a structure $\mathds{A}$ and a formula $\phi$ will always be the same as an EMC game on the same formula and structure. A proof of this fact is on our agenda--we will speak more about what is still to be done in this project in the last section.
\par Now we transition to explaining our encoding of a reduced game. There are a few helper functions for this definition. The moving parts are: $\vdash s$ defined above, which is sort of the underlying type for a reduced game, though not a reduced game itself. We can combine this with another definition $isRed$, a proof that a $\vdash s$ gametree is in fact a reduced game. Then, we trivially put these two pieces together in provesR, which is our formulation of a reduced game, i.e. a $\vdash s$ that satisfies isRed $\vdash s$.
\par We go through the Agda code for isRed, a proof that a gametree g1 is a reduced game.
\begin{code}
 isRed : ∀ {Σ oc} (A : Structure oc Σ) (φ : Formula Σ) → A ⊩s φ → (X : fixed1 (fst A)) → Type
  isRed A φ (leaf x) fix = Unit
  isRed A φ (node bs x) fix =  (∀ {Σ' oc'} {A' : StructureS oc' (fst A) Σ'} {φ'} bj → (prfbr : branchto A' φ' bj ∈ bs) →
                                      isRed (fst A , A') φ' (x bj prfbr) fix) ×
                               (isU φ → ∀ {Σ' oc'} {A' : StructureS oc' (fst A) Σ'} {φ'} bi →
                                    Either (branchto A' φ' bi ∈ bs) (Either ((fst A , A') ⊩o φ')
                                    (Σ
                                       (λ oc'' →
                                          Σ
                                          (λ (A'' : StructureS oc'' (fst A) Σ') →
                                             Σ
                                             (λ bj →
                                                Σ
                                                (λ (pfbr2 : branchto A'' φ' bj ∈ bs) →
                                                   (gi : (fst A , A') ⊩s φ') →
                                                   isRed (fst A , A') φ' gi fix →
                                                   gameEquiv (fst A , A') (fst A , A'') φ' gi (x bj pfbr2)
                                                   (lemma1 _ fix)))))))) ×
                               (isE φ → ∀ {Σ' oc'} {A' : StructureS oc' (fst A) Σ'} {φ'} bi →
                               Either (branchto A' φ' bi ∈ bs)
                               (Either ((fst A , A') ⊩o φ' false) (Σ
                                                                     (λ oc'' →
                                                                        Σ
                                                                        (λ (A'' : StructureS oc'' (fst A) Σ') →
                                                                           Σ
                                                                           (λ bj →
                                                                              Σ
                                                                              (λ (pfbr2 : branchto A'' φ' bj ∈ bs) →
                                                                                 (gi : (fst A , A') ⊩s φ') →
                                                                                 isRed (fst A , A') φ' gi fix →
                                                                                 gameEquiv (fst A , A') (fst A , A'') φ' gi (x bj pfbr2)
                                                                                 (lemma1 _ fix))))))))

\end{code}
\par IsRed takes a structure, $\mathds{A}$, a formula $\phi$, a gametree $\mathds{A} \vdash s \phi$, and a bag X. In the case that the gametree is a leaf, which means it has no outward branches, isRed is true vacuously and so the definition for that case is Unit, or true. In the case that the gametree $\mathds{A} \vdash s \phi$ is a node, we have a double product type; there are three requirements appended together. The first one (the code before the first $\times$) requires that for all structureS's A' and formulas $\phi '$ such that there is a branch  $bj \in bs$ that connects ($\mathds{A}$, $\phi$) $\rightarrow$ ((fst $\mathds{A}$, A'), $\phi$'), there is a reduced game on ((fst $\mathds{A}$, A'), $\phi$'), i.e.   isRed (fst A , A') $\phi$ ' (x bj prfbr) fix holds. In case it is confusing that  (x bj prfbr) is miraculously a gametree (fst A , A') $\vdash s$ $\phi$', recall from the definition of $\vdash s$ that the second argument can be thought of as a function that takes a branch and a proof that that branch is in the list of branches corresponding to some gametree, and returns a gametree on the structure that the branch points to. In the code here, we are calling that second argument "x", and we see that bj is a branch, and prfbr is a proof that bj is in bs, i.e. the list of branches of $A \vdash s \phi$. So, (x bj prfbr) is a gametree (fst A , A') $\vdash s$ $\phi$'.
\par Now, for the next two parts of the product type, the first corresponds to when the formula is universal, the other to when the formula is existential (the atomic cases will only happen with a leaf.) Let's tackle the first out of these two, which corresponds to the formula being universal. The first thing required is a proof that the formula is universal, isU $\phi$. Then we need a proof that for all structureS's A' and formulas $\phi '$such that there is a branch bi  between $(\mathds{A}, \phi)$ and (((fst $\mathds{A}$), A'), $\phi '$), either (1) there is a proof that branch is a part of the list of branches of  $\mathds{A} \vdash s \phi$, or (2) Either ((fst A , A') $\vdash$o $\phi$') i.e. the verifier has a winning strategy on the subgame labeled by that structure, formula pair; or (3) there is another structureS, A'', such that (a) there is a branch between $(\mathds{A}, \phi)$ and ((fst A, A''), $\phi$') ; (b) there is a subgame (fst A, A'') $\vdash s \phi$' that is reduced, i.e.  isRed (fst A , A') $\phi$' gi fi (where gi = (fst A, A'') $\vdash s \phi$' and fix = the bag X), and importantly, that there is a proof that this subgame is equivalent to (fst A , A') $\vdash$s $\phi$', i.e.  gameEquiv (fst A , A') (fst A , A'') $\phi$' gi (x bj pfbr2) (lemma1 fix)))))))). See that this corresponds exactly to the definition that we outlined for reduced games above: in the case of universal formulas, all subgames are true or undecided, and we only keep track of (keep in our special list of branches bs) undecided subgames that are not equivalent to one another.
\par The third part of this product type is very similar, except for the fact that instead of insisting that for all subgames, either the verifier has a winning strategy, and then all the other options listed; we ask that for all subgames, either the falsifier has a winning strategy (Either ((fst A , A') $\vdash$o $\phi$' false)) or one of the other options. Again, we see this matches the mathematical definition for reduced games nicely.
\par And finally, we come to provesR, a combiner that defines "a gametree that is reduced", or a reduced game.
\begin{code}
 provesR : ∀ {Σ oc} (A : Structure oc Σ) (φ : Formula Σ) (X : fixed1 (fst A))  → Type
  provesR  A φ X = Σ (λ (game : A ⊩s φ) → isRed A φ game X)
\end{code}
\par provesR takes a structure $\mathds{A}$, a formula $\phi$, a gametree $\mathds{A} \vdash s \phi$, and a bag X, and gives a proof that there is a gametree $\mathds{A} \vdash s \phi$ such that isRed $\mathds{A}$ $\phi$ $\mathds{A} \vdash s \phi$ X holds.


\par It has been proven that the verifier has a winning strategy on a model-checking game $MC(\mathds{A}, \phi)$ if and only if $\mathds{A} \vdash \phi$ [cite]. But at its heart, a game is a object that allows us to match up a formula and a structure.
\par In our Agda formulation, we take the game-theoretic nature out of the algorithm. We do not have players and games per se. We treat games essentially as trees that map out different possible interpretations of formula variables over a given structure. It looks like a tree: at each node there is a formula constructor, and each branch connects that node to all its possible sub-formulae on the given structure. For example, if there is a $\forall x$ in the formula, where $x$ is a free constant variable, then there will be a node in the tree corresponding to $\forall x$, and each branch coming from that node will correspond to a different possible interpretations of $x$ from the available structure. If there is an "and" in the formula, then there will be an "and" node that has branches to each of its sub-formulae.
\section{Outline of Algorithm}
\par Inputs: A structure $\mathds{A}$, a tree decomposition of that structure $T$, and an MSO formula $\phi$.
\par Output: Either a proof that the formula is false on the given structure, or a  proof that the formula is true on the given structure.
\par The agda function algo takes the inputs above and returns either an opentruth, and opentruth false, or a reduced game. The algorithm is defined by induction on the constructor of the tree decomposition it's given; so it has four cases, intro, delete, join and empty. Let's consider the empty case first. If the input tree decomposition is Empty empty empty, then we must be at a leaf, because otherwise our set B would not be empty. In this case, we perform the naive algorithm on the structure $\mathds{A}[\emptyset]$ and formula $\phi$, and bag $\emptyset$. The naive algorithm either returns that  $\mathds{A}[\emptyset] \vdash o \phi$,  $\mathds{A}[\emptyset] \vdash o \phi$ false, or it returns an undecided reduced game provesR $\mathds{A}[\emptyset]$ $\phi$ $\emptyset$.
\par If the tree decomposition is an Intro constructor, then the algorithm returns the output of the helper function combineIntro of a recursive call to algo on substructure induced by the penultimate node, and the naive algorithm of the structure restricted to the bag. This helper function returns an output of the same type.
\par Why we need having the tree decomposition bound/ it's okay to do naive algorithm on pieces of the game
\par the proofs we came up with about join, forget, introduce... going to need a bit of help recalling these
\section{What's Left}
\begin{code}
  postulate
    fixed2fixed1 : ∀ (A1 A2 : Subset) → fixed A1 A2 → fixed1 A1 --when you have a bag (fixed) that's in 2 subsets, it's in the other one. i.e. fixed -> fixed1
    fixed2fixed2 : ∀ (A1 A2 : Subset) → fixed A1 A2 → fixed1 A2 -- fixed - fixed1 (part 2)
    fixed2union : ∀ (A1 A2 : Subset) → fixed A1 A2 → fixed1 (union A1 A2) -- if you have a decidable subset that's in both A1 and A2, then it's in A1 union A2
    fixed1Sub : ∀ {A1 A2 : Subset} → fixed1 A1 → Sub A1 A2 → fixed1 A2 --if you have X = fixed1 A for any set A, X =fixed1 A' for any superset A' of A
  postulate
    decSingleton : ∀ {τ} → (x : Individ τ) → DecidableSub (singleton {τ = τ} x) --a singleton set is always decidable
    individSinSubset : ∀ {τ} (A : Subset) → ( x : IndividS A τ) → Sub (singleton {τ = τ} (fst x)) A --if x is an IndividS A for some subset A, then it's in A!!


  combineJoin : ∀ {Σ} {oc} (B1 B2 : Subset) (A : Structure oc Σ)  (φ : Formula Σ)  → (decb1 : DecidableSub B1) (decb2 : DecidableSub B2) (X : fixed B1 B2)
                    (b1subAset : Sub B1 (fst A)) (b2subAset : Sub B2 (fst A)) →
                               (recurcall1 : (provesR (restriction A B1 decb1 b1subAset) φ (fixed2fixed1 B1 B2 X)))
                               (recurcall2 : (provesR (restriction A B2 decb2 b2subAset) φ (fixed2fixed2 B1 B2 X)))
                            → let B1∪B2 = (restriction A (union B1 B2) (unionDec {S1 = B1} {B2} decb1 decb2) --uniondec bc we need to show B1UB2 is decidable for restriction
                                                               (subLUB b1subAset b2subAset))
                               in
                                Either (Either (B1∪B2 ⊩o φ) --need to show B1UB2 ⊂ A for restriction
                                               (B1∪B2 ⊩o φ false))
                                               (provesR B1∪B2 φ (fixed2union B1 B2 X)) --subLUB to show B1UB2 ⊂ fst A, fixed2union to say that X is a bag of this union
  combineJoin B1 B2 A φ decb1 decb2 X b1subAset b2subAset recurcall1 recurcall2 = {!!}

  combineIntro : ∀ {Σ} {τ} (B : Subset) (A : Structure Closed Σ) (φ : Formula Σ) (x : IndividS (fst A) τ)
                                        (xnew : (Sub (singleton {τ = τ} (fst x)) (complement B))) --x is not in B, the overall bag so far
                                        (decb : DecidableSub B) (bsubAset : Sub B (fst A)) (X : fixed1 B) → --B is decidable and a subset of universe of A
                                        (recurcall : provesR (restriction A B decb bsubAset) φ X) → --result of recursive call from intro
                                        (nai : provesR (restriction A (union (fst X) (singleton {τ = τ} (fst x))) --result of naive algorithm on A[X∪x] , φ
                                                                      (unionDec {S1 = (fst X)} {singleton (fst x)} (snd (snd X)) (decSingleton (fst x)))
                                                                      (subLUB (subtrans (fst (snd X)) bsubAset) (individSinSubset (fst A) x))) --this was all the restriction
                                                       φ ((fst X) , (subINL , (snd (snd X))))) --formula and bag
                       → let B∪x = (restriction A (union B (singleton {τ = τ} (fst x))) --restriction subset
                                                      (unionDec {S1 = B} {singleton (fst x)} decb (decSingleton (fst x))) --that subset is dec
                                                       (subLUB bsubAset (individSinSubset (fst A) x)))
                         in
                           Either (Either (B∪x ⊩o φ) -- that subset is subset of universe
                                          (B∪x ⊩o φ false))
                                          (provesR B∪x φ ((fst X) , ((subtrans (fst (snd X)) subINL) , (snd (snd X))))) --formula and bag
  combineIntro B A φ x xnew decB bsubAset recurcall nai = {!!}

--fix this: recurcall should have B not B union X
  combineForget : ∀ {Σ} {τ} (B : Subset) (A : Structure Closed Σ)  (φ : Formula Σ) (X : fixed1 B)
                            (x : IndividS (fst X) τ) (decB : DecidableSub B) (bsubAset : Sub B (fst A))
                            (xgone : (Sub (singleton {τ = τ} (fst x))) (complement (fst X))) →
                            (recurcall :   (provesR (restriction A (union B (singleton {τ = τ} (fst x))) (unionDec {S1 = B} {singleton (fst x)} decB (decSingleton {τ = τ} (fst x)))
                            (subLUB bsubAset (subtrans (subtrans (individSinSubset (fst X) x) (fst (snd X))) (bsubAset)))) φ (fixed1Sub X subINL)))
                          → (provesR (restriction A B decB bsubAset) φ X )
  combineForget B A φ X x decB bsubAset xgone recurcall = {!!}


  algorithm : ∀ {Σ} (B : Subset) (X : fixed1 B) (A : Structure Closed Σ) (φ : Formula Σ) (decB : DecidableSub B)(BinA : Sub B (fst A))
                         → (TD : TreeDecomp {Σ = Σ} {A} (fst X) B)
                           → Either (Either (A ⊩o φ) (A ⊩o φ false)) (provesR (restriction A B decB BinA)  φ X)
  algorithm B X A φ decB BinA TD = {!!}

  openToClosed : ∀ {Σ} → (A : Structure Closed Σ) (φ : Formula Σ) → (otruth : A ⊩o φ) → A ⊩c φ --EMC -> MC i.e. Lemma 11
  openToClosed A φ otruth = {!!}

  provesRtoClosed :  ∀ {Σ} → (A : Structure Closed Σ) (φ : Formula Σ) (X : fixed1 (fst A)) → (red : provesR A φ X ) → A ⊩c φ --reducedEMC -> MC i.e. Lemma 13
  provesRtoClosed A φ X redgame = {!!}

\end{code}
% End {{{
\bibliographystyle{plain}
\bibliography{paper}
\printindex
\backmatter
\end{document}
% }}}
