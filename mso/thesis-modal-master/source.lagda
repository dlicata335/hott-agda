
% Setup {{{

  % Imports and Styling {{{
  \RequirePackage{amsmath}
  \documentclass[12pt,final]{westhesis} % add "final" flag when finished
  \def\textmu{}

  %include agda.fmt
  \usepackage{amsmath, amsthm, natbib, textgreek, bussproofs, epigraph, color, float,
              enumerate, url, xcolor, graphicx, hyperref, listings, xfrac}
  \hypersetup{pdftex, backref = true, colorlinks = true, allcolors = {blue}}
  \usepackage{ dsfont }
  \graphicspath{ {images/} }
  \setcounter{tocdepth}{4}
  \setcounter{secnumdepth}{4}
  \newtheorem*{thm}{Theorem}
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

\title{Towards A  Formal Verification of Courcelle's Theorem}
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
\par In this thesis, we present our progress towards a formal verification of Courcelle's Theorem. In order to properly introduce the work, we first explain the background necessary to understanding the statement of Courcelle's Theorem: the kinds of questions we can ask, the kinds of graph we can ask questions about, and the kind of algorithm promised by the theorem. Following this, we delve into a quick description of verification with proof assistants, and discuss our verification tool, Agda. Then we will describe the contributions of this thesis, our work in progress, and our future directions. Finally, before embarking into the main part of the paper, we provide a roadmap for this journey.
\subsection{Courcelle's Theorem}
\par We begin our dive into the details of Courcelle's Theorem: what kinds of questions can we ask, on what kinds of structures, and what sort of a linear algorithm do we get? A slightly more formal statement of the theorem is as follows: Any problem that can be expressed in monadic second order logic can be decided in fixed-parameter tractable linear time on a structure of bounded treewidth.
\subsubsection{What Kinds of Questions: Monadic Second Order Logic Questions}
\par The kinds of questions we can ask are those expressible in Monadic Second Order Logic, or \textbf{MSO}. MSO is an extension of first order logic which, along with all of the capabilities of first order logic, introduces set variables, membership in these sets, and quantification over sets. MSO can also be seen as a restirction of second order logic where quantification is only allowed over unary relations, i.e. sets.  However, no matter which way we look at it,  we cannot quantify over relations that are not sets, i.e. that are not unary. For example, suppose we model a graph $G$ as a set of verticies $V$ and a binary relation $E(x,y)$, where $x$ and $y$ are vertices, to symbolize edges. Then suppose we wanted to see if there existed a binary relation $U(x,y)$ on $G$ such that
\[ \exists U(x,y)(U(x,y) \leftrightarrow E(x,y)\wedge E(y,x))
\]
In other words, are there bidirectional edges in $G$? We cannot ask this question because it quantifies over a binary relation, $U$. \textcolor{red}{I thought the whole reason why we put edges in the underlying set is because we can't quantify over them because of the monadic part of MSO.How do I motivate putting edges in the underlying set if we don't quantify over them anyway?}
\par Even without quantification over non-unary relations, MSO manages to express quite a few NP hard problems: $k$-colorability for fixed $k$, vertex cover, and dominating set, to name a few. Below are the MSO representations of Vertex Cover and Dominating Set. $R$ is a set of verticies, in each formula, and $Edge(x,y)$ denotes the fact that there is an edge between verticies $x$ and $y$, i.e. the tuple $(x,y) \in$ the relation $Edge$.
\[\text{Vertex Cover}(G)=\exists R \forall x \forall y (\neg Edge(x , y) \vee x \in R \vee y ∈ R)
\]
\[
\text{Dominating Set}(G)= \exists R \forall x(x\in R \vee (\exists y(y\in R \wedge Edge(x, y))))
\]
\par Note that, of course, we can include, the edge relation, and other $p$-ary relations for $r\geq 1$ in the formula, we simply cannot quantify over them. However, there is a trick to get around not being able to quantify over edges, taken from Courcelle\cite{graphrewrite} which we implement in our code. Instead of expressing edges as a binary relation, we model graphs as simply a set, where the set elements can represent veritices or edges of the graph. This way, edges are simply set elements, which we can quantify over in MSO logic, instead of a binary relation, which we cannot quantify over. To ensure that the two different types of set elements do not get confused in our code, we have set elements carry a bit of data with them, saying what type (node or edge) they are.
\par Beyond this quick fix of quantifying over edges, MSO still has limitations. There is no way to count in MSO, so while finding out that there is a vertex cover of a dominating set of a given graph is possible, there is no way to express the notion of a minimum vertex cover minimum dominating set.\cite{easyprobs}  This is a major limitation since this minimized form is the most common form in which these questions are asked. In order to remedy this, some groups have made extensions of Courcelle's Theorem to include optimized versions of MSO-expressible problems. We will cover these improvements in the related works section.
\subsubsection{What Kinds of Graphs: Graphs of Bounded Treewidth}
\par The kinds of graphs that we can ask MSO questions about are graphs of bounded treewidth. Treewidth can be thought of as is a measure of the extent to which a graph is "tree-like". If a graph has bounded treewidth, then all of its information can be encoded in a tree in a finite fashion.
In order to formally understand treewidth, we first have to understand tree decompositions. Tree decompositions are defined as follows:\cite{seymour, kneis}
\par A tree decomposition of a graph $G=(V, E)$ is a pair $(T, X)$ where $T$ is a tree and $X$ is a a family of sets indexed by the vertices of $T$, such that
\begin{enumerate}
\item $\bigcup X_{i} = V$
\item $\forall e \in E, \exists i $ such that the vertices incident on $e$ are present together $X_{i}\footnote{Note that this is not in MSO: this is the mathematical definition for a tree decomposition, which has nothing to do with MSO on its own.}$
\item If $i, j, k$ are nodes of $T$ such that $i$ is on a path between $j$ and $k$, then $(X_{j} \cap X_{k}) \subset X_{i}. $
\end{enumerate}
\par The sets of vertices, $X_{i}$, are called bags. The width of a tree decomposition is the size of the largest bag $X_{i}$ minus one. The \textbf{treewidth} of a graph is the minimum width over all possible tree decompositions.
\par We can see that a tree decomposition of a graph is an encoding of a graph into a tree: it preserves all the information of the original graph within it. It has all of the vertices of the original graph by the first condition. It keeps track of all of the edges in the graph by the second condition. The requirement for the third condition is more nebulous without a formal proof, but intuitively, it is there to retain the general shape of the graph--a given vertex cannot be in several different unconnected bags of the tree decomposition, it is just in one connected area.  \textcolor{red}{and the third condition ensures that ???what is the third condition good for??. REALLY STILL NEED HELP HERE!!}
\par We include an example. Consider the graph below, $G$. We can see it is certianly not a tree, as it has cycles. However, we want to encode $G$ as a tree, and preserve all of its information.
\\
\\
\includegraphics{ograph_small}
\\
\includegraphics{td_small}
\\
\\
\par Here is a tree decomposition of $G$.
\par In this diagram, the large ovals containing letters in them depict the nodes of the tree, and the letters depict the elements in the bag at that node. A quick inspection can convince the reader that the three conditions of a tree decomposition hold on this structure:  all vertices of the original graph are present in the union of the bags of the tree decomposition. For every edge $(i,j)$ of the original graph, we can find at least one bag of this tree decomposition containing both $i$ and $j$. The root contains edges $(b,g)$ and $(d,g)$, the children of the root contain $(a,b)$ and $(a,d)$, and $(d,g)$ over again, and the three children of the second child contain the data for the rest of the edges. Finally, for all $i, j, k$,  nodes of T such that $i$ is on a path between $j$ and $k$, we see that $(X_{j} \cap X_{k}) \subseteq X_{i}.$ For example, consider the path between the nodes corresponding to bags $\{ b,d\}$ and $\{ c,d,f\}$. The interesction of these two bags is $d$. Note that every node on the path between these two nodes has $d$ as an element of their bag. This property holds throughout the tree decomposition pictured.
\par This tree decomposition is not necessarily optimal, and it is definitely not unique. For example, the nodes at the bottom with singleton bags $\{ a \}$ and $\{ b\}$ are not necessary: all of the node and edge information is already encoded in the tree decomposition without them. So, an alternate tree decomposition of the same graph would not include these nodes. The tree decomposition pictured has width two, since the size of the largest bag is three.  It may have occurred to the reader that every finite graph $G$ has finite treewidth. To see this, note that one possible tree decomposition of a finite graph $G$ is a tree of one node, with a bag $X_{i}$ containing all vertices of $G$ within it. This satisfies all requirements: $X_{i}$ contains all vertices and edges, and the connectivity is held because there is only one node. This means that the treewidth of any graph cannot be greater than the number of verticies, or elements of the set, $\lvert G \rvert$. However, as we will soon see, using this tree decomposition would render Courcelle's Theorem useless.
\par Finding the treewidth of a graph is a technically an NP-hard problem, and the version of Courcelle's Theorem that this work verifies assumes that a tree-decomposition of the graph in question is given as a part of the input. Boldaender proved that finding the optimal tree decomposition of an input graph is strongly fixed-parameter tractable linear, i.e. linear in the sense that Courcelle's theorem gives a linear algorithm, which we will explain below \cite{lintd}. However, the algorithm originally presented by Bodleander is known to be incredibly impractical; for one thing, the constants in the algorithm are prohibitive to implementation, and also the algorithm, in turn, relies upon having a non-optimal tree decomposition to start with. Thankfully, there are several good heuristics for computing treewidth, which are covered nicely in Chapter 13 in Downey and Fellows' 2013 book Fundamentals of Parametrized Complexity \cite{fellows13} as well as several survey papers by Bodleander\cite{bodtw}. These heuristic algorithms may be the most efficient method for finding a tree decomposition as an input to the algorithm, since there is really no need that tree decomposition be entirely optimal. The width being slightly larger  will just increase the time the algorithm takes. However, the algorithm verified in this paper pays no attention to this part of the process, though other proofs of the theorem have taken a different approach. We only mention this problem here to discuss the feasibility of actually using the algorithm as a way to decide MSO-expressible hard problems on graphs of bounded treewidth quickly.
\subsubsection{What Kind of Linear: Fixed Parameter Tractable Linear}
\par Finally, we come to the condition on linear-ness:  the algorithm we get for deciding an MSO question on a graph of bounded treewidth is fixed-parameter tractable linear, or FPT linear. FPT linear means linear in the size of the input, with a "constant" that is a function of a fixed parameter, or several fixed parameters. In this case, we have an algorithm that is linear in the size of the input graph $G$, and our parameters are the encoding of the monadic second order logic sentence $\phi$ and the treewidth $t$ of $G$. So, the algorithm described by Courcelle's theorem takes time
\[ f(t, (\lvert \phi \rvert)) \cdot (\lvert G \rvert)
\]
for some function $f$.  Unfortunately, in the case of Courcelle's Theorem, this function $f$ is very large.  In fact, unless P=NP, the function cannot be upper bounded by an iterated exponential of height bounded by $\phi$ and $t$.\cite{kneis, cour, gro}
\par Bringing these definitions together, we can now understand the formal statement of Courcelle's Theorem\cite{kneis, cour, gro}:
\par Let P be an MSO problem and $\omega$ be a positive integer. There is an algorithm $A$ and a function $f : \textbf{N} \times \textbf{N}  \rightarrow \textbf{N}$ such that for every graph $G = (V, E)$ of order $n:= \lvert V \rvert$ and treewidth at most $\omega, A$ solves $P$ on input $G$ in time $f(||\phi||, \omega)  \cdot n,$ where $\phi$ is the MSO formula defining $P$ and $||\phi||$ is its length. Furthermore, unless $P=NP$, the function $f$ cannot be upper bounded by an iterated exponential of bounded height in terms of $\phi$ and $\omega$.
\par Upon reading about this ghastly constant, it may seem that the possibility of practical usage of Courcelle's Theorem is quite small. However, not all hope is lost. There is work being done on making Courcelle's theorem usable, as will be discussed in the related work section.

\subsection{Verification and Agda} The reader might wonder why we go so far into detail on a theorem that has already been proven. As mentioned earlier, this thesis is a progress towards a formal verification of Courcelle's Theorem. We perform the verification with a proof assistant, Agda\cite{agda}. Verification via proof assistants is a method of ensuring that either a mathematical proof or a program is correct, in a way that removes much of the possibility for human error. Verification is currently used in a few main situations. The first is  when there is a mathematical proof that is either too long for a human to reliably complete or a completed proof that is not well accepted by the community, for example the Jordan Curve theorem, or the Four Color theorem, which have both been verified by proof assistants [cite{jordan, color}]. Another area of use is for programs run in high-stakes situations, such as medical software, software used by NASA, or that used to create Intel hardware [cite{nasa, intel}]. Finally, proof assistants are also often used simply to record mathematical proofs in a standard fashion. The motivation behind this project is straddled between these latter two goals. Courcelle's Theorem is a large, important mathematical accomplishment, and we hope to add it to the list of verified proofs. However, although the algorithm in Courcelle's Theorem does not have any high-stake implementations that the authors are aware of, the theorem seems to have potential of becoming useful in the field of relational databases. If a relational database is created someday that relies upon Courcelle's Theorem to run its queries, a formal verification of the theorem may be useful in situations where queries are being run on sensitive data where far-reaching conclusions may be drawn from the queries on that data (medical data, census data, etc).
\par It should be mentioned that verifying with a proof assistant is very different from verifying with an automated theorem prover. Automated theorem provers minimize the level of human interaction with the program, but they have much less expressive power than proof assistants--usually limited to that of first order logic [cite{historyulf}]. Of course, since proof assistant code is still written by humans, there is still a possibility for error, but this space where this error can occur is minimized. The only place where a formal verification by a proof assistant can go wrong is in the definitions put forth in the program: these definitions may not exactly correspond to what the user is actually trying to verify. In other words, the only way a formal verificaion can go wrong is that the user is unwittingly proving the wrong thing, since they defined their goal incorrectly.[cite{historyulf}]
\par However, this means that as long as we agree with the definitions in a formal verification done with a proof assistant, we can trust that whatever logical implication is drawn from these definitions is proven absolutely correctly through the rules of type theory.\cite{historyulf}
\par Due to this fact, a large portion of this work will be dedicated to explaining the definitions we have created, and convincing the reader that they correspond to the mathematical definition as sufficiently so that our proof may be trusted.
\par The tool that we use to verify Courcelle's Theorem, as we mentioned above, is called Agda\cite{agda}. Agda is a dependently typed functional programming language based on Haskell. It was created by Ulf Norell in his PhD thesis at Gotenburg University\cite{agda}. In order for Agda's underlying logic to remain constistent, Agda also enforced termination checking, i.e. all possible patterns in a program must be matched, and all recursion must be performed on smaller subproblems. Agda's method of termination checking is based on the Foetus termination checker [cite{agda, foetus}].
\par Agda has the some of the usual trappings of regular programming languages, for example, data types, pattern matching, let expressions, and modules. Its syntax is similar to that of Haskell. One quite beautiful feature of Agda, is its use of metavariables in the code. A user can define a function and leave the proof as a metavariable, often referred to as the goal. Agda will display the expected type of the metavariable, an the user can incrementally refine it, by putting pieces of code in bit by bit, and having the expected types of the missing pieces updated by Agda.
\subsection{Contributions and Future Work}
\par The goal of this project is to complete a formal verification of Courcelle's Theorem in Agda, along with a verification of its use in A Simple Algorithm for the Graph Minor Decomposition by Grohe et. al.\cite{reed} At this stage, we have completed our translation of the definitions given in Courcelle's Theorem: A Game Theoretic Approach\cite{kneis} into Agda. We have defined the types of the functions corresponding to the lemmas in the paper that prove Courcelle's Theorem, however we have yet to implement them. We also have yet to prove the fact that the algorithm is fixed-parameter tractable linear; this is next on our agenda after completing the proof of the algorithm itself. After this work is complete, we hope to extend our verification of Courcelle's Theorem to some of its applications. One probable direction we will pursue is verifying the algorithm in the paper above by Grohe et. al. We are also considering applications to phylogenetics and database theory, upon greater research into the applications of Courcelle's Theorem.
\subsection{Road Map}
\par The rest of the paper will proceed in the following manner:
\par Section Two, Helpful Background and History, will expand a little bit on the three disciplines that this theorem draws upon. The first is graph minor theory, which is the origin of tree decompositions. The second is (monadic second order) logic, and some extensions of Courcelle's Theorem to which apply to questions formulated in slightly more expressive logics. We also touch on logic's connections to graphs via graph rewriting,  which is how Courcelle's Theorem takes in its input graphs. Finally, we will touch on parametrized complexity, which is where we get the notion of fixed-parameter tractable linear from. After briefly engaging with these topics, we will allude to some common methods of proving Courcelle's Theorem, and note their strengths and weakenesses.
\par Following this, in Section Three, we give an outline of the proof of Courcelle's Theorem in Courcelle's Theorem: A Game Theoretic Approach by Kneis et. al.\cite{kneis}, which is the proof method we base our verification off of.
\par In Section Four, Related Work and Applications, we touch on other verification work in this space and some applications of Courcelle's Theorem in graph theoretic algorithms, phylogenetics, and database theory  before heading into the main part of the paper.
\par Section Five, Definitions, contains the bulk of the work of this thesis. Here, we go through the concepts defined in the Kneis et. al. paper\cite{kneis}, present our translations of each concept in Agda, and show how the two are equivalent. This is in an effort to convince the reader that, once we do finish the complete proof, it will be correct since our definitons are correct. Specifically, we define symbols, signatures,  structures, and expansions of structures (3.1);  restrictions of structures (3.2); tree decompositions (3.3); MSO formulas (3.4), isomorphismis of structures (3.5); compatibility (3.6); structure union (3.7); games, model checking games, and extended model checking games (3.8); and finally, position equivalence,  game equivalence, and reduced games (3.9).
\par Our last section before the conlusion is Section Six, Outline of Algorithm and Work in Progress. Here, we give a mathematical proof of Courcelle's Theorem based on the lemmas outlined by Kneis et. al. \cite{kneis}. We intertwine this with our progress on the proof in Agda, i.e. along with the types of the functions in Agda with which we will prove the theorem.
\par Off we go! \textcolor{red}{put anything here as a transition?}
\section{Helpful Background and History}
\par The concept of treewidth was created by Halin \cite{sfunc} under the name S-function, but it only became prominent through the work of Robertson and Seymour leading up to their famous Graph Minor Theorem.\cite{recentprog} A minor of a graph $G$ is any graph $G'$ that can be produced by a series of the following three operations: deleting an edge, contracting an edge, and deleting an isolated node \cite{graphminor}. Robertson and Seymour set out on what ended up being a twenty-five year (and twenty-three-paper) long journey to prove something called Wagner's Conjecture, which became the Graph Minor Theorem. Wagner's Conjecture is based off of Kuratowski's Theorem in graph theory, which will help set up the intuition for the theorem. Kuratowski's Theorem states that a graph $G$ is embeddable in the plane if and only if it does not contain a subgraph homeomorphic to the complete graph $K_{5}$ or the complete bipartite graph $K_{3,3}$ \cite{kuratowski}. Wagner's Conjecture asks for a much more general principle: that if a class of graphs $K$ is minor-closed (i.e. $\forall G \in K, G'$ is a minor of $G,$ then $G' \in K$), then $K$ can be characterized by a finite number of excluded minors. Robertson and Seymour re-discovered treewidth in this context, as a purely mathematical tool to prove Wagner's Conjecture. Graph Minor Theory by Laszlo Lovasz is a well-written, concise introduction to graph minor theory and Robertson and Seymour's results from a purely mathematical perspective.\cite{graphminors} Graph minors have their own applications to computer science via coloring problems and combinatorial optimization [\cite{recentprog} pp 25, 31], but computer scientists soon picked up on the notion of treewidth much more widely as a way of putting a contraint on graphs in order to find faster algorithms that take advantage of this constraint.[cite??] Some Recent Progress and Applications in Graph Minor Theory is a more extended resource to learn about the landscape of graph minor theory beyond just Robertson and Seymour's work \cite{recentprog}. \textcolor{red}{need more stuff about treewidth applications more generally?}
\par Graph Rewriting: An Algebraic and Logical Approach by Courcelle \cite{graphrewrite} provides a background to expressing graphs as logical structures, which is how Courcelle's Theorem interprets graphs. It explains which graph properties are definable in first order logic (for example, having degree k is first order logic expressible, but not connectedness), monadic second order logic (e.g. connectedness, but not having the same number of edges in label sets A and B) and second order logic (e.g. that a graph is finite)\cite{graphrewrite}.
\par Recall our conversation from the introduction about MSO, where we brought attention to the fact that while MSO formulas can express the notion of k-colorability or vertex set, but because one cannot count in MSO, one cannot express the minimum vertex set or the minimum coloring. Successful efforts have been made to overcome this restriction. For example, Seese et. al. introduced Extended MSO, or EMS, which allows for optimizations of MSO-definable problems, as well as problems over graphs with weight functions, and several new problems besides. A more complete description of which problems are MSO and EMS definable are in \cite{easyprobs}.
\par Kneis et. al. develop their own extension, called LinMSO, that works specifically for linear optimizations of MSO definable problems \cite{kneis}. Both Seese et. al. and Kneis et. al. have proven that their extensions of MSO satisfy Courcelle's Theorem, i.e. that problems in EMS and LinMSO can be solved in FPT-linear time on graphs of bounded treewidth. \cite{kneis, easyprobs}. The formulation of Courcelle's Theorem with Extended MSO is very widely used, but in this paper we only verify the original version.
\par  Parametrized complexity, the field that gives us the notion of fixed parameter tractable algorithms, was developed by Robert Downey and Michael Fellows in the 1990s \cite{fellows13}. The main idea in paramtertized complexity is thinking of complexity in multiple dimensions rather than just one. Downey and Fellows explain their idea as a "deal with the devil" to compensate for the inevitable combinatorial explosion in most interesting algorithms: they limit the explosion to one attribute, which becomes the parameter, of the input\cite{fellows97}. In our case, the inevitable exponential blowup is checking every element of an underlying set of a structure at each universal or existential quantifier in the input formula. This blowup becomes confined to the treewidth of the graph and the encoding of the MSO sentence.
\par In Downey and Fellows' parametrized complexity book, they demonstrate one of many ways to prove Courcelle's Theorem, using the Myhill-Nerode theorem and the method of test sets [\cite{fellows97}, Chapter 6]. However, this method has never been implemented. There are several different ways to prove, and implement, the Theorem. The most common way to prove the theorem is through the automata-theoretic approach: a tree automaton $\mathds{A}_{\tau}$ is contructed in time that is exponential only in the treewidth $t$ and the size of the formula $\phi$. $\mathds{A}_{\tau}$ accepts a tree decomposition of width t if and only if the corresponding graph satisfies $\phi$.\cite{gro, fellows13}
\par The problem with this approach is that at every universal and existential quantifier, the automata expands exponentially. Since automata are so well understood, there are tools to miminize these generated automata, such as the MONA tool \cite{monamanual2001}. However, one particularly frustrating thing about the automata-theoretic method is that often, most of the states created are never used. Sometimes, even though the minimized automata are small, the initial computations are so expensive that even the MONA tool fails to run the algorithm--this can occur on graphs as small as $2\times n$ grids \cite{kneis}. There are a few different ways to circumvent this issue; they all involve some version of creating what you need as you go. Courcelle and Durand use functions instead of tables to model automata in an effort to make the algorithm faster and dub the method using fly-automata \cite{flyaut}. The name is due to the fact that the  state-transition functions are created "on-the-fly". Alternatively, this can be done by scrapping the idea of automata all together. Ganzow and Kaiser bypass the use of automata at all and directly manipulates the input formulas \cite{newalgo}. This is also the approach that Kneis et. al. take in their proof of Courcelle's Theorem, which is the version of the proof this work aims to verify.
\section{Outline of Kneis et. al. Algorithm}
\par Kneis, Langer, and Rossmanith do away with automata all together in their paper Courcelle's Theorem--A Game Theoretic Approach\cite{kneis},  which is the algorithm we use to verify Courcelle’s Theorem in our work. Kneis et. al. come up with a new strategy to tackle Courcelle’s Theorem, borrowing tools from game theory, namely, model checking games. The algorithm they outline to decide the formula on the structure is a dynamic programming algorithm on the tree decomposition\cite{kneis}. As mentioned above, the problem with the automata theoretic approach is that many of the states created are never actually used to decide the formula on the input graph, so prohibitively large amounts of time and space are spent creating things that will never actually be used. Kneis et. al. suggest this is because this proof and implementation method does not pay attention to the attributes of the specific graph and MSO formula given. Instead, the automata theoretic implementation does a very similar thing no matter what the input is.\cite{kneis} To fix this problem, Kneis et. al. take the details of the input into account, and in light of the input, systematically trim down the information stored to be only what is necessary.\cite{kneis} As alluded to earlier, there is evidence that this implementation runs in a reasonable amount of time (from a few seconds to under 24 hours) for graphs up to treewidth 12 for minimum vertex cover, dominating set, and 3-colorability.\cite{kneis} An explanation of the algorithm is in the last section of this paper, however, we give a quick intuitive idea. At each node $i$ of the tree decomposition, there is a bag $X_{i}$ of vertices of the original graph. Additionally, we can associate with each node a set $A_{i}$, which is the union of all bags on the tree starting at the leaves and up until, and including, the bag $X_{i}$. The paper shows that if an MSO sentence $\phi$ is shown to hold over a restriction of the graph $G$ to the set  $A_{i}$, called $G[A_{i}]$--a notion that we will formalize later but essentially means that $G[A_{i}]$ is the graph $G$ with all the elements that are not in $A_{i}$ thrown out of it--then $\phi$ is true over the whole graph. And similarly if the $\phi$ can be shown to not hold over $G[A_{i}]$, then it does not hold over the whole graph. (The way in which the formula is “shown to hold” is via a model checking game, which again, we will explain in the pages to come.) The algorithm traverses the tree decomposition bottom up, evaluating whether or not $\phi$ holds for each $G[A_{i}]$ via a game: if the formula holds, the algorithm exits and returns that the formula holds, similarly if the formula is shown to be false on the graph. Alternatively, if the data is insufficient, then there is a special combining algorithm that combines the game on $G[A_{i}]$ with the game on $G[X_{h}]$, where $h$ is the next node above $j$. Note that the combining algorithm takes the recursive call and only the $bag$ at the next node, not the entire set of all the bags below it. Because of this, the algorithm never checks the formula over the entire graph, only over the subsets of the graph in the bags $X_{i}$ of the tree decomposition. Note that by definition of treewidth, the size $X_{i}$ will always be less than the graph's treewidth $t$. So, even though there can be exponential blow up to check if $\phi$ holds on  $G[X_{i}]$, the time is only porportional to $\lvert X_{i} \rvert$, which is a constant. The computation at each node, then, is constant. Thus, the algorithm is linear in the size of the input graph. The algorithm checks the formula ocer the restrtiction at each tree decomposition node, where the number of nodes in the tree decompistion is linearly related to how many nodes are in the graph, and the computation at each node is constant time. Unfortunately, as mentioned, the algorithm on these restrictions is exponential in the size of the bags, which is where the nasty exponential constant in the size of the parameters partially comes from. However, the algorithm in Kneis et. al. addresses this problem as well. They introduce a notion of isomorphism between games, so that the algorithm keeps track of as few games as possible, which cuts down on the exponential constant. The details of these ideas will be explained in the pages to come.
\section{Related Work and Applications}
\par As far as the authors are aware, there are no other attempts to formally verify Courcelle's Theorem. There have been papers verifying  processes related to Courcelle's theorem. For example, Martin Streker verfied some systems of graph rewriting, which is central to Courcelle's Theorem.\cite{martin} But there is no literature we can find on tackling Courcelle's Theorem specifically.
\par Some application areas of Courcelle's Theorem include graph theoretic algorithms: for example, a paper on constructing graph minor decompositions by Reed et. al. uses Courcelle's Theorem in the proof \cite{reed}. Another application area is  phylogenetics, where scientists need to answer questions about graphs called agreement forests, which depict how close two different proposed phylogenetic histories are. The questions they need to ask are expressible in MSO, and in practice, one researcher Stephen Kelk points out that agreement forests often have low treewidth. A good, fast implementation of Courcelle's Theorem, then,  would likely speed up the research of phylogeneticists \cite{phylo}. Another potentially exciting area of application is to database theory, which deals mostly with first order logic questions asked about relational databases, which are of course covered by MSO. Courcelle's Theorem immediately extends to relational databases with bounded treewidth \cite{databases}. So, Courcelle's Theorem promises a faster implementation for SQL queries, which, if brought to fruition, could potentially cause a huge increase in querying speed.
\section{Definitions}
\subsection{Structures}
\par The version of Courcelle's Theorem that is verified in this paper generalizes beyond graphs as the input object to the algorithm. We show that any MSO sentence can be decided on a \textbf{structure} of bounded treewidth in FPT-linear time. In order to define structures, we have to introduce some other concepts first.
\par A \textbf{symbol}  $S$ is an object with an arity, $arity(S)\geq 0$. If a symbol has arity 0, then it is a $constant$, if it has arity greater than 0, it is a $relation$.
\par A \textbf{signature} $\Sigma$ is a finite set of symbols.
\par A \textbf{structure} $\mathds{A}$ is a tuple $\mathds{A} = ( A, (R^{\mathds{A}})_{R\in rel(\Sigma)}, (c^{\mathds{A}})_{c\in constants(\Sigma)})$, where $A$ is a finite set called the universe of $\mathds{A}$, and $R^{\mathds{A}}$ and $c^{\mathds{A}}$ are interpretations of the relations and constants in $\Sigma$ using the elements of $A$. More precisely, $R^{\mathds{A}} \subset A^{arity(R)},$ and $c^{\mathds{A}}$ is either an element of $A$, or $c^{\mathds{A}}$=nil.We call the constants $c$ nullary constants because they have arity zero. Additionally, we say that $c\in interpreted(\mathds{A})$ if and only if $c^{\mathds{A}} = a\in A$, i.e.  $c^{\mathds{A}} \neq nil.$
\par It may be useful to think of the signature as a mold to pour clay into, where clay is a finite set. Or, the reader may imagine

symbols in the signature as placeholders that are waiting to be filled by elements of a set. We illustrate this with the example of graphs. A possible signature for graphs is $\Sigma_{G} = Edge(x,y)$, where edge is a binary relation that determines which vertices have an edge in between them. This signature is not a graph itself. An actual graph would be a structure $\mathds{G}$ over the graph signature $\Sigma_{\mathds{G}}$ with a set, $V$, of vertices, $\mathds{G}= (V , Edge(x,y)^{\mathds{G}})$.   $Edge(x,y)^{\mathds{G}} \subset V \times V$ is an interpretation of the $Edge(x,y)$ relation that specifies all of the vertices that have an edge between them for that specific graph. Note that there are multiple different graphs $\mathds{G}'$ that have the same underlying $V$: they have different subsets of $V \times V$ for the interpretation of the edge relation, which makes $\mathds{G}'$ have different edges than $\mathds{G}$.
\subsubsection{Expansion}
\par Necessary to understanding the code is the idea of an expansion of a structure. Suppose $\Sigma$ is a signature, and $\{ R_{1}, ... R_{l}, c_{1}, ... c_{m}\}$ is a set of symbols, each of which is not in $\Sigma$. Then we say a signature $\Sigma '$ = $\{ \Sigma, R_{1}, ... R_{l}, c_{1}, ... c_{m} \}$ is an expansion of $\Sigma$. Then, if $\mathds{A}$ is a $\Sigma$-structure, and $\mathds{A}'$ is a $\Sigma '$-structure, such that $(R^{\mathds{A}})=(R^{\mathds{A}'})$ for all relations symbols $R \in \Sigma$, and $c^{\mathds{A}}= c^{\mathds{A}'}$ for all $c \in \Sigma$, we say $\mathds{A}'$  is a $\Sigma '$-expansion of $\mathds{A}$. Suppose we have a $\Sigma$-structure $\mathds{A}$, and suppose that  $\Sigma ' = \{ \Sigma, c_{1}\}$. Also suppose we have an element $u_{1} \in (A \cup {nil})$. Then we can write the $\Sigma ' $-structure $\mathds{A}'$ as $\mathds{A}' = (\mathds{A}, u_{1})$, to show that $\mathds{A}'$ is a $\Sigma ' $-expansion of $\mathds{A}$, and that $u_{1}$ is the  interpretation for the new symbol $c_{1}$. Similarly, if $\Sigma ' = \{ \Sigma, R_{1}\}$ for some relation symbol $R_{1}$, and we have a set $U_{1} \subset A^{arity(R)}$, then we could write a $\Sigma '$-expansion of $\mathds{A}$ as $\mathds{A}' = (\mathds{A}, U_{1})$. We will see this in the Agda code.
\par We designed our algorithm to respect the idea of structures as inputs, but in this particular implementation, we tailored it to expect graphs as input. As mentioned earlier, in the non-extended form of MSO we are using in this work, one cannot decide formulas on graphs that quantify over edges. In order to remedy this, we instead think of a graph as a set with two different types of elements: nodes and edges. This way, we can quantify over edges, since they are simply constants in the signature rather than a binary relation. However, including edges as elements of the underlying set of a structure $\mathds{G}$ instead of as a binary relation has the implication that edges and nodes are indistinguishable to the algorithm, which can pose problems. For example, suppose we want to have a graph $\mathds{G}_{red}$ that has a special set of of red nodes. Then there would be a unary relation in this graph's signature, $Red(x)$, and an interpretation in the structure, $Red(x)^{\mathds{G}_{red}} \subset G_{red}$, that specified which elements of the underlying set $G_{red}$ were the red vertices. However, the problem here is that some of these set elements of $Red(x)^{\mathds{G}_{red}}$, the "red vertices", might actually be edges, since vertices and edges in the underlying set are indistinguishable to the relation. So how do we make sure that only vertices are allowed in this set?
\par We fix this problem in the code by introducing the data type |Tp|, which has an edge constructor and a node constructor. We then require in our datatype for symbols, Sigthing, that constants (constructor $i$) specify which kind of set elements they want, nodes or edges, by carrying a Tp with them. Relations (constructor $r$) specify whether they want a node or edge for each argument, by carrying a list of Tp with them. This solves the problem illustrated above because the relation $Red(x)$ would really be a one-element list (node::[]), specifying that it only allows nodes in its interpretation-set.  Another, related reason why we introduce Tp is to make sure that when we have quantifiers in a formula, we specify whether that quantifier is for edges or for nodes, in order to ensure that we have as small a search space as possible. The code for |Tp| and |SigThing|, symbols, is below.  \textcolor{red}{is this right?}
\begin{code}
  data Tp : Type where
    node : Tp
    edge : Tp

  data SigThing : Type where
    i : Tp → SigThing
    r : List Tp → SigThing
\end{code}
\par Now we come to our Agda definition of a signature: a list of |SigThings|, i.e. a list of symbols. And, a list is finite by definition, so we satisfy the requirement that the signature is a finite set of symbols. We have two functions on signatures, which allows us to extend them: the function $,i$ allows us to add another constant onto our signature, and the function $,r$ allows us to add another relation onto our signature. These functions take a signature and either a constant or a relation, and return a signature which is the original signature appended the constant.
\begin{code}
  Signature = List SigThing

   _,i_ : Signature → Tp → Signature
  Σ ,i τ = i τ :: Σ

  _,r_ : Signature → Args → Signature
\end{code}
\par Coming up with a definition for a structure was a little bit more complicated, since there are a few more moving parts. Recall the definition of structure above: A structure $\mathds{A}$ is a tuple $\mathds{A} = ( A, (R^{\mathds{A}})_{R\in rel(\Sigma)}, (c^{\mathds{A}})_{c\in constants(\Sigma)})$, where $A$ is a finite set called the universe of $\mathds{A}$, and $R^{\mathds{A}}$ and $c^{\mathds{A}}$ are interpretations of the relations and constants in $\Sigma$ using the elements of $A$. In order to represent this in Agda, we needed to define what the underlying set would be. A set is a collection of elements, so before we could define sets, we had to define what sort of elements would be making up these collections. We called the objects in our space, the elements of our sets, our clay that would fill our signatures, Individs. An Individ takes a |Tp|, i.e. data of whether it is a node or an edge, and returns a type. This type is the underlying data that our input graphs will be made up of. In our implementation, we chose this type to be a string, one could change the code to model the set elements as any kind of structure one might like.
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
\par Now that we have our objects, we can define sets of objects. Our notion of set is called a Subset (because set is a reserved word in Agda). We defined Subset as a predicate on elements (Individ) of a certain type. So, edge elements and node elements can have different stipulations that determine whether or not they are in a given set. In case the difference between Tp and Individ is confusing, think of a Tp $\tau$ as a label for a certain slot in a signature that says what $type$ of thing can go in it, and an Individ of type $\tau$ is the thing that goes in. \textcolor{red}{is there a more intuitive way of explaining "predicate on elements of certain type?"}
\begin{code}
 Subset = (τ : Tp) → Individ τ → Type
 DecidableSub : (S1 : Subset) → Type
 DecidableSub S1  = ∀ {τ} (x : Individ τ) → Dec (S1 τ x)
\end{code}
\par For now, our construction Subset does not guarantee that the set is finite as is required in the definition of a structure. We anticipate revising this once we see what we need in the rest of the proof--- we will definitely add the conditions of finiteness and decidableness to the subset, but there may be other qualities that we require that are as of yet unseen. Adding these qualifications to the subset is a trivial task, we would simply add a bit more data that we could abstract away and leave the code unchanged, so please pay this small detail no mind.
\par After defining subsets, we defined IndividS, which is simply an Individ together with the data that it's in a specified subset. This will become useful later on.
\begin{code}
 IndividS : Subset → Tp → Type
  IndividS A τ = Σ \ (x : Individ τ) → A τ x

  IndividsS : Subset → Args → Type
  IndividsS A [] = Unit
  IndividsS A (τ :: τs) = IndividsS A τs × IndividS A τ
\end{code}
\par We also defined a datatype OC, with constructors open and closed. This datatype will be part of the information structures carry with them. A struction being open corresponds to possibly it having constants intepreted as nil, and a structure being closed means that all constants in $\Sigma$ are interpreted in $\mathds{A}$.

\begin{code}
data OC : Type where
    Open : OC
    Closed : OC
\end{code}

\par Then, combining subsets, OC, and signatures, we defined something called a StructureS, which we build on to finally define a structure.
Think of the StructureS as the part of the structure tuple that consists of all the interpretations of the signature, (i.e. all the $R^{\mathds{A}}, c^{\mathds{A}})$.
A StructureS is a datatype that requires information saying whether it is open or closed (OC), a subset, and a signature.
Now would be a useful time to review the notion of expansions of structures given a slightly above this definition.
StructureS has four constructors: empty, an expansion with an element of the underlying set (IndividS),
an extension with a nil (which mandates that the StructureS be open),
and an extension with a set (corresponding to a relation tuple).
Note that the expansion constructors return a StructureS over an expanded signature,
adding a constant symbol of type $\tau$ in the $,is$ and $,none$ cases, and adding a relation symbol in the $,rs$ case.

\begin{code}
data StructureS : OC → Subset → Signature → Type where
     []      : ∀ {oc A} → StructureS oc A []
     _,is_   : ∀ {oc A Σ τ} → StructureS oc A Σ → IndividS A τ → StructureS oc A (Σ ,i τ)
     _,none  : ∀ {oc A Σ τ} → StructureS oc A Σ → StructureS Open A (Σ ,i τ)
     _,rs_   : ∀ {oc A Σ τs} → StructureS oc A Σ → (IndividsS A τs → Type) → StructureS oc A (Σ ,r τs)
\end{code}
We then create the type Structure, which requires an OC and a Signature, and consists of a product of a subset and a StuctureS
that goes with that subset, i.e. a tuple of a set, and interpretations of a given signature from that set. This  is exactly what a structure is defined to be mathematically.
\begin{code}
  Structure : OC → Signature → Type
  Structure oc Sig = Σ \ (A : Subset) → StructureS oc A Sig
\end{code}
\subsection{Restrictions}
\par Suppose we have a structure $\mathds{A} = ( A, (R^{\mathds{A}})_{R\in rel(\Sigma)}, (c^{\mathds{A}})_{c\in constants(\Sigma)})$. We can restrict this structure to a smaller subset $A_{1} \subset A$, and call this structure $\mathds{A}[A_{1}]$. In this new structure, we insist that we  only have the set elements in $A_{1}$, and so we only have the constant and relation interpretations that are contained entirely inside $A_{1}$. Formally, given a structure $\mathds{A}$ and a set $A_{1} \subset A$, the restriction of $\mathds{A}$ to $A_{1}$, $\mathds{A}[A_{1}]$, is a structure with universe $A_{1}$,  $(R^{\mathds{A}[A_{1}]})= R^{\mathds{A}} \cap A_{1}^{arity(R)}$, and $c^{\mathds{A}[A_{1}]} = c^{\mathds{A}}$ if $c^{\mathds{A}} \in A_{1},$ and become interpreted as nil otherwise.
\par In Agda, we encode this notion by a helper function restrictionS on StructureS's, and from that we build restriction on Structures. restrictionS requires a structure $\mathds{A}_{1}$, a subset $S1$, a proof that $S1$ is decidable, and a proof that $S1 \subset A$, and it returns the interpretations of $\mathds{A}$ restrictied to the set $S1$. Note that in our helper function restrictionS, we ask for a proof that the subset we restrict to is decidable; when we fix our notion of subset this will no longer be necessary. The code is relatively straightforward and there is no need to go through it in detail; essentially this code runs through each IndividS that interprets a constant in the signature in the |StructureS A1'|, and if it is not in the restriction subset $S1$, it replaces this interpretation with a nil. And it only includes relation tuples that are entirely within $S1$. HELP HERE!!
\begin{code}
 restrictionS : ∀ {Σ} {oc1} {A1} (A1' : StructureS oc1 A1  Σ) (S1 : Subset)
                      → DecidableSub S1 → Sub S1 (A1) →  StructureS Open S1 Σ
 restrictionS [] S1 dec sb = []
 restrictionS (A1' ,is x) S1 dec sb with dec (fst x)
 ... | Inl inS = restrictionS A1' S1 dec sb ,is (fst x , inS)
 ... | Inr out = restrictionS A1' S1 dec sb ,none
 restrictionS (A1' ,none) S1 dec sb = restrictionS A1' S1 dec sb ,none
 restrictionS (A1' ,rs U) S1 dec sb = restrictionS A1' S1 dec sb ,rs (λ v → U (promoteIndividsS sb v))
\end{code}
\par The code for restriction simply attaches the appropriate underlying subset, S1, to the restricted interpretations given by restrictionS. restriction takes essentially the same inputs as restrictionS, except that it requires and returns a structure and not a structureS.
\begin{code}
  restriction : ∀ {Σ} {oc1} (A1 : Structure oc1  Σ) (S1 : Subset)
                → DecidableSub S1 → Sub S1 (fst A1) →  Structure Open Σ
  restriction (A1' , struc) S1 dec sb = S1 , restrictionS struc S1 dec sb
\end{code}
\subsection{Tree Decompositions}
\par Recall our definition of tree decompositions above. The formal definition that we based our code off of is more general than the definition given above, because the game-theoretic algorithm works over all structures and not simply over graphs. \textcolor{red}{RELATIONAL STRUCTURES??} The definition for a tree decomposition of an arbitrary structure is as follows:
\par A tree decomposition of a structure $\mathds{A}$ over signature $\Sigma$ is a tuple $(\textbf{T}, X)$, where $\textbf{T}=(T,F)$ is a rooted tree and $X=(X_{i})_{i \in T} $ is a collection of subsets $X_{i} \subset A$, (where A is the underlying subset of $\mathds{A}$) such that
\begin{enumerate}
\item $\bigcup X_{i} = A $
\item $\forall$  $p$-ary relation symbols $R \in \Sigma,$ and all $(a_{1}, a{2}, ....a_{p}) \in R^{\mathds{A}}$, $\exists i \in T$ such that $(a_{1}, a_{2}, ....a_{p})  \subset X_{i}$, and
\item If $i, j, k$ are nodes of T such that $i$ is on a path between $j$ and $k$ in $\textbf{T}$, then $(X_{j} \cap X_{k}) \subset X_{i}. $
\end{enumerate}
\par Furthermore, in the algorithm that the game theoretic paper outlines, they use only a type of tree decompositions called nice tree decompositions. Nice tree decompositions are directed, and every edge is directed away from the root. Nice tree decompositions have exactly four types of nodes: leaves, forget nodes, introduce nodes, and join nodes.
\begin{itemize}
\item A leaf $i$ in nice tree decomposition has an empty bag, i.e. $X_{i}=\emptyset$.
\item A forget node is a node $i$ that has exactly one child, $j$, and there exists some $a \in A$ $X_{i}=X_{j}/{a}$.
\item An introduce node is a node $i$ that has exactly one child, $j$, and there exists some $a \in A, a \notin X_{j}$ such that $X_{i}=X_{j}\cup {a}$.
\item A join node is a node $i$ with exactly two children, $j$ and $k$, where $X_{i}=X_{j}=X_{k}$. We say that node $i$ is below node $j$ if there is a path from $i$ to $j$ in $T$.
\end{itemize}
Recall our diagrams of a graph and its tree decomposition from the introduction. We add here a depiction of a nice tree decomposition on that same graph. We can turn a tree decomposition into a nice tree decomposition in linear time, so reqiuring a nice tree decomposition does not add a significant amount of time to the algorithm.
\includegraphics{nice_td_small}
\par Finally, keep this idea in mind: for every node $i$ of a nice tree decomposition of a $\Sigma$-structure $\mathds{A}$, let $A_{i} = \bigcup_{(j \text{ at or \\ below } i)} X_{j}$. See that $A_{i} \subset A$. Then for every node $i$, we can associate with $i$ a substructure $\mathds{A}[A_{i}]$, i.e. a restriction of $\mathds{A}$ to $A_{i}$.
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
\par The empty constructor is the leaf node, it has an empty set for its bag and an empty set for the elements below. This corresponds to the definitoin of a nice tree decomposition given above: the leaves are required to have no nodes below them, necessitating that $B = \bigcup_{\text{j at or below i}}X_{j}=\emptyset$, and and also to have empty bags, necessitating that $X_{i}=\emptyset$.
\par The delete constructor, i.e. the forget node, takes a tree decomposition of a bag $X_{i} \cup x$ and a set B of elements below, and returns a tree decomposition with just the bag $X_{i}$ and the same set B of elements below. \textcolor{red}{is this the right way to explain it?}
\par The Intro constructor, for the introduce node, requires a few additional pieces of information. Firstly, it needs a proof (xnew) that the element ($x$) being introduced is indeed new; i.e. it is an element of the complement of $B$, the set of objects below the Intro node in the tree decomposition. Secondly, it needs a proof showing that for all relations $R$ that have tuples made up exclusively of x and and elements of $B$, that all of the elements in these tuples are in fact contained in $X \cup {x}$. This is in order to satisfy the second and  third conditions of the definition of tree decompositions. To illustrate this, consider some introduce node $i$. Suppose the second proof were false, i.e. there exists some tuple $p$ consisting exclusively elements of $B$ and $x$ such that $p \notin X_{i}$. Recall that the second condition of a tree decomposition requires that every tuple of every relation be in some bag $X_{j}$. We know by the first required proof that $x$ is not in B, so any relation containing $x$, including $p$, must be either in $X_{i}$ or some $X_{j}$ above $X_{i}$. So since $p\notin X_{i}$, $p$ must be in some some $X_{j}$ above $X_{i}$. Suppose one of the elements $b \in B$, $b \in p$ is in some bag $X_{h}$, with $h$ below $i$ in $T$. Suppose $b \notin X_{i}$. Then $b$ must be in $X_{j}$, since $b \in p$. Then, by condition three of tree decompositions, since there is a path between $X_{h}$ and $X_{j}$ through $X_{i}$,  $(X_{h} \cap X_{j}) \subset X_{i}. $  This means that $b \in X_{i}$. But this is a contradiction, so it must in fact every tuple consisting entirely of elements of $B$ and $x$ must be contained in $X_{i}$.
\par Finally, we come to the Join constructor. First, note that for the join constructor, the bags $X_{i}=X_{j}$ for the nodes $i , j$ being joined, but the $B_{i}, B_{j}$, the sets of all elements in all bags below $i$ and $j$ respectively, may not necessarily be the same. In fact, they likely are not. The Join constructor in Agda requires two proofs, (written as three since we did not make equality for sets): that $X=B_{i} \cap B_{j}$, and that for all relation-tuples in $B_{i} \cup B_{j}$, either the entire relation tuple is in $B_{i}$ or it is in $B_{j}$. In other words, there is no relation tuple in $B_{i} \cup B_{j}$ that contains elements from both $B_{i}\setminus B_{j}$ and $B_{j}\setminus B_{i}$.
The first proof is required to maintain condition three of tree decompositions. Suppose there is some join node $i$, which joins nodes $j$ and $k$ where $\exists x \in X_{i}$ such that $x \notin B_{j} \cap B_{k}$. However, note that by construction, $X_{i}=X_{j}=X_{k}$, so $x \in X_{j} \subset B_{j}$, and $x \in X_{k} \subset B_{k}$, so $ x \in B_{j} \cap B_{k}$, and we have reached a contradiction. So $X_{i}=X_{j}=X_{k} \subset B_{j} \cap B_{k}$.
Suppose $\exists b \in B_{j} \cap B_{k}$ such that  $b \notin X_{i}$. Now, since $b \in B_{j}$, there is some node $m$ at or below $j$ such that $b$ is in $X_{m}$. And, since $b \in B_{k}$, there is some node $l$ at or below $k$ such that $b$ is in $X_{l}$. Since node $i$ joins nodes $j$ and $k$, there is a path between $m$ and $l$ through node $i$. Therefore, by condition three, $X{m} \cap X_{l} \subset X_{i}$. So $b$ must be in $X_{i}$. However, we assumed the opposite, so we have reached a contradiction. Therefore  $B_{j} \cap B_{k} \subset X_{i}$.
Putting these two proofs together, we see it must be that $B_{j} \cap B_{k} = X_{i}$.
\par The second proof is necessary to preserve the second and third condition of tree decompositions. Suppose that there exists some relation tuple $r \in R^{\mathds{A}} $ such that $r \in B_{j} \cup B_{k}$, and $r \notin B_{j}$ and $r \notin B_{k}$. That is, there exists some $b_{j} \in r$ such that  $ b_{j} \in B_{j} \setminus B_{k}$ and some $b_{k} \in r$ such that $b_{k} \in B_{k} \setminus B_{j}$. Then by condition two of tree decompositions, there must be some node $m$ in the tree decomposition such that $r \in X_{m}$. However, since r contains elements not in $B_{j}$ and elements not in $B_{k}$, node $m$ must be above both $j$ and $k$. And since $r \notin B_{j} \cap B_{k} = X_{i}$, $ r \notin X_{i}$ as well. So $m$ must be above $i$. However, there is some node $a$ below node $j$ such that $b_{j} \in bag X_{a}$. And, there is be a path between node $a$ and node $m$, and it must go through node $i$, since $i$ is the only connections between $B_{j}$ and $B_{k}$ . Therefore, $b_{j} \in X_{a} \cap X_{m} \subset X_{i}$. A symmetric argument can be used to show that $b_{k} \in X_{i}$. Therefore, $b_{j}, b_{k} \in X_{i} = B_{j} \cap B_{k}$. However, we assumed this was not the case; therefore we have reached a contradiction, and so it must be that for all relation-tuples in $B_{i} \cup B_{j}$, either the entire relation tuple is in $B_{i}$ or it is in $B_{j}$.
\par Now we run through a proof of that fact that for all nodes $i$, $B= \bigcup_{n=i \text{or n below} i} X_{n}$. We do this by showing that this property holds at each constructor.
\par We prove by induction. For the base case, we have that if node $i$ is an Empty, then it has $\bigcup_{n=i \text{or n below} i} X_{n} = \emptyset$ since the bag at a leaf is empty by definition, and there are also no nodes below a leaf. Then since $B=\emptyset$ as well, we have $\bigcup_{n=i \text{or n below} i} X_{n} = B$, as desired.
\par Now we run through our inductive steps, one for each constructor. Consider a node $i$. Firstly, suppose $i$ is a delete node. By definition, we know that the node directly below $i$, call it $i-1$, had $X_{i-1} = X_{i} \cup x$ for some $x$. And, we know that $B_{i-1}=B_{i}$. By our inductive hypothesis, we have that $B_{i-1}= \bigcup_{n=i-1 \text{or n below} i-1} X_{n}$. Note that $\bigcup_{n=i \text{or n below} i} X_{n} = (\bigcup_{n=i-1 \text{or n below} i-1} X_{n}) \cup X_{i} $. But since $X_{i-1} = X_{i} \cup x$, then $X_{i} \subset X_{i-1}$, $X_{i}$ brings in nothing new. So $\bigcup_{n=i \text{or n below} i} X_{n} = \bigcup_{n=i-1 \text{or n below} i-1} = B{i}$, as desired.
\par Suppose $i$ is an introduce node. Then by definition, $X_{i}= X_{i-1} \cup {x}$ for some $x \notin B_{i-1}$, and $B{i}= B_{i-1} \cup {x}$. By induction, we have that $B_{i-1} = \bigcup_{n=i-1 \text{or n below } i-1} X_{n}$. Note that $\bigcup_{n=i \text{or n below } i} X_{n}= \bigcup_{n=i-1 \text{or n below } i-1} X_{n} \cup X_{i}$. But note that this is simply $B_{i-1} \cup {x}= B{i}$, as desired.
\par Suppose $i$ is a Join node; suppose it joins nodes $j$ and $k$. By definition, we have $B{i}=B{j} \cup B{k}$, and we have $X=B{j} \cap B{k}$. By the inductive hypothesis, we have that $B{j}= \bigcup_{n=j \text{or n below } j} X_{n}$, and $B{k}= \bigcup_{n=k \text{or n below } k} X_{n}$. Note that $\bigcup_{n=i \text{or n below } i} X_{n} = B_{j} \cup B_{k} \cup X_{i}$. However, since $X=B{j} \cap B{k}$, this is simply $B_{j} \cup B_{k} $. Therefore, $\bigcup_{n=i \text{or n below } i} X_{n} =B_{j} \cup B_{k}= B{i}$, as desired.
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
\par Our encoding of formulas Agda follows the definition above pretty exactly. The first constructor corresponds to the case where we have $\phi \in \{ \exists c \psi, \forall c \psi \}$. It takes a $\phi \in MSO(\Sigma , {c})$, i.e. the $c$-expansion of $\Sigma$ of for some constant $c$, and turns it into a $\Sigma$ formula. \textcolor{red}{HOW?}  The second constructor does a similar thing with relations, except it makes the restriction that the added relation can only take one argument, i.e. it must be a set. This is done in the code by specifying that the R in $MSO(\Sigma \cup {R})$ does not have an arbitrary list of argument types $\tau$s but rather a one-element list of argument types, $r$ ($\tau$ :: []).  The third constructor corresponds to creating ands and ors out of smaller formulas, as in the definition. Then, we add the atomic formulae true and false, i.e. $\top$ and $\perp$.
\par Now we come to the most interesting case for the code, the atomic relation formulas. We introduce a datatype called Terms in order to make the definition work. Terms has two constructors, $[]$ (empty) and $,t$ (add one term). In the add one term case, we see that Terms $\Sigma$ $\tau$s makes sure that there are symbols in $\Sigma$ that have type $\tau$ for all $\tau \in \tau$s. In other words: recall that a signature $\Sigma$ is a list of symbols, or placeholders, each of a certain type $\tau$. Terms ensures that there are actually placeholders in $\Sigma$ that want elements of type $\tau$ for every $\tau \in \tau$s. Then the atomic formula constructor of Formula takes a tuple of set elements, $r$, of type $\tau s$, along with evidence that $\tau s$ is the right type for the realtion in question, and out of these elements, creates a formula.\textcolor{red}{IS THIS RIGHT? THIS IS NECESSARY FOR THE RELATION CONSTRUCTOR BECAUSE.....?}
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
\par Let's see how the function $f : (\text{elements of the set } A1) \rightarrow (\text{elements of the set } A2)$ in preserves satisfies all but the bijection conditions of the function $h$ above. We prove that this by induction over the structures $\mathds{A}1$ and $\mathds{A}2$ that $f$ relates, which corresponds to the proof in the code.
\par As a base case, we have that both $\mathds{A}1$ and $\mathds{A}2$  are empty structures, i.e. they are structures over an empty signature, so all of the conditions of $h$ are satisfied vacuously.
\par Now we begin our inductive steps. First, we have the case where $\mathds{A}1$ = $(A1 , s1 ,is\space x)$and $\mathds{A}2$ =  $(A2 , s2 ,is\space xx)$, i.e. both structures are extensions with an Individ. %Individs?
By the inductive hypothesis, we have that there is a function $f$ between $(A1 , s1)$ and  $(A2 , s2)$, such that it upholds all of the conditions of $h$. Then we extend this function $f$ to a function $f'$ that keeps all of $f$ the same, and also maps the new Individ, the extension $x$, in  $\mathds{A}1$ to the extension $xx$ in $\mathds{A}2$. This satisfies the first property, because by induction $f$ satisfies all the conditions of h; and then this new assignment satisfies the first property because it sends an interpreted element to an interpreted element. (In case it is not clear, the "none" extensions in the structure correspond to a constant being interpreted as nil, and the extensions with Individ correspond to a constant being interpreted by a set element. Broadly, each structure extension corresponds to interpreting a new symbol of a signature.) $f'$ satisfies the second condition of $h$, that $h(c^{\mathds{A}})=c^{\mathds{B}}$ for all constants $c \in \Sigma$: again, by our inductive hypothesis, we only have to pay attention to the assignment of $f(x) = xx$. Since $\mathds{A}1$ and  $\mathds{A}2$ are mandated to have the same signature, they must be filling in the same constant, call it $c_{i}$, of their signature with this extension. By sending $f(x) = xx$,

we then are sending $c^{\mathds{A}}_{i} \rightarrow c^{\mathds{B}}_{i}$ under $f'$. (The "fst" in the code is just to isolate the set element portion of an IndividS from the information of what set it belongs to---don't worry about it).   \textcolor{red}{is this explanation correct??}
$f'$ satisfies the third condition of $h$ by the inductive hypothesis, because no new relations are added to the signature at this step.  \textcolor{red}{is this  correct?? I feel like no.} Is it more like... all relation tuples that do not contain $c_{i}$ satisfy this property by the inductive hypothesis. Now that we also have $c^{\mathds{A}}_{i} \rightarrow c^{\mathds{B}}_{i}$ under $f'$, any relation symbol R that contains $c_{i}$ will also have this property (????).
\par Now we consider the case where one structure, without loss of generality suppose $\mathds{A}1$, is extended with a nil (none) and $\mathds{A}2$ is not. This is a violation of condition one of isomorphism above, so we do nothing in this case: Void simply means false, or impossible. In this case, we do not extend $f$. This ensures that there is never and $f$ between two structures where $f(c_{i}^{\mathds{A}_{1}} =c_{i}^{\mathds{A}_{2}}$ where $c_{i}^{\mathds{A}_{1}}\in A_{1}$ and $c_{i}^{\mathds{A}_{1}}=$ nil, in order for $f$ to satisfy the first condition of $h$.
\par Now, consider the case where both $\mathds{A}1$ and $\mathds{A}2$ are extended with nils. Then we say that our extension $f' = f$, and this satisfies condition one of two structures being isomorphic, and the two conditions of $h$, by the inductive hypothesis.
\par Finally, we get to the case where we extend each structure by a relation tuple, $U1$ and $U2$. In this case, we keep $f$ the same, but we require a proof that that the third condition of $h$ holds for the relation tuples $U1 = R^{\mathds{A}1}_{i}$ and  $U2 = R^{\mathds{A}2}_{i}$. Then the proof that this case upholds all the necessary conditions of isomorphism, besides the fact that $f$ is not a bijection, is similar to the proof for extensions with constants above.
\par You might ask, why are there not instances of where one structure extends with a relation and another with a constant or a nil? This is because the structures are mandated to have the same signature. \textcolor{red}{is this explanation correct??}
\begin{code}
  iso : ∀ {Σ oc1 oc2} (A1 : Structure oc1 Σ) (A2 : Structure oc2 Σ) → Type
  iso A1 A2 = Σ \ (f : ∀ {τ} → IndividS (fst A1) τ → IndividS (fst A2) τ )
                → preserves A1 A2 f × (∀ τ → IsEquiv (f {τ})))
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
\par The paper that we base our implementation off of uses games, instead of automata, or fly-automata, or another method, to determine if a given MSO sentence holds on a given structure. Model checking games, or MC games, are based off of pebble games, which we define below.
\par [A pebble game $G = (P, M P_{0}, P_{1}, p_{0})$ between two players, say Player 0 and Player 1, consists of a finite set $P$ of positions, two disjoint sets $P_{0}, P_{1} \subset P$ which assign positions to the two players, an initial position $p_{0} \in P$, and an acyclic binary relation $M \subset P \times P$, which specifies the valid moves in the game (i.e., how to get from one position to another). We only allow moves \textit{from} positions assigned to one of the two players, i.e. we require $p \in P_{0} \cup P_{1} \forall (p, p') \in M$. On the other hand, we do allow that positions without outgoing moves are assigned to players. Let $\lvert G \rvert := \lvert P \rvert$ be the size of $G$. At each round of play $i$,  $ 1 \leq i \leq l$, the player assigned to position $p_{i}$ has to pick a valid next position, i.e. a $p_{i+1}$ such that $(p_{i}, p_{i+1}) \in M$. %For $p \in P$, we let $next_{G}(p)={p'}
A play of $G$ is a maximal sequence $(p_{0},...,p_{l})$ of positions $p_{0},...,p_{l} \in P_{0} \cup P_{1}$, such that $(p_{i}, p_{i+1}) \in M$, i.e. all positions adjacent in the sequence have a valid move between them. Since M is acyclic, such a play is finite, and is said to have $l$ rounds and end in position $p_{l}$. If $p_{l} \in P_{0}$, Player 1 wins, and if $p_{l} \in P_{1}$, Player 0 wins. If $p_{l} \notin P_{0}\cup P_{1}$ then the game is a draw. The object of the game is to force the opposite player into a place where they cannot move. A player is said to have a winning strategy on a game $G$ if and only if they can win the game on every play, no matter what the choices of the other player. Player $i$ has a winning strategy on a game $G$ if and only if
\begin{itemize}
\item $p_{0} \in P_{i}$ and there is a move $(p_{0}, p_{1}) \in M$, for some choice of $p_{1}$ such that Player $i$ has a winning strategy on $subgame_{G}(p_{1})$, or
\item $p_{0} \in P_{1-i}$ and Player $i$ has a winning strategy on $subgame_{G}(p_{1})$ for all valid choices of $p_{1}.$
\end{itemize}
\par A game $G$ is said to be determined if either one of the players has a winnings strategy, otherwise $G$ is undetermined. The game returns either some indication either player 1 or player 2 has a winning strategy, or a proof that the game is a draw. (all from game theory paper, more or less)
\subsubsection{Model Checking Games}\cite{kneis}
\par MC games are pebble games specific to a given formula and structure. In the case of MC games, we call one player the falsifier, who wants to show that the formula is false on the given structure, and one player the verifier, who wants to show that the formula is true on the given structure. A model checking game $MC(\mathds{A}, \phi) =  (P, M P_{f}, P_{v}, p_{0})$, over a $\Sigma$-structure $\mathds{A}$ that fully interprets $\Sigma$, and $\phi \in MSO(\Sigma)$, is defined by induction over $\phi$ as follows: we define $p_{0} = (\mathds{A}[\overline{c}^\mathds{A}], \phi)$, where $\overline{c}$ = {all constants $c \in \Sigma$}.
\par If $\phi$ is an atomic formula , i.e. $R(a_{1}, a_{2}, ... a{p})$ or $\neg R(a_{1}, a_{2}, ... a{p})$ for some $R \in \Sigma, (a_{1}, a_{2}, ... a{p}) \in A^{p}$, then $MC(\mathds{A}, \phi) =  (p_{0}, \emptyset, P_{f}, P_{v}, p_{0})$, and $p_{0} \in P_{f}$ if the atomic formula is true (which will make $ P_{f}$, the falsifier, lose) and $p_{0} \in P_{v}$ if the atomic formula is false (which will make $ P_{v}$, the verifier, lose).
\par If $\phi \in {\forall R \psi, \exists R \psi}$ for some relation R, then let $A_{u}=(A, U)$ for $U \subset A$ be the $(\Sigma, R)$-expansion of $\mathds{A}$ with $R^{\mathds{A}_{U}}=U$, and let $MC(\mathds{A}_{U}, \psi) = (P_{U}, M_{U}, P_{f,U}, P_{v,U}, p_{U})$ be the corresponding model checking games over $\mathds{A}_{U}$ and $\psi$. Then $MC(\mathds{A}, \phi)= (P, M, P_{f}, P_{v}, p_{0})$ where
\begin{itemize}
\item $P = {p_{0}} \cup \bigcup_{U \subset A} P_{U}$
\item $M = \bigcup_{U \subset A} (M_{U} \cup {p_{0}, p_{U}})$
\item  $P_{f} = {P_{f}'} \cup \bigcup_{U \subset A} P_{f,U}$, where $P_{f}'= {p_{0}}$ iff $\phi = \forall R \psi$ and $\emptyset$ otherwise, and similarly
\item  $P_{v} = {P_{v}'} \cup \bigcup_{U \subset A} P_{v, U}$, where $P_{v}'= {p_{0}}$ iff $\phi = \exists R \psi$ and $\emptyset$ otherwise
\end{itemize}
\par If $\phi \in {\forall c \psi, \exists c \psi}$ for some nullary symbol c, then let $A_{a}=(A, a)$ for $U \subset A$ be the $(\Sigma, c)$-expansion of $\mathds{A}$ with $c^{\mathds{A}_{a}}=a \in A$, and let $MC(\mathds{A}_{a}, \psi) = (P_{a}, M_{a}, P_{f,a}, P_{v,a}, p_{a})$ be the corresponding model checking games over $\mathds{A}_{a}$ and $\psi$. Then $MC(\mathds{A}, \phi)= (P, M, P_{f}, P_{v}, p_{0})$ where
\begin{itemize}
\item $P = {p_{0}} \cup \bigcup_{a \in A} P_{a}$
\item $M = \bigcup_{a \in A} (M_{a} \cup {p_{0}, p_{a}})$
\item  $P_{f} = {P_{f}'} \cup \bigcup_{a \in A} P_{f,a}$, where $P_{f}'= {p_{0}}$ iff $\phi = \forall c \psi$ and $\emptyset$ otherwise, and similarly
\item  $P_{v} = {P_{v}'} \cup \bigcup_{a \in A} P_{v, a}$, where $P_{v}'= {p_{0}}$ iff $\phi = \exists c \psi$ and $\emptyset$ otherwise
\end{itemize}
\par If $\phi \in {\psi_{1} \vee \psi_{2}, \psi_{1} \wedge \psi_{2}}$, then let $MC(\mathds{A}, \psi) = (P_{\psi}, M_{\psi}, P_{f,\psi}, P_{v,\psi}, p_{\psi})$ be the corresponding model checking games over $\mathds{A}_{\psi}$ and $\psi \in {\psi_{1}, \psi_{2}}$. Then $MC(\mathds{A}, \phi)= (P, M, P_{f}, P_{v}, p_{0})$ where
\begin{itemize}
\item $P = {p_{0}} \cup \bigcup_{\psi \in {\psi_{1}, \psi_{2}}} P_{\psi}$
\item $M = \bigcup_{\psi \in {\psi_{1}, \psi_{2} }} (M_{\psi} \cup {p_{0}, p_{\psi}})$
\item  $P_{f} = {P_{f}'} \cup \bigcup_{\psi \in {\psi_{1}, \psi_{2}}} P_{f,\psi}$, where $P_{f}'= {p_{0}}$ iff $\phi = \psi_{1} \wedge \psi_{2}$ and $\emptyset$ otherwise, and similarly
\item  $P_{v} = {P_{v}'} \cup \bigcup_{\psi \in {\psi_{1} , \psi_{2}}} P_{v, \psi}$, where $P_{v}'= {p_{0}}$ iff $\phi =  \psi_{1} \vee \psi_{2}$ and $\emptyset$ otherwise
\end{itemize}
\par In our Agda formulation, we take the game-theoretic nature out of the algorithm. We do not have players and games per se. We treat games essentially as trees that map out different possible interpretations of formula variables over a given structure. At each node there is a formula constructor, and each branch connects that node to all its possible sub-formulae on the given structure. \textcolor{red}{include graphic elsewhere?}
\\
\\
\\
\includegraphics{gameEx}
\\
\\
\\
For example, if there is a $\forall x$ in the formula, where $x$ is a free constant variable, then there will be a node in the tree corresponding to $\forall x$, and each branch coming from that node will correspond to a different possible interpretations of $x$ from the available structure. If there is an "and" in the formula, then there will be an "and" node that has branches to each of its sub-formulae.
\par It has been proven that the verifier has a winning strategy on a model-checking game $MC(\mathds{A}, \phi)$ if and only if $\mathds{A} \vdash \phi$ \cite{modelgame}.
\par The Agda formulation of MC games is an operation on structures and formulas we call  "$\vdash c$", or "closed truth". Note that instead of "$\vdash c$" being a game, we simply say that for a structure (A , SA) and a formula $\phi$ $(A , SA) \vdash c\phi$ holds if the verifier of an MC game $MC((A, SA), \phi)$ has a winning strategy. If the falsifier has a winning strategy, $(A , SA) \vdash c\phi$ fails. This is how we take the game-theoretic element out of the algorithm; we simply model a structure very similar to the definition of game given in the code. Other than this, however, the code, below, follows the definition of MC games pretty exactly.
\par We have to trudge through some background code before we can give the definition of "$\vdash c$" directly. We define three helper functions, Value, get, and gets, which help us pick out actual elements from the underlying set to fill our symbols with when needed, that is,  when we need to check that $(c^{\mathds{A}}_{1}, ...c^{\mathds{A}}_{1}) \in R^{\mathds{A}}$ for some atomic formula $R(c_{1}...c_{m})$, or that $(c^{\mathds{A}}_{1}, ...c^{\mathds{A}}_{1}) \notin R^{\mathds{A}}$ for $\neg R(c_{1}...c_{m})$, as the definition for MC games specifies.
\begin{code}
 Value : Subset → SigThing → Type
  Value A (i τ) = IndividS A τ
  Value A (r τs) = (IndividsS A τs → Type)
\end{code}
\par Value takes a Subset, the underlying set of the structure in question, and a SigThing, i.e. a symbol. In the case that it is given a constant symbol, it returns the interpretation of that symbol. In the case that it is given a relation symbol, it returns a function that checks to see if a given tuple of the correct type is in the relation.
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
\par Now, get takes a SigThing (symbol) in a signature, a closed structure on that same signature, and returns one of the outputs of Value, listed above. In the case that the structure is extended with a \textcolor{red}{HELP HERE!! i0 and i1? Do I need to explain?}
\begin{code}
  gets : ∀ {Σ} {τs : List Tp}
       → Terms Σ τs
       → (A : Structure Closed Σ)
       → IndividsS (fst A) τs
  gets [] A = <>
  gets (x ,t xs) A = (gets xs A) , (get x A)
\end{code}
\par gets takes Terms $\Sigma$ $\tau$, i.e. a tuple of constant symbols in $\Sigma$, a closed structure, and it returns a tuple of set elements from the underlying set of the structure that are of the correct type.
\par Finally, we can come to our code for closed truth. $\vdash c$ requires a $\Sigma$-structure $(A , SA)$ and $\Sigma$-formula $\phi$.  The input $\Sigma$-structure needs to be closed (recall the datatype OC defined way above: this means, as is required in the definition of MC games, that no constants in $\Sigma$ are interpreted as nil in $\mathds{A}$).
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
\par Now we move onto existentials and universal formulas over constants. If $\phi = \forall c \psi$, for some constant symbol $c$, then in order for $(A , SA) \vdash c\phi$, $(A , (SA \text{ } ,is \text{ } a)) \vdash c\psi$ needs to hold for all $a \in A$ (for all a : IndividS A $\tau$). This corresponds to the fact that in order for the verifier to have a winning strategy on $MC(\mathds{A},\forall i \psi)$ there needs to be a winning strategy on $MC(\mathds{A_{a}},\psi)$ for all $a \in A$, where $\mathds{A_{a}}$ is the $(\Sigma, c)$ extension structure of $\mathds{A}$. (since on universal formulas, the falsifier would go first).
\par If $\phi = \exists c \psi$, for some constant symbol $c$, then in order for $(A , SA) \vdash c\phi$, there needs to exist some $a \in A$, i.e. some a : IndividS A $\tau$, such that $(A , (SA \space ,is \space a)) \vdash c\psi$. (The $\Sigma  a \rightarrow$ in the code corresponds to "exists an a such that"). This, in turn, corresponds to the fact that in order for the verifier to have a winning strategy on $MC(\mathds{A},\exists c \psi)$, there needs to be just one $a \in A$, one next move, such that the verifier has a winning strategy on the subgame $MC(\mathds{A_{a}},\psi)$. A very similar explanation works with the cases $\phi \in  {\forall R \psi, \exists R \psi}$ where R is written in the code as p.
\par Now consider the case where the formula is atomic, i.e. $R(c_{1}, c_{2}, ... c_{p})$ or $\neg R(c_{1}, c_{2}, ... c{p})$ for some $R \in \Sigma$. In the first case, in order for the verifier to win, the formula needs to be true, i.e. that $(c^{\mathds{A}}_{1}, ...c^{\mathds{A}}_{1}) \in R^{\mathds{A}}$. And, in order for the verifier to win, this step needs to be the turn of the falsier, so that the falsifier gets trapped. Since we have done away with the notion of playing a game, we just keep the condition that the formula is true, i.e. $(c^{\mathds{A}}_{1}, ...c^{\mathds{A}}_{1}) \in R^{\mathds{A}}$. The corresponding (R rel xs) constructor in the code is exactly a proof that $(c^{\mathds{A}}_{1}, ...c^{\mathds{A}}_{1}) \in R^{\mathds{A}}$. Firstly, rel is a set that corresponds to a relation and $xs$ corresponds to the tuple of nullary constants $(c_{1}, ... c_{m})$.
gets xs A is an individsS, i.e. a list of set elements of A which interpret the constant symbols specified in $xs$, and get rel A (gets xs A) checks to make sure that this list of set elements is actually inside rel, the interpretation of the relation symbol R in A. So, get rel A (gets xs A) holds only if, indeed,  $(c^{\mathds{A}}_{1}, ...c^{\mathds{A}}_{1}) \in R^{\mathds{A}}$, and so $A \vdash c$ (R rel xs) only holds if this is true. A similar argument works for the negation case, but with the constructor only holding if the elements are not in R.
\par In the case where $\phi = \psi1 \wedge \psi2$, the falsifier would go first, so the verifier needs winning strategies on both subgames, i.e. $(A , SA) \vdash c \psi1 \wedge \psi2$ requires that both $(A , SA) \vdash c \psi1$ and $(A , SA) \vdash c \psi 2$.
\par %first define general notion of games as moves and tokens; without formulas and structure
%Then define the MC game for a formula and a structure
\subsubsection{EMC Games}
\par Model checking games are all well and good, but some structures have nils in them, and MC games do not accept that. More pointedly, MC games on their own do not possess the qualities that we need them to have in order for them to be useful in giving an algorithm for Courcelle's Theorem. Recall our explanation of the overall algorithm. Essentially, in order to prevent exponential blow up for the algorithm at every quantifier (as occurs on the automata implementation of Courcelle's Theorem), we never want to check a quantifier over the entire set of nodes and edges in a graph. Instead of looking at the whole graph at once, the algorithm in Kneiss et. al. looks at in pieces: for a structure $\mathds{A}$, the pieces are the restrictions $\mathds{A}[A_{i}]$ associated with each node of the tree decomposition. (Recall that for a node $i$ of a tree decomposition, we let $A_{i}=\bigcup_{j \text{at or below } i} X_{j}$, and $\mathds{A}[A_{i}]$ is the restriction of $\mathds{A}$ to that subset.) The algorithm that we use to prove Courcelle's theorem traverses the given tree decomposition bottom up, checking to see if the formula holds on $\mathds{A}[A_{i}]$ for each node, starting at the empty leaves, and adding a little bit of the set at a time.
\par This may sound like malarkey: first of all, these subsets do not fully interpret the signature, and secondly, how do we know that if there is a winning strategy on one of these smaller games, it propagates to a winning strategy on the overall game? To satisfy the first point, we need games that can handle nil assignments, which is the first handy property of EMC games. Additionally, consider the idea that, if you can satisfy an equation with a structure full of nil assignments, you can satisfy that equation on a structure with any interpretations for those nil assignments, because the elements that are interpreted as nil are not doing anything consequential if they don't prevent the MSO formula from being satisfied. This is because if the constants were important, if some $c^{\mathds{A}}_{i}$ were interpreted as nil came up in some atomic formula $R(c_{1}....c_{n})$, at the end of the game, then the tgame would be undefined by definition. But if the game comes back true, this means that that particular constant had nothing to do with the formula at all, since this situation never arose. So having a winning strategy on some game made with a restricted structure, chock full of nils as it may be, should propagate to having a winning strategy on the full game, since giving specific values to constants that weren't affecting the formula anyway is not going to change anything. But even with this fact, we still have to come up with a way of propagating the winning strategy upward. We have to find a method of seamlessly transitioning from a game on a restricted structure to a game on the a larger restriction, or the whole structure.
\par Consider the fact that for each node $i$ in a tree-decomposition $T$ of a structure $\mathds{A}$, while we have  $A_{i}=\bigcup_{j \text{at or below } i} X_{j}$, we can also consider $A \setminus A_{i} := B_{i}$, the set of everything in A not yet taken into account by the tree decomposition. This set is often called, illustratively, the future of $A_{i}$. Just as we can restrict $\mathds{A}[A_{i}]$, we can define a structure $\mathds{A}[B_{i}]$. Recalling our notion of the union of two structures from earlier, see that at any node $i$, $\mathds{A}=\mathds{A}[A_{i}] \cup \mathds{A}[B_{i}]$. So, the condition we want is that, if we have a winning strategy on a game for $\mathds{A}[A_{i}]$ and $\phi$, then we want to propagate this to a winning strategy on $\mathds{A}[A_{i}] \cup \mathds{A}[B_{i}] $ and $\phi$. Thankfully, Kneiss et. al. created EMCs with the property that are well-defined on taking the union of structures (provided the structures are compatible)\cite{kneis}.
\par To summarize, Kneis et. al. developed another form of model checking game, which does allow structures with nils, and is well defined over taking unions of compatible structures, i.e. if there is a winning strategy for a game over $\mathds{A}$ and $\phi$, that translates to a winning strategy on $\mathds{A} \cup \mathds{B}$ and $\phi$ for two compatible structures $\mathds{A}$ and $\mathds{B}$.  In the Kneiss et. al. paper, an EMC is defined to keep track of what bag of the tree decomposition it is on. We found this unnecessary in the code, but provide the original definition here for clarity.
\par [An extended model checking game $EMC(\mathds{A}, X, \phi) = (P, M, P_{f}, P_{v}, p_{0})$, over a $\Sigma$-structure $\mathds{A}$, a set X $\subset$ A, and $\phi \in MSO(\Sigma)$, is defined over induction over the structure of $\phi$ as follows. Let $p_{0} = (\mathds{A}[\overline{c}^\mathds{A} \cup X], \phi)$, where again $\overline{c}$ = {all constants $c \in \Sigma$}. If $\phi$ is an atomic formula, then $EMC(\mathds{A}, X, \phi) = ({p_{0}}, \emptyset, P_{f}, P_{v}, p_{0})$, where $p_{0} \in P_{f} $ if and only if there are no nils in the relation tuple and the formula is true; i.e. if the formula is $R(c_{1}, c_{2}, ... c_{p})$ or $\neg R(c_{1}, c_{2}, ... c{p})$ for some $R \in \Sigma$, then each $c^{\mathds{A}}_{i}$ in $(c^{\mathds{A}}_{1}, ...c^{\mathds{A}}_{1})$ must not be nil, and the formula is actually true, i.e.  $(c^{\mathds{A}}_{1}, ...c^{\mathds{A}}_{1}) \in R^{\mathds{A}}$. Again, as explained for MC games, this will make the verifier win. Alternatively, $p_{0} \in P_{v}$ if the tuple $(c_{1}, c_{2}, ... c_{p})$ is fully interpreted, and the atomic formula is false (which will make $ P_{v}$, the verifier, lose).
\par If $\phi \in \{ \psi_{1} \wedge \psi_{2}, \psi_{1} \vee \psi_{2}, \exists R \psi, \forall R \psi\} $ for some relation R, then EMC games are defined exactly the same as MC games above.
\par If $\phi \in \{ \exists c \psi, \forall c \psi \}$ for some constant $c$, then the definition for an EMC game is almost exactly the same as that of an MC game, except that we also add the possibility of extending our structure $\mathds{A}$ with a nil, not just elements of $A$. That is, we let $\mathds{A_{u}}$ be the $(\Sigma, c)$ expansion of $\mathds{A}$ as before, but this time we let either $c^{A_{u}} = u \in A$ OR  $c^{A_{u}}= nil.$ Let $EMC(\mathds{A}_{u}, X, \psi) = (P_{u}, M_{u}, P_{u,f}, P_{u,v}, p_{u})$ be the corresponding EMC game over $\mathds{A_{u}}, \psi$ as before. Then, $EMC(\mathds{A}, X, \phi) = (P, M P_{f}, P_{v}, p_{0})$ where
\begin{itemize}
\item $P = {p_{0}} \cup \bigcup_{u \in A\cup {nil}} P_{u}$
\item $M = \bigcup_{u \in A\cup {nil}} (M_{u} \cup {p_{0}, p_{u})}$
\item  $P_{f} = {P_{f}'} \cup \bigcup_{u \in A\cup {nil}} P_{f,u}$, where $P_{f}'= {p_{0}}$ iff $\phi = \forall c \psi$ and $\emptyset $otherwise, and similarly
\item  $P_{v} = {P_{v}'} \cup \bigcup_{u \in A\cup {nil}} P_{v, u}$, where $P_{v}'= {p_{0}}$ iff $\phi = \exists c \psi$ and $\emptyset$ otherwise] \cite{kneis}
\end{itemize}
\par The way that we model EMC games in the code is through a datatype "$\vdash$ o", or open truth. Similar to our definition of closed truth above, we do away with the notion of a game and players, and just outline "$\vdash o$" so that for a structure $\mathds{A}$ and a formula $\phi$, $\mathds{A} \vdash o \Sigma$ if and only if there is a winning strategy for the verifier on an EMC game $EMC(\mathds{A}, X, \phi)$. Before we can get to this definition, however, we have to explain some of the code leading up to it.
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
\par Similar to our code for closed truth, we define ValueOpen, getOpen, and getsOpen, which perform almost the same functions that Value, get, and gets do, except that they all take into account the fact that for open truth/EMC games, we could be working with open structures, which may contain nils. So, ValueOpen, instead of returning an set element that is an interpretation when given a nullary constant, gives either None (for nil) or Some v (for some set element). This propagates through getOpen and getsOpen: getOpen .... \textcolor{red}{HELP}. getsOpen, when given Terms (a tuple of constant symbols) and a structure, returns a tuple of elements that interpret the constant symbols--except that, if even one of the symbols is not interpreted, it returns a None value instead of a tuple of set elements.
\par Differing from what we did for closed truth, we have three constructors for open truth: one for existential formulas, one for universal formulas, and one for atomic formulas. In order to explain this, we need to show some code that leads up to it.
\par We defined predicates on formulae that determined whether a given formula was existential $(\phi = \exists R \psi, \exists c \psi, \psi_{1} \vee \psi_{2})$ universal $(\phi = \forall R \psi, \forall c \psi, \psi_{1} \wedge \psi_{2})$, or an atomic relation ($R$ or $\neg R$ for some arity(R)-tuple of constants). These predicates have different constructors for each kind of existential, universal, or atomic formula. For example, isE has a constructor for each of $\{ \exists i, \exists R, \vee, \perp \}$.
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
\par Based on these different types of formulae, we defined a notion of a branch, of which there are universal branches and existential branches. Think of a branch as an edge between two nodes in a game: it keeps track of which formula and structure the game is are traveling from and towards. (For as the algorithm goes through a game, the formula and structure shrinks). So if there is a node (i.e. a position in the definition above) %is this right??
$(\mathds{A}, \phi)$ where one possible next move is to $(\mathds{A} ', \phi ')$, then there will be a branch "branch $\mathds{A}$ $\phi$  $\mathds{A} '$ $\phi '$" to in the game to show that. We will see further below in our definition of game.  %is this right?
Included below is only the universal branch code, as the existential branch code is quite similar. Ubranch has a different constructor for all the different kinds of branches required for different formulas. For an and node, $\phi = \psi_{1} \wedge \psi_{2}$, we need a branch going to each of $\psi_{1}$ and $\psi_{2}$, and this is what ufstb and usndb are. If  $\phi = \forall c \psi$, we need a branch $\mathds{A} \rightarrow \mathds{A}'$ where $\mathds{A}'$ is a $c$-expansion of $\mathds{A}$ with $a$ interpreted as $c$. Finally, in the case that $\phi = \forall R \psi$, ubranch creates a branch for all tuples $r$ of elements in $A$ to interpret $R$. \textcolor{red}{is this right??}
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
    ebr : ∀ {Σ2} {oc1 oc2} {A1 : Structure oc1 Σ1} {φ1 : Formula Σ1}
            {A2 : StructureS  oc2 (fst A1) Σ2} {φ2 : Formula Σ2}
            → isE φ1 → ebranch A1 φ1 A2 φ2 → branch A1 φ1 A2 φ2
    ubr : ∀ {Σ2} {oc1 oc2} {A1 : Structure oc1 Σ1} {φ1 : Formula Σ1}
            {A2 : StructureS oc2 (fst A1) Σ2} {φ2 : Formula Σ2}
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
\par Let's see how works. Consider the provesbase case in the code, which corresponds to the place in the EMC definition where the formula is $R(c_{1}, ...c_{m})$ for some relation symbol $R$ in $\Sigma$. In the mathematical definition, in order for the verifier to win in this case, the atomic formula needs to be correct, and it should be the falsifier's turn. Since we have taken the notion of players in the game out, we only need the proof that the atomic formula is true. And this is exactly what the provesbase constructor is: a proof that the formula holds. Given a tuple, vs, of elements in the underlying set (i.e. vs : IndividsS $A$ $\tau s$) ((getsOpen xs A) == (Some vs)) is a proof that the xs, i.e. the tuple $(c_{1}, ...c_{m})$ in the formula $R(c_{1}, ...c_{m})$ is actually interpreted as this tuple of set elements vs, i.e. there are no nils. We can see this because getsOpen takes a list of constant symbols (Terms $\Sigma \tau s$) and a structure, and makes sure that each of those symbols is interpreted on that structure (i.e. returns "Some v" in ValueOpen). \textcolor{red}{(Or is it that  ((getsOpen xs A) == (Some vs)) ensures that all of the elements in the given tuple at that node are interpreted, i.e. not nil, because getsOpen takes a list of constant symbols (Terms $\Sigma \tau s$) and a structure, and makes sure that each of those symbols is interpreted on that structure (i.e. returns "Some v" in ValueOpen).?} Then, (getOpen rel A) (vs) checks to make sure that vs, the actual tuple of elements of A (the IndividsS-A-$\tau$s), is actually in $R^{\mathds{A}}$. We see this because getOpen will return a ValueOpen for this relation rel on A, i.e. a function that checks if a given tuple is in a given relation, and so in (getOpen rel A) (vs) we are using that given function to check if $vs \in R^{\mathds{A}}$. A similar proof will show that the provesnotbase constructor is a proof that $\neg R(c_{1}, ...c_{m})$ holds, i.e. $(c^{\mathds{A}}_{1}, ...c^{\mathds{A}}_{m}) \notin R^{\mathds{A}}$. The only real difference is that in the provesnotbase constructor, the ((getOpen rel A) (vs) $\rightarrow$ Void) signifies that the tuple vs is not in $R^{\mathds{A}}$.
\par Now let's consider the provesu constructor. This maps to the case in the definition where we have any universal formula: $\phi \in {\forall c \psi, \forall R \psi, \psi_{1} \wedge \psi_{2}}$. The provesu constructor is a proof that
\begin{enumerate}
\item The formula is universal (IsU $\phi$)
\item For all $\Sigma '$-structures $\mathds{A}'$ with the same underlying set as $\mathds{A}$, and all $\Sigma '$-formulas $\phi '$, if there's a branch (a ubranch, since we're in the universal case) between $\mathds{A}$, $\phi$ and $\mathds{A}'$ $\phi '$, then $\mathds{A}' \vdash o \phi '$
\end{enumerate}
\par Note that depending on what exact formula $\phi$ is, the ubranches from $\phi$ will branch to different  $\mathds{A}'$, $\phi '$-- we don't make a separate constructor for each case. But if, for example, the formula was $\forall c \psi$ for some constant $c$, then there would be a ubranch for $\mathds{A_{a}}$ for all $a \in A$, where $\mathds{A_{a}}$ is a $\Sigma , c$ extension of $\mathds{A}$ with c interpreted as $a$ for all $a \in A$. This corresponds to a winning strategy for the verifier because, since the falsifier gets to choose the next move on a universal quantifier, the verifier needs a winning strategy on every subgame that the falsifier could move to. We interpret this as $\mathds{A}' \vdash o \phi '$ for every possible $\mathds{A}'$, $\phi '$ we can branch to from $\mathds{A}$, $\phi$.
\par A very similar explanation to the one above works for the provese constructor. In this case, we just need to show that the formula is existential, and that $\mathds{A}' \vdash o \phi '$ for one possible $\mathds{A}'$, $\phi '$ we can branch to from $\mathds{A}$, $\phi$. This corresponds to the verifier having a winning strategy on a corresponding EMC game because since the verifer gets to choose the next move on existentials, we only need to find one subgame that the verifier can win, i.e. where  $\mathds{A}' \vdash o \phi '$. Again, the specific subgames that are checked depend on the ebranch constructor. We also have a definition,  $ \vdash o $false, which takes a structure and a formula as before and shows that the formula is false on that structure. This corresponds to a falsifier having a winning strategy on an analogous EMC game, and we define it as a  $ \vdash o $ that proves the negation of the formula given.
\subsection{Reduced Games}
\par As described above, the algorithm used to prove Courcelle's theorem in the Kneiss paper runs through an entire EMC game on each node of the tree decomposition, and propagates undecided games upward through the tree decomposition until it has enough data to come to a definitive answer as to whether or not the formula holds on the given structure. In order to further reduce the time of the algorithm, we want to be running games as efficiently as possible. In order to do this, we want to keep as few possible next positions (analogously in our code, as few branches) as possible. This way, we have fewer places to move to at each step, and so our game becomes much smaller. We would like to keep track of only the necessary information as we propagate games upward. For example, if we are able to achieve a winning or losing strategy on a game at a given node, we want to exit the algorithm there since we've found out answer. If our game is undecided, we still don't have to keep all information that is available to us: for example, if our formula is universal, we don't have to keep track of all of the different subgames that prove the formula true.
\par With this in mind, we introduce another game-like structure in the Agda code, which will become the underlying type for something called a reduced game. A reduced game will keep track of only the information from any given game that we absolutely need. The explanation for all of this will come later, but because of the way the code is structured, we will introduce a constructor called $\vdash s$, which we call a "raw game tree", now.
\begin{code}
 data _⊩s_ {oc : _} {Σ : _} (A : Structure oc Σ) (φ : Formula Σ) : Type where
    leaf : (isR φ) → A ⊩s φ
    node : (bs : Branches A φ)
         → (∀ {Σ'} {oc'} {A' : StructureS oc' (fst A) Σ'} {φ'} b
         → (branchto A' φ' b) ∈ bs → ((fst A , A') ⊩s φ'))
         → A ⊩s φ
\end{code}
\par A $\vdash s$ is a game that is either atomic, or has a certain set of branches. However, which branches these are is not specified. That is, it does not require the exact set of outward branches (subgames) that opentruth or closed truth require. We enclose the code below. See that a $\vdash s$ is a datatype with two constructors, leaf and node. The leaf constructor is simply a proof that the formula is atomic, |isR φ|. There are no outward branches, i.e. subgames, here. The node constructor is a product type, consisting of (1) of a list of branches (bs) from the given structure A and formula $\phi$ (i.e. the game position that has structure A and formula $\phi$), and (2) a proof that for all structure, formula pairs $A', \phi '$ (i.e. positions) that any branch $bi \in bs$ points toward, $A' \vdash s \phi'$. We can also think of (2) as a function that takes a branch b, a proof that b is in the list of branches of some game tree gt, and returns a game tree on the structure that b branches towards.
\par Note the difference between opentruth, closedtruth and gametrees: as mentioned earlier, there are no specifications on the branches of a gametree---unlike for the open truth and closed truth datatypes, if the formula $\phi = \psi_{1} \wedge \psi_{2}$, there is no requirement in a gametree that there be a branch for both $\psi_{1}$ and $\psi_{2}$. There's just some unspecified list of branches; and what goes in that list will become clear later.
\par Continuing from the conversation above about throwing out unnecessary information in games, how do we decide which next positions (or branches) to keep and which ones to throw away? To help answer this question, we introduce a concept of \textbf{equivalent games}.
\subsubsection{Position Equivalence}
\par Consider a game $EMC(\mathds{A}, X, \phi)$. Two positions $p_{1}, p_{2}$ are position-equivalent, denoted by $p_{1} \cong p_{2}$ if and only if
\begin{itemize}
\item $p_{1} = (\mathds{H}_{1}, X, \phi)$ and $p_{2} = (\mathds{H}_{2}, X, \phi)$ for some formula $\phi$ and set $X \subset \mathds{H}_{1} \cap \mathds{H}_{2}.$
\item There is an isomorphism $h : H_{1} \rightarrow H_{2}$ such between $\mathds{H}_{1}$ and $\mathds{H}_{2}$, such that $h(a)=a$ for all $a \in X$.
\end{itemize}
\par Let's take a look at the Agda encoding of position equivalence. We define position equivalence with two functions, positionequiv' and positionequiv. We discuss positionEquiv first--it may be helpful to look back at the definition and explanation of the function iso (for isomorphism between structures) above, or otherwise just accept that iso called on two structures gives us an isomorphism between them. Also note that $constants(\mathds{A_{i}})$ is the set of elements of $A_{i}$ that were used as interpretations of constants in $\mathds{A_{i}}.$ (The code is below). positionEquiv takes two structures, $A1$ and $A2$, the bag $X$ that they share, proof that $X \subset A1$ and $X \subset A2$  (so that $X \subset A1 \cap A2$), proof that X is decidable (which will go away when we change our definition of subset). positionEquiv holds on these inputs if there is a function $h$ that satisfies iso $\mathds{A}_1[X \cap constants(\mathds{A_{1}})]$ $\mathds{A}_2[X \cap constants(\mathds{A_{2}})]$, i.e. is an isomorphism between $\mathds{A}_1[X \cap constants(\mathds{A_{1}})]$ $\mathds{A}_2[X \cap constants(\mathds{A_{2}})]$, such that $\forall x \in X,$ $h(x) = x$. All of the little functions such as subLUB, constantsDec, unionDec, and promoteIndividS are all just little fixes to convince Agda that everything is the correct type, in the correct subset, etc. (For example, unionDec is a proof that the union of two decidable sets is decidable.) We won't go into these functions, but if the reader is curious, the source code is attached.
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
\par Now we must show why this code is a sufficient definition for positionEquiv above--certainly, at first glance, it seems like it may fall short because we don't have an isomorphism over the entire structure but only the structure restricted to those elements that have been interpreted as constants and the relevant bag, X. But note that this is simply a difference in labeling, not of content. Recall that the position $p_{0}$ of a game $EMC(\mathds{A}, X, \phi) =  (P, M, P_{f}, P_{v}, p_{0})$ is defined as $p_{0} = (\mathds{A}[\overline{c}^\mathds{A} \cup X], \phi)$, where $\overline{c}$ = {all constants $c \in \Sigma$}. Note that the structure at a position is by definition the overall structure restricted to the set elements that are interpreted as constants along with the relevant bag $X$. However, in the Agda code, we don't have a specific type for positions, we just have $\vdash c$ and $\vdash o$ which look like trees with branches between structures, with the entire structure as a label for each node. So, we take this restriction to $\mathds{A}[\overline{c}^\mathds{A} \cup X]$ only when we define position equivalence, to make it match the mathematical definition, where this restriction is implicit. So, the mathematical definition and the code in fact have the same requirements.
\par Quickly, we include our code for positionEquiv'; this does exactly the work that positionEquiv does except it changes the accepted input type slightly so that it works more seamlessly with the rest of the code.
\begin{code}
  positionEquiv' : ∀ {Σ oc1 oc2} (A1 : Structure oc1 Σ) (A2 : Structure oc2 Σ) → fixed (fst A1) (fst A2)  → Type
  positionEquiv' A1 A2 (X , (X⊆A1 ,  X⊆A2) ,  decX )  = positionEquiv A1 A2 X X⊆A1  X⊆A2 decX
\end{code}
\subsubsection{Game Equivalence}
\par We say that two games $G_{1}= (P_{1}, M_{1}, p_{1}), G_{2}= (P_{2}, M_{2}, p_{2})$ are equivalent, denoted $G_{1} \cong G_{2}$, if $p_{1} \cong p_{2}$, and there is a bijection $\pi :$ subgames($G_{1}$) $\rightarrow$ subgames($G_{2}$), such that  $G' \cong \pi (G)$ $\forall G' \in$ subgames($G_{1})$.
\par Now, let's look at our code for proving that two games are equivalent. We have two functions, gameEquiv and gameEquiv', defined mutually, that do this job. These functions rely on a helper definition, BranchBijection. BranchBijection, which is enclosed below, does exactly what it sounds like: it is the proof of a bijection between two sets of branches. (The type Branches is simply a list of branches, which we defined earlier).
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
\par gameEquiv' does most of the work of the recursive calls. It takes the same input as gameEquiv, but here we case on the constructors of the two game trees. If the game trees are both leaves, there are no subgames (i.e. structures that are branched to) and so no recursive calls are needed, the subgames are equivalent vacuously, and gameEquiv' returns Unit, or True. If one gametree is a leaf and the other is a node, there is no possible way for them to be equivalent, so gameEquiv returns Void, or false. Now the interesting case: both gametrees are nodes. Then, |gameEquiv' A1 A2 φ (A1 ⊩s φ) (A2 ⊩s φ) X| holds if there exists a BranchBijection $b$ between the list of branches in the (A2, $\phi$) game tree and the list of branches in the $(A2, \phi$) game tree, such that for all structures A' (with underlying set A1) and formulas $\phi$' that A1 and $\phi$ branches to, gameEquiv A' b(A') $\phi$' A'$\vdash s \phi^{'}$  b(A')$\vdash s \phi^{'}$ X holds. Through mutual recursion, the two functions determine if two games are equivalent, with gameEquiv checking the initial positions are equivalent and gameEquiv' keeps sending the correct subgames to gameEquiv to check for position equivalence.
\par %Let's see how this happens in more detail: "$ \Sigma (\lambda$ (b : BranchBijection A1 A2 $\phi$ bs1 bs2) $\rightarrow$" means "there exists a BranchBijection b such that"; " $\forall$ {?' oc'} {A' : StructureS oc' (fst A1) ?'} {?'} bi ?" means "for all branches bi such that";  "(brnchi : branchto A' ?' bi ? bs1), i.e. there is a proof, brnchi, that $bi \in bs1$, the set of branches of the first gametree of input, and gameEquiv
\par If two games are equivalent, they will have the same outcome. \textcolor{red}{what do I do to back this up?} Certainly, for each game $G$, we only need to keep one representative of each equivalence class of  subgames($G$) modulo $\cong$. Additionally, note that for any game $G$, we can discard the subgames where the opposing player, which in our case will always be the falsifier, wins. There is no use in checking a path that is known to fail.  \textcolor{red}{what do I do to back this up?}
\subsubsection{Reduced Games Definition}
\par With this in mind, we give a definition of a \textbf{reduced game}. A reduced $EMC$ game $G$ over a $\Sigma$-structure $\mathds{A}$ and a $\Sigma$-formula $\phi$, $reduce(\mathds{A}, X, \phi)$ is defined by induction as follows:
\begin{itemize}
\item If $\phi$ is an atomic formula, then the reduced game is defined exactly as a regular EMC game.
\item If $\phi$ is not an atomic formula, then all subgames $G'$ of $G$ must be undecided, and further, $\forall G_{1}' \in $ subgames($G$), $\nexists G_{2}'  \in $ subgames($G$) such that $G_{1}' \cong G_{2}'$. That is, all subgames come from distinct equivalence classes in the $\cong$ relation.
\end{itemize}
\par It may be more instructive to think about how to turn an $EMC$ into a reduced $EMC$ than to simply ponder over the definition. Given an EMC, Kneiss et. al. describe an algorithm for making a reduced $EMC$ $G_{red}$ as follows: if the formula in the game is atomic, treat the reduced EMC game as a regular EMC game. Otherwise, recursively compute all of the reduced subgames of the original EMC, and:
\begin{itemize}
\item If the formula is universal, and there is a subgame $G'$ where the falsifier has a winning strategy, then return that the falsifier won. % $\perp$ (i.e., the statement not being true) then return $\perp$ (i.e. that the formula does not hold over the given structure).
If the falsifier does not have a winning strategy on any subgame, then we define the set of subgames of $G{red}$, subgames($G_{red}$) = ($G'_{1}$, ..$G'_{n}$) such that $\forall i$ $G_{i}$ is undecided, and there does not exist a $j$ such that $G_{i} \cong G_{j}$.
\item If the formula is existential, and there is a subgame $G'$ where the verifier has a winning strategy, then return that the verifier won. If the verifier does not have a winning strategy on any subgame, then we define the set of subgames of $G{red}$, subgames($G_{red}$) = ($G'_{1}$, ..$G'_{n}$) such that $\forall i$ $G_{i}$ is undecided, and there does not exist a $j$ such that $G_{i} \cong G_{j}$.
\end{itemize}
\par So, a reduced game $G$ is a game that has not been decided yet, but that retains as little information as possible in order to speed up the overall algorithm. It may seem counterintuitive that we can throw away so much information and still get the same answer as an EMC game, which is what we would like. Let's think about this a bit. Certainly, we want a game that is undecided, because otherwise we can simply leave the entire algorithm and say we've found that the formula is either true or not true on the structure. Once we've established that the game is undecided, however, still not all information is necessary. For example, if our formula is universal, we don't have to keep track of all of the different subgames that prove the formula true. It doesn't help the future of the algorithm to keep track of the fact that one particular interpretation of symbols satisfied the formula, because all the algorithm looks for is one interpretation that does not satisfy the formula. If one subgame in a universal formula returns true, we breathe a sigh of relief and then discard it, and focus on the games that are undecided. Similarly, if a formula is existential, we don't have to keep track of the subgames that end up being false--because we are just looking for one satisfying interpretation of variables. If the reader can accept this, then all that is left to be convinced of is that the result of a reduced game on a structure $\mathds{A}$ and a formula $\phi$ will always be the same as an EMC game on the same formula and structure. A proof of this fact is on our agenda--we will speak more about what is still to be done in this project in the last section.
\par Now we transition to explaining our encoding of a reduced game. There are a few helper functions for this definition. The moving parts are: $\vdash s$ defined above, which is sort of the underlying type for a reduced game, though not a reduced game itself. We can combine this with another definition $isRed$, a proof that a $\vdash s$ gametree is in fact a reduced game. Then, we trivially put these two pieces together in provesR, which is our formulation of a reduced game, i.e. a $\vdash s$ that satisfies isRed $\vdash s$.
\par We go through the Agda code for isRed, a proof that a gametree g1 is a reduced game.
\begin{code}
 isRed : ∀ {Σ oc} (A : Structure oc Σ) (φ : Formula Σ) → A ⊩s φ → (X : fixed1 (fst A)) → Type
  isRed A φ (leaf x) fix = Unit
  isRed A φ (node bs x) fix =  (∀ {Σ' oc'} {A' : StructureS oc' (fst A) Σ'} {φ'} bj → (prfbr : branchto A' φ' bj ∈ bs) →
                                      isRed (fst A , A') φ' (x bj prfbr) fix)
                                      ×
                               (isU φ → ∀ {Σ' oc'} {A' : StructureS oc' (fst A) Σ'} {φ'} bi →
                                Either (branchto A' φ' bi ∈ bs)
                                  (Either ((fst A , A') ⊩o φ')
                                          (Σ (λ oc'' → Σ (λ (A'' : StructureS oc'' (fst A) Σ') →
                                                  Σ (λ bj → Σ (λ (pfbr2 : branchto A'' φ' bj ∈ bs) →
                                                         (gi : (fst A , A') ⊩s φ') →
                                                         isRed (fst A , A') φ' gi fix →
                                                         gameEquiv (fst A , A') (fst A , A'') φ' gi (x bj pfbr2) (lemma1 _ fix))))))))
                                                   ×
                               (isE φ → ∀ {Σ' oc'} {A' : StructureS oc' (fst A) Σ'} {φ'} bi →
                               Either (branchto A' φ' bi ∈ bs)
                                 (Either ((fst A , A') ⊩o φ' false)
                                       (Σ (λ oc'' → Σ (λ (A'' : StructureS oc'' (fst A) Σ') →
                                             Σ (λ bj → Σ (λ (pfbr2 : branchto A'' φ' bj ∈ bs) →
                                                      (gi : (fst A , A') ⊩s φ') →
                                                      isRed (fst A , A') φ' gi fix →
                                                      gameEquiv (fst A , A') (fst A , A'') φ' gi (x bj pfbr2) (lemma1 _ fix))))))))

\end{code}
\par IsRed takes a structure, $\mathds{A}$, a formula $\phi$, a gametree $\mathds{A} \vdash s \phi$, and a bag X. In the case that the gametree is a leaf, which means it has no outward branches, isRed is true vacuously and so the definition for that case is Unit, or true. In the case that the gametree $\mathds{A} \vdash s \phi$ is a node, we have a double product type; there are three requirements appended together. The first one (the code before the first $\times$) requires that for all structureS's A' and formulas $\phi '$ such that there is a branch  $bj \in bs$ that connects ($\mathds{A}$, $\phi$) $\rightarrow$ ((fst $\mathds{A}$, A'), $\phi$'), there is a reduced game on ((fst $\mathds{A}$, A'), $\phi$'), i.e.   isRed (fst A , A') $\phi$ ' (x bj prfbr) fix holds. In case it is confusing that  (x bj prfbr) is miraculously a gametree (fst A , A') $\vdash s$ $\phi$', recall from the definition of $\vdash s$ that the second argument can be thought of as a function that takes a branch and a proof that that branch is in the list of branches corresponding to some gametree, and returns a gametree on the structure that the branch points to. In the code here, we are calling that second argument "x", and we see that bj is a branch, and prfbr is a proof that bj is in bs, i.e. the list of branches of $A \vdash s \phi$. So, (x bj prfbr) is a gametree (fst A , A') $\vdash s$ $\phi$'.
\par Now, for the next two parts of the product type, the first corresponds to when the formula is universal, the other to when the formula is existential (the atomic cases will only happen with a leaf.) Let's tackle the first out of these two, which corresponds to the formula being universal. The first thing required is a proof that the formula is universal, isU $\phi$. Then we need a proof that for all structureS's A' and formulas $\phi '$such that there is a branch bi  between $(\mathds{A}, \phi)$ and (((fst $\mathds{A}$), A'), $\phi '$), either
\begin{itemize}
\item there is a proof that branch is a part of the list of branches of  $\mathds{A} \vdash s \phi$, or
\item Either ((fst A , A') $\vdash$o $\phi$') i.e. the verifier has a winning strategy on the subgame labeled by that structure, formula pair; or
\item  there is another structureS, A'', such that
\begin{itemize}
\item there is a branch between $(\mathds{A}, \phi)$ and ((fst A, A''), $\phi$') ;
\item there is a subgame (fst A, A'') $\vdash s \phi$' that is reduced, i.e.  isRed (fst A , A') $\phi$' gi fi (where gi = (fst A, A'') $\vdash s \phi$' and fix = the bag X), and importantly, that there is a proof that this subgame is equivalent to (fst A , A') $\vdash$s $\phi$', i.e.  gameEquiv (fst A , A') (fst A , A'') $\phi$' gi (x bj pfbr2) (lemma1 fix)))))))).
\end{itemize}
\end{itemize}
See that this corresponds exactly to the definition that we outlined for reduced games above: in the case of universal formulas, all subgames are true or undecided, and we only keep track of (keep in our special list of branches bs) undecided subgames that are not equivalent to one another.
\par The third part of this product type is very similar, except for the fact that instead of insisting that for all subgames, either the verifier has a winning strategy, and then all the other options listed; we ask that for all subgames, either the falsifier has a winning strategy (Either ((fst A , A') $\vdash$o $\phi$' false)) or one of the other options. Again, we see this matches the mathematical definition for reduced games nicely.
\par And finally, we come to provesR, a combiner that defines a reduced game.
\begin{code}
 provesR : ∀ {Σ oc} (A : Structure oc Σ) (φ : Formula Σ) (X : fixed1 (fst A))  → Type
  provesR  A φ X = Σ (λ (game : A ⊩s φ) → isRed A φ game X)
\end{code}
\par provesR takes a structure $\mathds{A}$, a formula $\phi$, a gametree $\mathds{A} \vdash s \phi$, and a bag X, and gives a proof that there is a gametree $\mathds{A} \vdash s \phi$ such that isRed $\mathds{A}$ $\phi$ $\mathds{A} \vdash s \phi$ X holds.



\section{Outline of Algorithm}
\par While we will prove our own version of the overall proof of the algorithm with our code, we outline the proof from the paper here, which is never explicitly put together for this method of proving Courcelle's Theorem. However, in an effort not to reproduce too much of their paper, we simply rely upon several lemmas from the paper by Kneiss et. al. We reproduce the statement of the lemmas below, but for the proof, please refer to the Kneiss et. al. paper. Additionally, note that we refer to two algorithms not mentioned yet, "combine" and "combine-forget". These are algorithms laid out in the Kneiss et. al. paper which we will not reproduce, but please think of them as similar to the agda functions combineIntro, combineJoin, and combineForget which will be described below, after the proof.
\par We show that given a $\Sigma$-structure $\mathds{A}$ that fully interprets $\Sigma$, a $\Sigma$-formula $\phi \in MSO(\Sigma)$, and a tree decomposition \textbf{T} on $\mathds{A}$ and $\phi$, we can return a game that determines whether or not $\mathds{A}$ satisfies $\phi$. To follow are the lemmas from the paper that we use:
\par \textbf{Lemma 11} Let $\mathds{A}_{1}$ and $\mathds{A}_{2}$ be compatible $\Sigma$-structures, $\phi$ in MSO($\Sigma$) and let $X_{1}\subset A_{1}$ and $X_{2}\subset A_{2}$ with ${A}_{1}\cap {A}_{2}$= ${X}_{1}\cap {X}_{2}$. Then, $combine(reduce(\mathds{A}_{1}, X, \phi), reduce(\mathds{A}_{r}, X, \phi)) \cong reduce(\mathds{A}_{1}\cup \mathds{A}_{2}, X, \phi).$
\par \textbf{Lemma 12} Let $\mathds{A}$ be a $\Sigma$-structure, $X\subset A$, and $x\in X$. Futher, let $reduce(\mathds{A}, X, \phi)\notin {\perp, \top}$. Then $reduce(\mathds{A}, X, \phi)\cong combineForget(G, x).$
\par \textbf{Lemma 13} Let $\mathds{A}$ be a $\Sigma$-structure that fully interprets $\Sigma$, $X \subset A$, and $\phi \in MSO(\Sigma)$. Then the result of $MC(\mathds{A}, \phi)$ returns that $\mathds{A} \vdash \phi$ if and only if convert(reduce($\mathds{A}, X, \phi$)) returns that $\mathds{A} \vdash \phi$. Here think of convert as the function provesRtoClosed, which will be explained later.
\par First, we prove that given a $\Sigma$-structure $\mathds{A}$, a $\Sigma$-formula $\phi \in MSO(\Sigma)$, and a tree decomposition \textbf{T} on $\mathds{A}$ and $\phi$, we can create a reduced game over the entire structure by putting together games over the structure restricted to bags of the tree decomposition T. In other words, we show how the only games we ever compute are games restricted to the bags $X_{i}$ of the tree decomposition.
\par Suppose node $i$ is a leaf. By definition of a leaf of a tree decomposition, this means that $A_{i}= \emptyset$ and $X_{i}= \emptyset$. Here, we simply return $reduce(\mathds{A}[ \emptyset ], \emptyset , \phi)$ since there are no lower nodes to combine with. So, the desired result is achieved.
\par Suppose node $i$ is a join node, structure $\mathds{A}[A_{l} \cup A_{r}]$ and formula $\phi$. Then by definition of a join node, there are two tree decompositions \textbf{$T_{l}$} and \textbf{$T_{l}$}, corresponding to the left and right children $i$.  \textbf{$T_{l}$} is over $\mathds{A}[A_{l}]$, $\phi$, where $A_{l}= \bigcup_{\text{i below l}} X_{i}$, and \textbf{$T_{l}$} is over $\mathds{A}[A_{r}]$, $\phi$, where $A_{r}= \bigcup_{\text{i below r}} X_{i}$. We want to show that $combine(reduce(A_{l}, X, \phi)$, $reduce(A_{r}, X, \phi))=reduce(A_{l}\cup A_{r}, X, \phi)$. Recall Lemma 11 defined above; we wish to apply this lemma to prove our proposition.
\par Let $X_{1}=X_{l}=X,$ $X_{2}=X_{r}=X,$ $\mathds{A}_{1}=\mathds{A}[A_{l}]$ and $\mathds{A}_{2}=\mathds{A}[A_{r}]$. The requirements of lemma 11 are that $\mathds{A} [A_{l}]$ and $\mathds{A}[A_{r}]$ are compatible, $X \subset A_{l}$, $X \subset A_{r}$, and that $X \cap X = A_{l} \cap A_{r}$.
\par First we show that $\mathds{A}[A_{l}]$ and $\mathds{A}[A_{r}]$ are compatible. Recall that two $\Sigma$-structures $\mathds{A}_{1}$ and $\mathds{A}_{2}$ are compatible if:
\begin{itemize}
\item For all constants $c_{i}$ such that $c^{\mathds{A}_{1}}_{i} \neq$ nil and $c^{\mathds{A}_{2}}_{i} \neq$ nil, then $c^{\mathds{A}_{1}}_{i} = c^{\mathds{A}_{2}}_{i} $
\item The identity function is an isomorphism between $\mathds{A}_{1}[A_{1} \cap A_{2}]$ and $\mathds{A}_{2}[A_{1} \cap A_{2}]$.
\end{itemize}
By definition of a restriction of a structure, $c^{\mathds{A}[{A}_{r}]}_{i}$ must equal  $c^{\mathds{A}[{A}_{l}}]_{i}$ if $c_{i} \in interpreted(\mathds{A}[{A}_{r}]) \cup interpreted(\mathds{A}[{A}_{l}])$. And again, by definition of a restriction of a structure, $\mathds{A}[{A}_{l}][{A}_{l}\cap A_{r}]=\mathds{A}[{A}_{l}\cap A_{r}]=\mathds{A}[{A}_{r}][{A}_{l}\cap A_{r}]$, so since $\mathds{A}[{A}_{l}][{A}_{l}\cap A_{r}]=\mathds{A}[{A}_{r}][{A}_{l}\cap A_{r}]$, the identity function is indeed an isomorphism between the two structures, since the structures are the same. So, we have the two structures are compatible.
\par Now we show that the rest of the conditions of Lemma 11 hold, namely that $X \subset A_{l}$, $X \subset A_{r}$, and that $X \cap X = A_{l} \cap A_{r}$.  Recall the definition of $A_{i}$ for a node $i$ : $A_{i} = \bigcup_{\text{j at or below i}}X_{j}$ for all bags $X_{j}$ for nodes $j$ equal to below $i$. So, by definition of  $A_{l}$ and  $A_{r}$, $X \subset A_{l}$ and $X \subset A_{r}$ since $X$ is the bag at nodes $l$ and $r$. We see that $X \cap X = A_{l} \cap A_{r} = X$. Firstly note that $X \subset X = A_{l} \cap A_{r} $ necessarily because the bag of a join node is defined to be $X=X_{r}=X_{l}$, so $X \subset A_{r}$ $X \subset A_{l}$ necessarily. To see the other containment, recall that by condition three of a tree decomposition, all bags that contain the same element must be connected. If there exists a $y \in A_{l} \cap A_{r}$, $y \notin X$, then this condition would not hold. If $y \in A_{l}$ and $y \in A_{r}$, there must exist some node $l'$ at or below $l$ and a node $r'$ at or below $r$ such that $y \in X_{l'}$ and $y\in X_{r'}$. Then by condition 3 of tree decompositions, there must be a path between these two nodes such that $y$ is contained in every bag of every node on that path. However, the only connection between $l'$ and $r'$ is through node that connects $r$ and $l$, which has bag $X$, so $y$ must be in $X$. Therefore,  $A_{l} \cap A_{r} = X$ as desired. With these qualifications in place, we can apply lemma 11 and get that $combine(reduce(A_{l}, X, \phi), reduce(A_{r}, X, \phi))=reduce(A_{l}\cup A_{r}, X, \phi).$
\par Suppose $i$ is an introduce node, over structure $\mathds{A}[A_{j}\cup {x}]$, (where $j$ is the node directly below $i$ and $x \notin A_{j}$) and formula $\phi$. Then by definition of an introduce node, we have a tree decomposition $T_{j}$ at node $j$ where the tree decomposition is over structure $\mathds{A}[A_{j}]$ and $\phi$. We want to show that $combine(reduce(\mathds{A}[A_{j}], X_{j}, \phi), reduce(\mathds{A}[X_{j} \cup {x}], (X_{j}\cup {x}), \phi))=reduce(A_{j}\cup {x}, X_{j}\cup{x}, \phi)$. We can use Lemma 11 again: we let $X_{1}=X_{j},$ $X_{2}=X_{j}\cup {x},$ $\mathds{A}_{1}=\mathds{A}[A_{j}]$ and $\mathds{A}_{2}=\mathds{A}[X_{j} \cup {x}]$. Again we require that $\mathds{A}[A_{j}]$ and $ \mathds{A}[X_{j} \cup {x}]$ are compatible, $X_{j} \subset A_{j}$, $X_{j}\cup {x} \subset X_{j} \cup {x}$, and that $X_{j} \cap (X_{j} \cup {x}) = A_{j} \cap (X_{j}\cup {x})$. The proof of compatibility for the two structures is exactly the same as the proof above, substituting the relevant subsets. For the rest of the requirements, note that again $X_{j}\in A_{j}$ by definition of $A_{j}$. $X_{j}\cup {x} \subset X_{j} \cup {x}$ since they are the same set. $X_{j} \cap (X_{j} \cup {x})= X_{j}$ since by assumption $x \notin X_{j}$, and $A_{j} \cap (X_{j}\cup {x}) = X$ as well since by definition $X_{j}\in A_{j}$, but $x \notin A_{j}$. Therefore $X_{j} \cap (X_{j} \cup {x}) =X_{j} A_{j} \cap (X_{j}\cup {x})$ as desired, so by Lemma 11 we have the desired result that $combine(reduce(\mathds{A}[A_{j}], X_{j}, \phi), reduce(\mathds{A}[X_{j} \cup {x}], (X_{j}\cup {x}), \phi))=reduce(A_{j}\cup {x}, X_{j}\cup{x}, \phi). $
\par Suppose $i$ is a forget node. Then by definition of a forget node, we have a tree decomposition $T_{j}$ at node $j$ directly below $i$ such that $A_{j}=A_{i}$ but $X_{j}=X_{i}\cup {x}$ for some $x \notin X$. $T_{j}$ is over structure $\mathds{A}[A_{j}]$ and $\phi$. We want to show that $combineForget(reduce(\mathds{A}[A_{i}], (X_{i}\cup {x}), \phi), x)=reduce(\mathds{A}[A_{i}], X_{i}, \phi)$. Then recall Lemma 12, which we will use for this proof. Let $\mathds{A}$=$\mathds{A}[A_{i}]$, $X= X_{i} \cup {x}$, and $x=x$. The lemma requires that We see that $ X_{i} \cup {x} \subset \mathds{A}[A_{i}]$, which is true by construction, and that $x \in X_{i}\cup {x}$, which is also true by construction. So, by Lemma 12, we have the desired result that $combineForget(reduce(\mathds{A}[A_{i}], (X_{i}\cup {x}), \phi), x)=reduce(\mathds{A}[A_{i}], X_{i}, \phi).$
\par Now, given that we have a proof that our method of building a reduced game from smaller pieces returns a game that is isomorphic to a reduced game made over the entire structure, we need to show that that reduced game gives the same final result as a brute-force model checking game, which as mentioned previously, is proven to return a winning strategy for the verifier if and only if the input MSO sentence holds on the given structure. But, note that this result is already given to us in Lemma 13: since by the precondition to our overall algorithm, the input structure $\mathds{A}$ fully interprets $\Sigma$, and by construction, $X\subset A$, all the conditions for Lemma 13 are satisfied. So the result of $MC(\mathds{A}, \phi)$ returns that $\mathds{A} \vdash \phi$ if and only if convert(reduce($\mathds{A}, X, \phi$)) returns that $\mathds{A} \vdash \phi$. Therefore, given a $\Sigma$-structure $\mathds{A}$ that fully interprets $\Sigma$, a $\Sigma$-formula $\phi \in MSO(\Sigma)$, and a tree decomposition \textbf{T} on $\mathds{A}$ and $\phi$, we can return a game that determines whether or not $\mathds{A}$ satisfies $\phi$.
\par This proof is fine and dandy, but does not mention the time bound of the algorithm, which is arguably the entire reason why Courcelle's Theorem is interesting. Unfortunately, proving the time bound is one of the parts of the Courcelle's Theorem that is left for the future of this project. However, we present an intuitive idea of the proof. Note that the brute force MC game algorithm takes as many steps as there are quantifiers or conjunctions in the MSO formula, and that it takes exponential time in the size of the input structure because you have to try every element in the input structure at every quantifier. However, note that the only place we ever do the brute force MC game on the structure is on games where the structure is restricted to the bag of a given node. But these bags, by definition of a tree decomposition, have size less than or equal to $t$ where $t$ is the treewidth of the input graph G. So, each time we do the brute force algorithm, even though the algorithm is exponential on the size of the input structure, it ends up being constant time because the time it takes is not related to the size of the overall input graph, only the treewidth. This is the main part of the proof--- you can create a simple algorithm to forget an element from a game by stepping through the game and taking it out at every position, which takes time linear in the size of the input graph (HELP); and a combine algorithm which \textcolor{red}{(HELP HELP HELP linear??) \textcolor{red}COMBINE AND FORGET ARE LINEAR BECAUSE...}

\section{What's Left}
\par Keeping the above proof of the algorithm in mind, we now go into the Agda code that was promised. The overarching proof is described by these three functions: algorithm, provesRtoclosed, and OpentoClosed. Picking up from towards the end of the mathematical proof, the idea here is that algorithm provably takes: a subset B, a bag X, a $\Sigma$-structure $\mathds{A}$, a $\Sigma$-formula $\phi$, a proof that B is decidable, proof that $B \subset A$, and finally tree decomposition TD on  $\mathds{A}$, X, and $\phi$, and returns either that
\begin{itemize}
\item the verifier has a winning strategy on EMC($\mathds{A}$, X, and $\phi$),
\item that the falsifier has a winnings strategy on EMC($\mathds{A}$, X, and $\phi$),
\item or a reduced undecided game reduced(A[B], X, $\phi$).
\end{itemize}
The idea of what the proof of this function will look like is that, like the proof above, it will case on the tree decomposition. It will use the functions combineJoin and combineIntro to take care of combining the recursive calls where the mathematical proof used Lemma 11, and it will use combineforget where the mathematical proof used Lemma 12. If algorithm returns an undecided reduced game, that game will be sent to provesRtoClosed, which is our interpretation of Lemma 13 from the proof above, and if the algorithm returns a decided EMC game (i.e. an open truth), that result will be sent to openToClosed which is our interpretation of another lemma from the paper.
\par We see quite clearly that openToClosed takes a structure and a formula, a "$\vdash o$", i.e. an EMC game on that pair, and then sends it to a "$\vdash c$", i.e. an MC game, on that pair. provesRtoClosed, similarly, takes reduced games to MC games, as lemma 13 does. The general idea of both of these proofs is essentially that if your structure is closed, you can simply take out the branches where constants where interpreted as nil to keep options open for future expansions, (since all possible options are already expressed), and see if the closed MC game left behind has a winning strategy for the verifer. But even more simlpy, if a game is still undecided even when the entire underlying set is available to the game, then the game is true if it is a universal game and false if it is an existential game. This is because the nil is kept as a sort of open space for more possible interpretations of constants, if more of the underlying set is to be merged in. If a universal game is undecided, it must be because the verifier has a winning strategy on all branches except those with nil, because if the falsifier had a winning stategy on even one subgame, the game  would have been terminated. However, if the nil doesn't really exist since all possible interpretations have been explored, this must mean that the formula does work for every possible interpretation and the universal formula is true on the structure. A dual argument works for existential formulas being false.
\begin{code}
 algorithm : ∀ {Σ} (B : Subset) (X : fixed1 B) (A : Structure Closed Σ) (φ : Formula Σ)
                   (decB : DecidableSub B)(BinA : Sub B (fst A))
                 → (TD : TreeDecomp {Σ = Σ} {A} (fst X) B)
                 → Either (Either (A ⊩o φ) (A ⊩o φ false)) (provesR (restriction A B decB BinA)  φ X)
\end{code}
\begin{code}
   {-EMC -> MC i.e. Lemma 11-}
  openToClosed : ∀ {Σ} → (A : Structure Closed Σ) (φ : Formula Σ) → (otruth : A ⊩o φ) → A ⊩c φ
   {-reducedEMC -> MC i.e. Lemma 13-}
  provesRtoClosed :  ∀ {Σ} → (A : Structure Closed Σ) (φ : Formula Σ) (X : fixed1 (fst A))
                       → (red : provesR A φ X ) → A ⊩c φ

\end{code}
\par Now that we have a grasp on the outer layer of the algorithm, we take a look at one layer down: what will go inside the cases of algorith, which cases on the constructors of the given tree decomposition. First, we need to trudge through some background code that is used throughout these lemmas. Recall that fixed and fixed1 are the types for bags in a tree decomposition, re-defined below. fixed is just a proof that for given subsets $A1$ and $A2$, there exists a subset X such that X is in each of $A1$ and $A2$ and X is decidable. Similarly, fixed1 says that given a subset A1, there exists a subset X such that $X \subset A_{1}$ and X is decidable. The first two postulates show that fixed A1 A2 implies fixed1 A1 and fixed1 A2. The third postulate asserts that if you have fixed A1 A2, then you must have fixed1 $A_{1} \cup A_{2}$. Then, the last postulate in the first bunch asserts that if X is a possible bag of a set A1 and $A1 \subset A2$ then X could be a bag of A2 as well. decSingleton states that a singleton set is always decidable. individSinSubset is essentially a dance around Agda's strict type system. It says that if an element x  in a given subset A, then the singleton set ${x}$ is a subset of A. The quick definitions are explained in the comments above the code; these lemmas are unimportant as they are just small, obvious proofs to aid the larger ones.
\begin{code}
  fixed : (A1 : Subset) (A2 : Subset) → Type
  fixed A1 A2 = Σ \ (X : Subset) → ((Sub X (A1)) × ( Sub X (A2))) × DecidableSub X

  fixed1 : (A1 : Subset) → Type
  fixed1 A1 = Σ \ (X : Subset) → (Sub X (A1)) × DecidableSub X

  postulate
  {-when you have a bag (fixed) that's in 2 subsets, it's in each one-}
    fixed2fixed1 : ∀ (A1 A2 : Subset) → fixed A1 A2 → fixed1 A1
    fixed2fixed2 : ∀ (A1 A2 : Subset) → fixed A1 A2 → fixed1 A2
    {- if you have a decidable subset that's in both A1 and A2, then it's in A1 union A2-}
    fixed2union : ∀ (A1 A2 : Subset) → fixed A1 A2 → fixed1 (union A1 A2)
    {-if you have X = fixed1 A for any set A, X =fixed1 A' for any superset A' of A-}
    fixed1Sub : ∀ {A1 A2 : Subset} → fixed1 A1 → Sub A1 A2 → fixed1 A2

  postulate
    {-A singleton set is always decidable-}
    decSingleton : ∀ {τ} → (x : Individ τ) → DecidableSub (singleton {τ = τ} x)
     {-if x is an IndividS A for some subset A, then it's in A!!-}
    individSinSubset : ∀ {τ} (A : Subset) → ( x : IndividS A τ) → Sub (singleton {τ = τ} (fst x)) A
\end{code}
\par As mentioned earlier,   we translate Lemma 11 into Agda with two functions, one to be used in the case that we are combining two subgames from the join node of a tree decomposition called combineJoin, and one to be used in the case that we are combining two game in an into node of a tree decomposition, called combineIntro. The code is below. See that combineJoin takes a structure $\mathds{A}$, two decidable subsets $B_{1}$ and  $B_{2}$ (where $\mathds{A}_{1}$ in the definition of the lemma is supposed to be represented by $\mathds{A}[B_{1}]$ and similar for $B_{2}$), a bag X (fixed B1 B2), and proofs that both $B1 \subset A$ and $B2 \subset A$, and two undecided reduced games, $reduced(\mathds{A}[B_{i}] \phi X)$ for $i ∈ {1, 2}.$ CombineJoin returns either a proof that the verifier has a winning strategy for $EMC(\mathds{A}[B_{1}], X, \phi)$, a proof that the falsifier has a winning strategy for that game, or that the game is reduced and undecided. Note that the result type is the same as that of the overarching algorithm, as required because algorithm returns the result of comineJoin. The proof of this function is in process, as with the rest outlined in this section.
\begin{code}
 combineJoin : ∀ {Σ} {oc} (B1 B2 : Subset) (A : Structure oc Σ)  (φ : Formula Σ)  → (decb1 : DecidableSub B1) (decb2 : DecidableSub B2) (X : fixed B1 B2)
                    (b1subAset : Sub B1 (fst A)) (b2subAset : Sub B2 (fst A)) →
                               (recurcall1 : (provesR (restriction A B1 decb1 b1subAset) φ (fixed2fixed1 B1 B2 X)))
                               (recurcall2 : (provesR (restriction A B2 decb2 b2subAset) φ (fixed2fixed2 B1 B2 X)))
                            → let B1∪B2 = (restriction A (union B1 B2) (unionDec {S1 = B1} {B2} decb1 decb2)
                                                               (subLUB b1subAset b2subAset))
                               in
                                Either (Either (B1∪B2 ⊩o φ)
                                               (B1∪B2 ⊩o φ false))
                                               (provesR B1∪B2 φ (fixed2union B1 B2 X))
\end{code}
combineIntro is quite similar to combineJoin. See that combineIntro takes a decidable subsets $B$; a structure $\mathds{A}$, a set element x of A, (where $\mathds{A}_{1}$ in the definition of the lemma is supposed to be represented by $\mathds{A}[B]$ and similar for $A_{2}$ and $[X \cup {x}]$), a proof that $x \notin B$,  a bag X (fixed B), a proof that $B \subset A$, and an undecided reduced game, $reduced(\mathds{A}[B], X, \phi )$, and a naive (i.e. brute force) algorithm of whether the structure restricted to the bag $X \cup {x}$ satisfies the formula. CombineIntro returns either a proof that the verifier has a winning strategy for $EMC(\mathds{A}[B \cup {X}], X\cup {x}, \phi)$, a proof that the falsifier has a winning strategy for that game, or that the game is reduced and undecided. Note that the result type is again the same as that of the overarching algorithm, as required because algorithm returns the result of comineIntro.
\begin{code}
combineIntro : ∀ {Σ} {τ} (B : Subset) (A : Structure Closed Σ) (φ : Formula Σ) (x : IndividS (fst A) τ)
                                        (xnew : (Sub (singleton {τ = τ} (fst x)) (complement B)))
                                        (decb : DecidableSub B) (bsubAset : Sub B (fst A)) (X : fixed1 B) →
                                        (recurcall : provesR (restriction A B decb bsubAset) φ X) →
                                        (nai : provesR (restriction A (union (fst X) (singleton {τ = τ} (fst x)))
                                                                      (unionDec {S1 = (fst X)} {singleton (fst x)} (snd (snd X)) (decSingleton (fst x)))
                                                                      (subLUB (subtrans (fst (snd X)) bsubAset) (individSinSubset (fst A) x)))
                                                       φ ((fst X) , (subINL , (snd (snd X)))))
                       → let B∪x = (restriction A (union B (singleton {τ = τ} (fst x)))
                                                      (unionDec {S1 = B} {singleton (fst x)} decb (decSingleton (fst x)))
                                                       (subLUB bsubAset (individSinSubset (fst A) x)))
                         in
                           Either (Either (B∪x ⊩o φ)
                                          (B∪x ⊩o φ false))
                                          (provesR B∪x φ ((fst X) , ((subtrans (fst (snd X)) subINL) , (snd (snd X)))))
\end{code}
\par Now we have combineForget, which corresponds to Lemma 12 in the paper and is used in the case where the tree decomposition in the function "algorithm". combineForget takes a decidable subsets $B$; a structure $\mathds{A}$, a $\Sigma$-formula $\phi$, a bag X (fixed B), a set element x of A, a proof that $x \notin X$, and a reduced undecided game $reduced(A[B], X \cup {x}, \phi)$, (which is supposed to represent the result of a recursive call to algorithm for a node below the current node of the tree decomposition). combineForget only returns a reduced undecided game $reduced(A[B], X, \phi)$, because Lemma 12 states that the game needs to be undecided for the lemma to hold.
\begin{code}
 combineForget : ∀ {Σ} {τ} (B : Subset) (A : Structure Closed Σ)  (φ : Formula Σ) (X : fixed1 B)
                            (x : IndividS (fst X) τ) (decB : DecidableSub B) (bsubAset : Sub B (fst A))
                            (xgone : (Sub (singleton {τ = τ} (fst x))) (complement (fst X))) →
                            (recurcall :   (provesR (restriction A B decB bsubAset) φ (X)))
                          → (provesR (restriction A B decB bsubAset) φ X )
\end{code}
\par As noted in the mathematical proof, there is no need for a combine algorithm for the base case, because we simply call naive, the brute force algorithm of determining if a formula holds on a  structure. (For those who are familiar with the Kneiss et al paper, this is our eval.) The type of naive is included below: see that takes a formula $\phi$ , a structure $\mathds{A}$, a bag X, and returns whether the fasifier or the verifier has a winning strategy on  EMC( $\mathds{A}, X, \phi)$, or if the game is undecided. Unlike the combine algorithms, there is no fancy footing here: this algorithm is exponential time, but as outlined above, it only is used on sets of constant size.
\begin{code}
naive : ∀ {Σ'} {oc} → (φ : Formula Σ') (A : Structure oc Σ') → (X : fixed1 (fst A))
                           → Either (Either (A ⊩o φ) (A ⊩o φ false)) (provesR A φ X)
\end{code}
\par After the proof of the overall algorithm is finished, we plan to formalize in Agda how the algorithm outlined meets the FPT criteria for Courcelle's Theorem. After we verify the time bound, then we will move on to verifying some applications of this theorem--some proimising directions seem to be in phylogenetics and other graph algorithms, especially those having to do with graph minor theory as explained in the related work section.
\section{Conclusion}
\par We are well en-route to completing a verification in Agda of Courcelle's Theorem, a general graph algorithm stating that questions definable in Monadic Second Order Logic can be decided in fixed-parameter tractable time on graphs of bounded treewidth. We have encoded all of the necessary definitions for this project, namely symbols (SigThing), signatures (Signature), structures (Structure), restrictions of structures (restriction), isomorphisms between structures (preserves, iso) set elements (Individ and IndividS), sets (Subset), tree decompositions (TreeDecomp), model checking games ($\vdash$c), extended model checking games ($\vdash$o), position equivalence and game equivalence (positionEquiv and gameEquiv), and finally, educed games (isRed, $\vdash$s, provesR). We are in the process of constructing the naive, or brute force algorithm (naive), which will run only on leaves of the tree decomposition and restrictions of the input structure of bags of the tree decomposition. We have defined the types for all of the lemmas required to prove the algorithm overall (algorithm, provesRtoClosed, openToClosed combineIntro, combineJoin, combineForget), and the proofs of these types is in progress as well. Once this is completed, we hope to prove the time bound of the algorithm, and then verify its use in the graph minor decomposition paper by Reed et. al.
\par This work could become useful if Courcelle's Theorem becomes more useful in the field of relational databases[cite???], as the fact that it is verified could provide a sense of security to manipulating sensitive data more quickly. It could also allow Bruno Courcelle to take a quick sigh of relief, since Agda agrees that his proof is correct.
% End {{{
\bibliographystyle{plain}
\bibliography{paper}
\printindex
\backmatter
\end{document}
% }}}
