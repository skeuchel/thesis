%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt

This chapter briefly describes our two implementations of \Knot. The first is a
generic implementation that acts as a constructive proof of the boilerplate's
existence for all well-formed specifications. The second, called \Needle, is a
code generator that is better suited to practical mechanization.

%-------------------------------------------------------------------------------
\section{The Generic \Knot\ Implementation}\label{sec:elab:impl:generic}
We implemented the boilerplate functions generically for all well-formed \Knot
specifications in about 4.3k lines of Coq by employing datatype-generic programming techniques
\cite{genericprogramming}. Following our free monad principle, we capture de Bruijn terms in a
free monadic structure that is parameterized by namespaces and whose underlying
functor covers the regular constructors of sorts. To model the underlying
functors, we use the universe of finitary containers
\cite{containers,dependentpolynomialfunctors,lawoftraversals,shapelyfunctors}
Finitary containers closely model our specification language: a set of shapes
(constructors) with a finite number of fields. We use an indexed
\cite{indexedcontainers} version to model mutually recursive types and use a
higher-order presentation to obtain better induction principles for which we
assume functional extensionality \footnote{However, the code based on our
  generator \Needle does not assume any axioms.}. We implemented boilerplate
operations and lemmas for this universe generically.


%-------------------------------------------------------------------------------
\section{The \Needle\ Code Generator}\label{sec:elab:impl:codegen}

While the generic Coq definitions presented in the previous sections are
satisfactory from a theoretical point of view, they are less so from a pragmatic
perspective. The reason is that the generic code only covers the variable binder
boilerplate; the rest of a language's formalization still needs to be developed
manually. Developing the latter part directly on the generic form is
cumbersome. Working with conversion functions is possible but often reveals too
much of the underlying generic representation. As observed by Lee et
al. \cite{gmeta}, this happens in particular when working with generic
predicates.

For this reason, we also implemented a code generation tool, called \Needle
that generates all the boilerplate in a language-specific non-generic
form. \Needle~takes a \Knot~specification and generates Coq code: the
inductive definitions of a de Bruijn representation of the object language and
the corresponding specialized boilerplate definitions, lemmas and proofs. Both
proof terms and proof scripts are generated. \Needle is implemented in about
11k lines of Haskell.


%if False
The \Needle~tool generates inductive definitions for each sort in the
\Knot~specification. Furthermore, it analyzes mutually recursive groups of
sorts, creates mutually recursive definitions for the groups and derives
corresponding induction schemes, so that lemmas can be proven by mutual
induction. It also analyzes groups of mutually recursive functions. Functions
can be defined on a subset of a mutually recursive group of sorts and there can
be multiple functions per sort.

\paragraph{Function Boilerplate}
The effect of shifting on de Bruijn indices is generically defined in
the companion library. \Needle\ generates a function that traverses
a term to its variable positions and updates the cutoff whenever
recursing into a field with a binding specification.

The variable case of the substitution operator is also generically
implemented in the library. It is parameterized over the term datatype
$T$ for the sort that is substituted, the variable constructor |var :
T → T| and the shift operation |shift : nat → T → T|.


\paragraph{Proof Boilerplate}
To reduce the implementation effort, \Needle\ generates proof scripts
rather than proof terms for boilerplate lemmas. These scripts
are backed by dedicated tactics in the companion library
that capture our knowledge of how such proofs proceed.

We have pushed the generic boilerplate for the variable case of lemmas into
the library in the same manner as we did for syntax operations. The
library contains a proof of the shift commutation lemma for
indices. The full proof of commutation for shifts on terms
$$|∀ c, shift (1 + c) ∘ shift 0 = shift 0 ∘ shift c|$$
is merely a congruence proof that can be proven by straightforward
induction.

The library also contains two modules for generic proofs for the
variable case of the commutation lemmas. The first one covers
commutations between a shift and a substitution and is parameterized
over three properties
\begin{enumerate}
\item The effect of shift on variables
     $$|∀ c, shift c ∘ var = var ∘ shiftN c|.$$
\item The commutation lemma for |shift|.
\item The effect of subst on variables
     $$|∀ x t, subst x t ∘ var = substN x t|.$$
\end{enumerate}

Using the first module the code generator will derive the commutation
lemmas for terms which are additional inputs to the second module that
derives the variable case of the commutation lemma for two
substitutions.

%%   Parameter subst_shift_comm :
%%     forall x t t',
%%       subst (S x) t (shift 0 t') =
%%       shift 0 (subst x t t').
%%   Parameter subst_shift_reflection :
%%     forall x t t',
%%       subst x t (shift x t') = t'.
%endif


%-------------------------------------------------------------------------------
\paragraph{Soundness}

We have not formally established that \Needle~always generates type-correct
code or that the proof scripts always succeed. Nevertheless, a number of
important implementation choices bolster the confidence in \Needle's
correctness:
%
First, the generic-programming based implementation is evidence for the
existence of type-sound boilerplate definitions and proofs for for every
language specified with \Knot.

Secondly, the generic implementation contains a small proof-term DSL featuring
only the basic properties of equality such as symmetry, reflexivity,
transitivity and congruence and additionally stability and associativity lemmas
as axioms. The induction steps of proofs on the structure of terms or on the
structure of well-scopedness relation on terms in the generic implementation
elaborate to this DSL first and then adhere to its soundness
lemma. Subsequently, we ported the proof term elaboration to \Needle. Hence,
we have formally established the correctness of elaboration functions but not
their Haskell implementations.

Thirdly, lemmas for which we generate proof scripts follow the structure of the
generic proofs. In particular, this includes all induction proofs on natural
number- or list-like data because these are less fragile than induction proofs
on terms. A companion library contains tactics specialized for each kind of
lemma that performs the same proof steps as the generic proof.

Finally and more pragmatically, we have implemented a test suite of
\Knot~specifications for \Needle~that contains a number of languages with
advanced binding constructs including languages with mutually recursive and
heterogeneous binders, recursive scoping and dependently-typed languages with
interdependent namespaces for which correct code is generated.


Nevertheless, the above does not rule out trivial points of failure like name
clashes between definitions in the code and the Coq standard library or software
bugs in the code generator. Fortunately, when the generated code is loaded in
Coq, Coq still performs a type soundness check to catch any issues. In short,
soundness never has to be taken at face value.


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% End:
