%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt

This chapter briefly describes our two implementations of \Knot. The first is a
generic implementation that acts as a constructive proof of the boilerplate's
existence for all well-formed specifications. The second, called \Needle, is a
code generator that is better suited to practical mechanization.

%-------------------------------------------------------------------------------
\section{The \Loom\ Generic Library}\label{sec:elab:impl:generic}

We implemented the datatype-generic library \Loom around \Knot specifications
that provides boilerplate functionality. \Loom is only built for the development
of elaborations without end users in mind. Hence direct usability is not a
concern. The universe of the library covers generic representations of sorts,
environments and expressions, since these determine all of the interesting
elaborations. The universe does not deal with user-defined relations and their
derivation trees.

Following our free monad principle, we capture de Bruijn terms in a free monadic
structure similar to the one in Section \ref{ssec:knotdesign:freemonad}. We use
the universe of finitary containers
\cite{categoriesofcontainers,dependentpolynomialfunctors,lawoftraversals,shapelyfunctors}
to model the underlying pattern functors of regular constructors of sorts, in
order to deal with any positivity and termination requirements. Finitary
containers closely model our specification language: a set of shapes
(constructors) with a finite number of fields. Each field is associated with a
binding specification, all constraints for the well-formedness of specifications
and the well-scopedness of meta-variables are encoded in the universe codes
using strong intrinsic types \cite{stronglyttypedterm}. Furthermore, we use an
indexed \cite{indexedcontainers} version of finitary containers to model
mutually recursive types and use a higher-order presentation to obtain better
induction principles for which we assume functional
extensionality \footnote{However, the code based on our generator \Needle does
  not assume any axioms.}.

The boilerplate lemmas implemented in the library follow the elaboration
methodology outlined in this chapter. In total, the library consists of about
4.3k lines of Coq code.



%-------------------------------------------------------------------------------
\section{The \Needle\ Code Generator}\label{sec:elab:impl:codegen}

\begin{itemize}
\item \Needle is a Code generator written in Haskell that produces \Coq code
  from a \Knot specification.

\item It produces both, proof terms and invocations of proof script that
  are implemeneted in an accompanying library.

\item

\item It performs both simplifications of de Bruijn terms and of proof
  witnesses.
\item Simplification of terms is partial evaluation of functions.
\item For instance, the elaboration never takes any shortcuts in case of empty
  binding specifications. As a result, the intermediate terms may lift a
  terms with 0 newly introduced variables or extend a domain with 0 variables.
  Partial evaluation of the intermediate representation removes these
  unnecessary calls.

\item The other simplification is removing function calls based on
  subordination. This removes unnecessary calls to which are effectively are the
  identity function such as performing a term substitution in a type in
  \fexistsprod.

\item Proof terms can be every large. For example, the elaboration of the shift
  commutation proof term is duplicated for each field. In the case of an empty
  binding specification the induction hypothesis has already the correct shape
  and can be invoked directly without the rewriting steps before and after.

\item This is handled by a witness simplifier.
\item On of the simplification steps is partial evaluation of lemmas. For instance,
  the shift commutation proof contains two invocations for the associtivity of
  domain addition. For an empty binding specification the resulting associativity
  \[ (h_1 + h_2) + 0 = h_1 + (h_2 + 0)
  \]
  Since both sides are already definitionally equal, the equality can be
  alternatively be witnessed by |refl|, which is also the implementation of the
  associativity lemma for this base case.
\item The second simplification is using the group structure of equality proofs
  where transitivity is the group operation, reflexivity the neutral element and
  symmetry the inversion.

\end{itemize}

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
