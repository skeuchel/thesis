%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt

%% This chapter briefly describes our two implementations of \Knot. The first is a
%% generic implementation that acts as a constructive proof of the boilerplate's
%% existence for all well-formed specifications. The second, called \Needle, is a
%% code generator that is better suited to practical mechanization.

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

\Needle is a Code generator written in about 11k lines of Haskell. \Needle~takes
a \Knot~specification and generates Coq code for the representation of the
syntactic sorts of an object language and its semantic relations. Furthermore,
it generates specialized language-specific non-generic boilerplate definitions,
lemmas and proofs.

\begin{figure}[t]
  \centering
  \begin{minipage}{0.96\columnwidth}
    \includegraphics[width=\columnwidth]{src/GenBinding/Elaboration/NeedlePipeline.pdf}
  \end{minipage}
  \caption{Needle Processing Stages}
  \label{fig:elab:needle:stages}
\end{figure}

\Needle processes \Knot specifications in multiple stages which is pictured in
Figure \ref{fig:elab:needle:stages}.

The first stage is the parsing and checking of a textual \Knot specification,
name-resolution, sort checking, scope inference and scope checking, and grouping
of mutually recursive sorts and functions. The result is a \KnotCore
specification that is enriched with the inferred information such as the scope
of binding meta-variables. Furthermore, information is also cached in different
parts of the specification for easy access. For instance, each symbolic
sub-expression is annotated with its scope.

The elaboration to \Coq code is performed both, directly from \KnotCore and via
the intermediate representation \DbCore. \DbCore consists of a generic
representation of symbolic de Bruijn terms and the domain-specific witness
languages from this chapter. \Needle first generates generic version of
boilerplate in \DbCore, for example, of lemma statements. The specialization to
the given concrete specification is then carried out by a simplifier in \DbCore.
The simplification steps mainly consist of applying sub-ordination information
and partially evaluating the symbolic terms.

The elaborated proof terms tend to be very large. For almost all cases simpler
specialized proofs exists. For example, in the case of empty binding
specifications some proof steps are entirely unnecessary, however, they are
still part of the elaboration. To speed up the checking of the generated code
\DbCore's simplifier also performs simplification of the domain-specific witness
terms. For that, it uses the group structure of equality
proofs~\cite{stump2005algebra} with transitivity as the group operation,
reflexivity as the neutral element and symmetry as the inversion. Furthermore,
the simplifier performs partial evaluation of lemmas that have been added as
axioms to the witness languages, e.g. \textsc{EqhAssocPlus} in Figure
\ref{fig:elab:equalitywitness:domain:interpretation}\footnote{In contrast to the
  witness languages presented in this chapter, \DbCore's representation contains
  symbolic terms that exactly describe the left and right hand sides of the
  witnessed equality. This extra information is needed for the partial
  evaluation.} The correctness of the proof simplification has also been
verified in \Loom.

The \Coq code produced by \Needle contains both, elaboration proof terms and
invocations of proof scripts that are implemented in an accompanying library. To
reduce the development effort, lemmas that do not directly depend on the
structure of user-defined sorts and relations are primarily implemented via
proof scripts, since for this kind of lemmas, proof scripts are sufficiently
robust. These include lemmas about domains, indices and contexts, but also the
variable cases of interaction lemmas which are always proven separately. Lemmas
that induct over sorts or relations directly depend on the user-defined
structure and are therefore more brittle. These are always implemented via by
proof term elaboration.


%% %-------------------------------------------------------------------------------
%% \paragraph{Soundness}

%% We have not formally established that \Needle~always generates type-correct
%% code or that the proof scripts always succeed. Nevertheless, a number of
%% important implementation choices bolster the confidence in \Needle's
%% correctness:
%% %
%% First, the generic-programming based implementation is evidence for the
%% existence of type-sound boilerplate definitions and proofs for for every
%% language specified with \Knot.

%% Secondly, the generic implementation contains a small proof-term DSL featuring
%% only the basic properties of equality such as symmetry, reflexivity,
%% transitivity and congruence and additionally stability and associativity lemmas
%% as axioms. The induction steps of proofs on the structure of terms or on the
%% structure of well-scopedness relation on terms in the generic implementation
%% elaborate to this DSL first and then adhere to its soundness
%% lemma. Subsequently, we ported the proof term elaboration to \Needle. Hence,
%% we have formally established the correctness of elaboration functions but not
%% their Haskell implementations.

%% Thirdly, lemmas for which we generate proof scripts follow the structure of the
%% generic proofs. In particular, this includes all induction proofs on natural
%% number- or list-like data because these are less fragile than induction proofs
%% on terms. A companion library contains tactics specialized for each kind of
%% lemma that performs the same proof steps as the generic proof.

%% Finally and more pragmatically, we have implemented a test suite of
%% \Knot~specifications for \Needle~that contains a number of languages with
%% advanced binding constructs including languages with mutually recursive and
%% heterogeneous binders, recursive scoping and dependently-typed languages with
%% interdependent namespaces for which correct code is generated.

%% Nevertheless, the above does not rule out trivial points of failure like name
%% clashes between definitions in the code and the Coq standard library or software
%% bugs in the code generator. Fortunately, when the generated code is loaded in
%% Coq, Coq still performs a type soundness check to catch any issues. In short,
%% soundness never has to be taken at face value.


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% End:
