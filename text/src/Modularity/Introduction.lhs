%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt

%if False

> {-# LANGUAGE RankNTypes, TypeOperators, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances #-}
>
> module Introduction where

%endif

\section{Introduction}\label{sec:intro}

Meta-theory of programming languages is a core topic of computer
science that concerns itself with the formalization of propositions
about programming languages, their semantics and related systems like type
systems. Mechanizing formal meta-theory in proof assistants is crucial,
both for the increased confidence in complex designs and as a basis for
technologies such as proof-carrying code.

The \textsc{PoplMark} challenge \cite{poplmark} identified
% \emph{variable binding}, \emph{complex inductions},
% \emph{experimentation} and
\emph{component reuse} as one of several key issues of
formal mechanization of programming language meta-theory. Reuse is
crucial because formalizations have high costs. Unfortunately the
current practice to achieve reuse is to copy an existing formalization
and to change the existing definitions manually to integrate new
features and to subsequently \emph{patch up the proofs} to cater for
the changes.

The recent work on \emph{Meta-Theory \`a la Carte} (MTC) \cite{mtc} is
the first to improve this situation. It is a Coq framework for
defining and reasoning about extensible modular datatypes and
extensible modular functions thereby gaining modular component
reuse. MTC builds on Datatypes \`a la Carte (DTC) \cite{dtc}, a
Haskell solution to the expression problem, to achieve
modularity. Besides writing modular algebras for expressing semantic
functions as folds, MTC also supports writing generally recursive
functions using mixins and bounded fixed points.  On top of that
MTC presents techniques for modularly composing proofs by induction
for structurally recursive functions and step-bounded induction for
generally recursive functions.

The transition from the Haskell setting of DTC to a proof-assistant like Coq
comes with two major hurdles. DTC relies on a general fixed point combinator to
define fixed points for arbitrary functors and uses a generic fold operation
that is not structurally recursive. To keep logical consistency, Coq applies
conservative restrictions and rejects both: a) DTC's type level fixed-points
because it cannot see that the definition is always strictly-positive, and b)
DTC's fold operator because it cannot determine termination automatically.

MTC solves both problems by using extensible Church-encodings
instead. Yet, this solution leaves much to be desired.
\begin{enumerate}
\item
By using Church-encodings MTC is forced to rely on Coq's impredicative-set
option, which is known to be inconsistent with some standard axioms
of classical mathematics.  % This option is known to lead to logical inconsistency, and thus
% undermines all formal results obtained in MTC.
% \steven{Is it already inconsistent with
% impredicativity or do we need another ingredient as well?}
\item
The fixpoint combinator provided by Church-encodings admits too
many functors. For inductive reasoning, only strictly-positive functors are
valid, i.e, those functors whose fixpoints are inductive datatypes. Yet,
Church-encodings do not rule out other functors.  Hence, in order to reason
only about inductive values, MTC requires a witness of inductivity: the
universal property of folds. Since every value comes with its own
implementation of the fold operator, MTC needs to keep track of a different
such witness for every value. It does so by decorating the value with its
witness.

This decoration obviously impairs the readability of the code. Moreover, since
proofs are opaque in Coq, it also causes problems for equality of terms.
Finally, the decoration makes it unclear whether MTC adequately encodes fixpoints.
\item
Church-encodings do not support
proper induction principles. MTC relies on a
\emph{poor-man's induction principle} instead and requires the user to
provide additional well-formedness proofs.
Even though these can be automated with proof tactics, they nevertheless
complicate the use of the framework.
\end{enumerate}

This paper applies well-known techniques from \emph{datatype-generic
programming} (DGP) to overcome all of the above problems. For this purpose, it
extends Schwaab and Siek's Agda-based approach~\cite{schwaab:mtp} to encompass
all of MTC's features in Coq.

% Building fixpoints for classes of functors. We
% show that it is useful in our setting for building
% modular datatypes, functions and proofs.

Our specific contributions are:
\begin{itemize}

\item
We show how to solve the expression problem in the restricted setting of Coq. We
build modular datatypes, modular functions and modular proofs from well-studied
DGP representations of fixpoints for different classes of functors.

In particular, we consider polynomial functors like Schwaab and Siek, but also
the more expressive container types which are useful for modelling MTC's lambda
binders that are based on (parametric) higher-order abstract syntax.

\item
Our approach avoids impredicativity in Coq and adequately encodes fixpoints.  It
achieves these properties by exploiting DGP approaches that capture only
strictly-positive functors.

\item
We show how to obtain more reuse than MTC by
complementing modular definitions with generic definitions.

\item
We show how to apply MTC's automatic construction of fixpoints for
datatypes, relations and proofs to the DGP setting
and thus improve over Schwaab and Siek's manual fixpoint construction.

\end{itemize}

\paragraph{Code and Notational Conventions}

While all the code underlying this paper has been developed in Coq,
the paper adopts a terser syntax for its many code fragments.  For the
computational parts, this syntax exactly coincides with Haskell
syntax, while it is an extrapolation of Haskell syntax style for
propositions and proof concepts. The Coq code is available at
\url{https://github.ugent.be/skeuchel/gdtc}.



