
\section{Introduction}\label{sec:intro}

This paper takes a better approach to the problem with datatype-generic
programming (DGP). It applies well-known DGP techniques to represent modular
datatypes, to build functions from functor algebras with folds and to compose
proofs from proof algebras by means of induction. Moreover, for certain
functionality and proofs our approach can achieve more reuse than MTC: instead
of composing modular components we provide a single generic definition once and
for all.

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
