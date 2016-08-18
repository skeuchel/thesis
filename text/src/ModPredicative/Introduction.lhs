
\section{Introduction}\label{sec:intro}

%% The recent work on \emph{Meta-Theory \`a la Carte} (MTC) \cite{mtc} is the first
%% to improve this situation. It is a Coq framework for defining and reasoning
%% about extensible modular datatypes and extensible modular functions thereby
%% gaining modular component reuse. MTC builds on Datatypes \`a la Carte (DTC)
%% \cite{dtc}, a Haskell solution to the expression problem, to achieve modularity.

%% Besides writing modular algebras for expressing semantic functions as folds, MTC
%% also supports writing generally recursive functions using mixins and bounded
%% fixed points.  On top of that MTC presents techniques for modularly composing
%% proofs by induction for structurally recursive functions and step-bounded
%% induction for generally recursive functions.

The transition from the Haskell setting of DTC to a proof-assistant like Coq
comes with two major hurdles. DTC relies on a general fixed point combinator to
define fixed points for arbitrary functors and uses a generic fold operation
that is not structurally recursive. To keep logical consistency, Coq applies
conservative restrictions and rejects both: a) DTC's type level fixed-points
because it cannot see that the definition is always strictly-positive, and b)
DTC's fold operator because it cannot determine termination automatically.

MTC solves both problems by using extensible Church-encodings. However, MTC's
use of extensible Church-encodings is unsatisfactory and this solution leaves
much to be desired.

\begin{enumerate}
\item
  By using Church-encodings MTC is forced to rely on an impredicative sort and
  uses Coq's impredicative-set option, which is known to be inconsistent with
  some standard axioms of classical mathematics.

  %% This option is known to lead to logical inconsistency, and thus
  %% undermines all formal results obtained in MTC.

\item
  The fixpoint combinator provided by Church-encodings admits too many
  functors. For inductive reasoning, only strictly-positive functors are valid,
  i.e, those functors whose fixpoints are inductive datatypes. Yet,
  Church-encodings do not rule out other functors.  Hence, in order to reason
  only about inductive values, MTC requires a witness of inductivity: the
  universal property of folds. Since every value comes with its own
  implementation of the fold operator, MTC needs to keep track of a different
  such witness for every value. It does so by decorating the value with its
  witness.

  This decoration obviously impairs the readability of the code. Moreover, since
  proofs are opaque in Coq, it also causes problems for equality of terms.
  Finally, the decoration makes it unclear whether MTC adequately encodes
  fixpoints.

\item
  Church-encodings do not support proper induction principles. MTC relies on a
  \emph{poor-man's induction principle} instead and requires the user to provide
  additional well-formedness proofs.  Even though these can be automated with
  proof tactics, they nevertheless complicate the use of the framework.

\end{enumerate}


We take a better approach to the problem by applying well-known datatype-generic
programming (DGP) techniques to represent modular datatypes, to build functions
from functor algebras with generic folds and to compose proofs from proof
algebras by means of generic induction. Moreover, for certain functionality and
proofs our approach can achieve more reuse than MTC: instead of composing
modular components we provide a single generic definition once and for all.

\paragraph{Outline}

In our approach to modular reasoning we take a top down approach. We first
present the user-facing programming in Section
\ref{sec:mod:strictlypositivefunctors} based on type classes for
strictly-positive functors with associated fixpoints.  We also discuss our
approach to modularized reasoning and in particular our notion of \emph{proof
  algebras} which is different from MTC's proof algebras and closer to standard
structural inductive reasoning.

Our type class for strictly-positive functors cannot be modularized. We
therefore present the universe of container types in Section
\ref{sec:mod:containers} which is modular and which admits datatype-generic
generic definitions of folds and induction that we use to generically
instantiate our interface. The universe of containers is very large and admits
only a small number of generic functions. As a complement, we discuss the
universe of polynomial functors in Section \ref{sec:mod:polynomial}, which
admits more generic functions like generic equality, and show how to embed it in
the universe of containers. We compare our approach direclty with MTC in Section
\ref{sec:mod:casestudy} using a port of MTC's case study. In section
\ref{sec:modp:related} we discuss related work before concluding in Section
\ref{sec:modp:conclusion}.




%if False

% Building fixpoints for classes of functors. We show that it is useful in our
% setting for building modular datatypes, functions and proofs.

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

%endif



%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
