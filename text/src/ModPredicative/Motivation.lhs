\section{Motivation}\label{sec:modpred:motivation}

The MTC framework uses Church encodings to represent modular datatypes, but
Church encodings have multiple drawbacks when it comes to reasoning:

%% The recent work on \emph{Meta-Theory \`a la Carte} (MTC) \cite{mtc} is the
%% first to improve this situation. It is a Coq framework for defining and
%% reasoning about extensible modular datatypes and extensible modular functions
%% thereby gaining modular component reuse. MTC builds on Datatypes \`a la Carte
%% (DTC) \cite{dtc}, a Haskell solution to the expression problem, to achieve
%% modularity.

%% Besides writing modular algebras for expressing semantic functions as folds,
%% MTC also supports writing generally recursive functions using mixins and
%% bounded fixed points.  On top of that MTC presents techniques for modularly
%% composing proofs by induction for structurally recursive functions and
%% step-bounded induction for generally recursive functions.

\begin{enumerate}
\item
  Church encodings are inherently impredicative and thus MTC is forced to rely
  on an impredicative sort and uses Coq's \texttt{impredicative-set}
  option. However, this option is inconsistent with standard axioms of classical
  logic like the law of excluded middle or double negation elimination. This
  also restricts the approach to systems that allow impredicative encodings and
  hence rules out systems that are fully predicative like Agda.

\item
  The fixed-point combinator provided by Church encodings admits too many
  functors. For inductive reasoning, only strictly-positive functors are valid,
  i.e, those functors whose fixed-points are inductive datatypes. Yet, Church
  encodings do not rule out other functors.  Hence, in order to reason only
  about inductive values, MTC requires a witness of inductivity: the universal
  property of folds. Since every value comes with its own implementation of the
  fold operator, MTC needs to keep track of a different such witness for every
  value. It does so by decorating the value with its witness with the help of a
  $\Sigma$-type.

  As a result of this decoration, the user is confronted with a mix of decorated
  and un-decorated values. This obviously impairs the readability of the code,
  but it also creates confusion which variant is the proper one to use when
  stating propositions. Moreover, since proofs are opaque in Coq, it also causes
  problems for equality of terms.  Finally, the decoration makes it unclear
  whether MTC adequately encodes fixed-points.

\item
  B\"ohm and Berarducci isomorphism of strictly-positive datatypes and their
  Church encodings in System~F \cite{bohm85automatic} is a meta-theoretic
  result. In fact, currently it is impossible to prove induction principles for
  Church encodings in Coq.

  MTC relies on a \emph{poor-man's induction principle} instead and requires the
  user to provide additional well-formedness proofs. Even though these can be
  automated with proof tactics, they nevertheless complicate the use of the
  framework.

\end{enumerate}

We take a better approach to the problem by applying well-known datatype-generic
programming (DGP) techniques to represent modular datatypes, to build functions
from functor algebras with generic folds and to compose proofs from proof
algebras by means of generic induction. This overcomes the above shortcomings:

\begin{enumerate}
\item
  It does not assume \texttt{impredicative-set} or any axioms.

\item
  A witness of inductivity is always associated with the type, i.e. a type-class
  instance that holds the universe code for a functor, and not with values.

\item
  The generic induction principle is a proper one that does not rely on any
  additional well-formedness conditions. Moreover, for certain functionality and
  proofs, our approach can achieve more reuse than MTC: instead of composing
  modular components we provide a single generic definition once and for all.
\end{enumerate}



%% \paragraph{Outline}
%% In our approach to modular reasoning we take a top down approach. We first
%% present the user-facing programming in Section
%% \ref{sec:mod:strictlypositivefunctors} based on type classes for
%% strictly-positive functors with associated fixed-points.  We also discuss our
%% approach to modularized reasoning and in particular our notion of \emph{proof
%%   algebras} which is different from MTC's proof algebras and closer to standard
%% structural inductive reasoning.
%%
%% Our type class for strictly-positive functors cannot be modularized. We
%% therefore present the universe of container types in Section
%% \ref{sec:mod:containers} which is modular and which admits datatype-generic
%% generic definitions of folds and induction that we use to generically
%% instantiate our interface. The universe of containers is very large and admits
%% only a small number of generic functions. As a complement, we discuss the
%% universe of polynomial functors in Section \ref{sec:mod:polynomial}, which
%% admits more generic functions like generic equality, and show how to embed it in
%% the universe of containers. We compare our approach direclty with MTC in Section
%% \ref{sec:mod:casestudy} using a port of MTC's case study. In section
%% \ref{sec:modp:related} we discuss related work before concluding in Section
%% \ref{sec:modp:conclusion}.
%%
%%
%% %if False
%%
%% % Building fixed-points for classes of functors. We show that it is useful in our
%% % setting for building modular datatypes, functions and proofs.
%%
%% Our specific contributions are:
%% \begin{itemize}
%%
%% \item
%% We show how to solve the expression problem in the restricted setting of Coq. We
%% build modular datatypes, modular functions and modular proofs from well-studied
%% DGP representations of fixed-points for different classes of functors.
%%
%% In particular, we consider polynomial functors like Schwaab and Siek, but also
%% the more expressive container types which are useful for modelling MTC's lambda
%% binders that are based on (parametric) higher-order abstract syntax.
%%
%% \item
%% Our approach avoids impredicativity in Coq and adequately encodes fixed-points.  It
%% achieves these properties by exploiting DGP approaches that capture only
%% strictly-positive functors.
%%
%% \item
%% We show how to obtain more reuse than MTC by
%% complementing modular definitions with generic definitions.
%%
%% \item
%% We show how to apply MTC's automatic construction of fixed-points for
%% datatypes, relations and proofs to the DGP setting
%% and thus improve over Schwaab and Siek's manual fixed-point construction.
%%
%% \end{itemize}
%%
%% \paragraph{Code and Notational Conventions}
%%
%% While all the code underlying this paper has been developed in Coq,
%% the paper adopts a terser syntax for its many code fragments.  For the
%% computational parts, this syntax exactly coincides with Haskell
%% syntax, while it is an extrapolation of Haskell syntax style for
%% propositions and proof concepts. The Coq code is available at
%% \url{https://github.ugent.be/skeuchel/gdtc}.
%%
%% %endif

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
