\section{Modular definitions}

Modularity is one of the holy grails of software engineering. The dream is to be
able build new software systems entirely from reusable components, that have
been written independently and can (potentially) be reused in many different
configurations for different applications. Increasingly more modularity demands
are being made: without modifying components, it must be possible to augment or
modify their behavior. At the same time, unprincipled copy-\&-paste approaches,
even performed by automated tools, are not acceptable. Components must have a
meaning beyond their textual form and independently of a particular composition;
they must support \emph{modular reasoning}. \sk{Discuss statically-typed
  components as one form of modular reasoning to ensure absence of type errors.}

\subsection{Modular programming languages}
\sk{This should first talk about modularity in the specification of programming
  language features and the move on to discuss modularity in the context of
  metatheory.}
The \textsc{PoplMark} challenge \cite{poplmark} identifies
% \emph{variable binding}, \emph{complex inductions},
% \emph{experimentation} and
\emph{component reuse} as one of several key issues of formal mechanization of
programming language meta-theory. Reuse is crucial because formalizations have
high costs. Unfortunately the current practice to achieve reuse is to copy an
existing formalization and to change the existing definitions manually to
integrate new features and to subsequently \emph{patch up the proofs} to cater
for the changes.

Building modular reusable components is a key issue in reducing these costs. A
stumbling block for reuse is that inductive definitions and proofs are closed to
extension. This is a manifestation of the expression problem.

%% This is a manifestation of the expression problem that has been
%% addressed by the Meta-Theory \`a la Carte (MTC) framework in the context of
%% programming language meta-theory.


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
