
Formal mechanization of programming language meta-theory is a big endeavor due
its unwieldy size, complexity and attention to detail. Therefore reuse is
crucial and indeed, the \textsc{PoplMark} challenge~\cite{poplmark} identifies
lack of \emph{component reuse} as one of several key obstacles of large-scale
mechanizations.


It is therefore desirable to apply established and \emph{principled software
  engineering methods} for reusability to programming language
mechanization. The objective of these software engineering methods is
\emph{modularity}: to build new software systems entirely from reusable
components, that have been written independently and can (potentially) be reused
in many different configurations for different applications.

A stumbling block for applying the modularity principle to programming language
formalization is that traditional inductive definitions and proofs are closed to
extension. It is therefore necessary to develop modular reasoning principles
first; in fact, \emph{modular induction principles}, because we want to stay as
close to established proof techniques as possible. Opening induction definitions
for extensibility is a manifestation of the \emph{expression
  problem}~\cite{expression-problem}.

This chapter covers background information on modular reasoning that forms the
basis for Chapter \ref{ch:modpreduniv} and \ref{ch:modmoneff}. In particular, we summarize techniques that are used
in the \emph{Meta-Theory \`a la Carte} (MTC) framework, an existing solution for
modular reasoning about programming languages in Coq, on which we
build. However, we limit ourselves to parts that are relevant to Chapters  \ref{ch:modpreduniv} and \ref{ch:modmoneff}
 and refer the reader to the original paper~\cite{mtc} for full details.

%% This is a manifestation of the expression problem that has been
%% addressed by the Meta-Theory \`a la Carte (MTC) framework in the context of
%% programming language meta-theory.


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
