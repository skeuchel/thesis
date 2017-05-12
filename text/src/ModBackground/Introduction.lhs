
Formal mechanization of programming language meta-theory is a big endeavor due
its unwieldy size, complexity and attention to detail. Therefore reuse is crucial and indeed, the
\textsc{PoplMark} challenge~\cite{poplmark} identifies lack of \emph{component reuse} as
one of several key obstacles of large-scale mechanizations. Unfortunately the
current practice to achieve reuse is to copy an existing formalization,
\emph{change the existing definitions} manually, integrate new features and to
subsequently \emph{patch up the proofs} to cater for the changes. This
unprincipled approach to reuse leaves much to be desired. First, editing and
patching the existing definitions breaks \emph{abstraction}, a core principle of
computer science. Ideally we would like to reuse existing code via an interface that
provides functionality (for programming) and properties (for reasoning). Second,
this approach does not encourage \emph{isolation} of new features from existing ones, which
hinders backporting improvements to the existing formalization.

It is therefore desirable to apply established and \emph{principled software
engineering methods} for reusability to programming language mechanization. The
objective of these software engineering methods is \emph{modularity}: to build
new software systems entirely from reusable components, that have been written
independently and can (potentially) be reused in many different configurations
for different applications. 

A stumbling block for applying the modularity principle to programming language
formalization is that traditional inductive definitions and proofs are closed to
extension. It is therefore necessary to develop modular reasoning principles
first; in fact, \emph{modular induction principles}, because we want to stay as
close to established proof techniques as possible. Opening induction
definitions for extensibility is a manifestation of the \emph{expression
problem}~\cite{expression-problem}.

%% This is a manifestation of the expression problem that has been
%% addressed by the Meta-Theory \`a la Carte (MTC) framework in the context of
%% programming language meta-theory.


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
