
Formal mechanization of programming language meta-theory is a big endeavor due
the high implementation costs. Therefore reuse is crucial and indeed, the
\textsc{PoplMark} challenge~\cite{poplmark} identifies \emph{component reuse} as
one of several key issues of large-scale mechanizations. Unfortunately the
current practice to achieve reuse is to copy an existing formalization,
\emph{change the existing definitions} manually, integrate new features and to
subsequently \emph{patch up the proofs} to cater for the changes. This
unprincipled approach to reuse leaves much to be desired. First, editing and
patching the existing definitions breaks \emph{abstraction}, a core principle of
computer science. Ideally we would reuse existing code via an interface that
provides functionality (for programming) and behavior (for reasoning). Second,
this approach demotes \emph{isolation} of new features from existing ones, which
hinders backporting any improvements to the existing functionality within the
new formalization to the existing formalization.

It is therefore desirable to apply established and \emph{principled software
engineering methods} for reusability. One of the holy grails of reuse in
software engineering is \emph{modularity}. The dream is to be
able to build new software systems entirely from reusable components, that have
been written independently and can (potentially) be reused in many different
configurations for different applications. Because confidence and correctness
requirements in software systems rise, increasingly more modularity demands are
being made: components must have a meaning beyond a particular composition; they
must also support \emph{modular reasoning}.

A stumbling block for applying the modularity principle to programming language
formalization is that traditional inductive definitions and proofs are closed to
extension. It is therefore necessary to develop modular reasoning principles
first; in fact, \emph{modular induction principles}, because we want to stay as
close to established proof techniques as possible.  Opening induction
definitions for extensibility is a manifestation of the \emph{expression
problem}\cite{expression-problem}.

%% This is a manifestation of the expression problem that has been
%% addressed by the Meta-Theory \`a la Carte (MTC) framework in the context of
%% programming language meta-theory.


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
