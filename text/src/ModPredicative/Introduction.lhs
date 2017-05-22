
The \emph{Datatypes \`a la Carte} (DTC) approach is a Haskell solution for
modular programming in Haskell. However, as outlined in Section
\ref{sec:mod:reasoningalacarte} the transition to a proof-assistant, for modular
reasoning, comes with major hurdles. DTC relies on a general fixed point
combinator to define fixed points for arbitrary functors and uses a generic fold
operation that is not structurally recursive. To keep logical consistency Coq
applies conservative restrictions and rejects both: a) DTC's type level
fixed-points because it cannot see that the definition is always
strictly-positive, and b) DTC's fold operator because it cannot determine
termination automatically.

Meta-Theory \`a la Carte (MTC) \cite{mtc} solves both problems by using
extensible Church encodings. However, MTC's use of Church encodings leaves much
to be desired. This chapter discusses the problems that Church encodings bring
with them in terms of reasoning and presents an alternative implementation of
MTC based on a predicative universe of strictly-positive functors instead of
Church encodings. The universe admits generic definitions of folds and proper
strong induction that fulfill Coq's conservative restrictions.

\paragraph{Outline} We first discuss the drawbacks of using Church
encodings in Section \ref{sec:modpred:motivation} to motivate their replacement.
Section \ref{sec:modpred:strictlypositivefunctors} presents the approach to
modularized induction for our new representation. This results in a different
user-facing interface than MTC's for modular reasoning. In particular, the
representation of \emph{proof algebras} is significantly different from the one
used with MTC's weak induction principle and closer to standard structural
inductive reasoning. We discuss the universe of container types in Section
\ref{sec:mod:containers} which is modular and which admits datatype-generic
generic definitions of folds and induction that we use to generically
instantiate our interface. The universe of containers is very large and admits
only a small number of generic functions. As a complement, we discuss the
universe of polynomial functors in Section \ref{sec:mod:polynomial}, which
admits more generic functions like generic equality, and show how to embed it in
the universe of containers which provides us with additional reuse
opportunities. We compare the universe basec solution directly with MTC's Church
encoding solution in Section \ref{sec:mod:casestudy} using a port of MTC's case
study.

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
