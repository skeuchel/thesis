%include lhs2TeX.fmt
%include polycode.fmt
%include Formatting.fmt
%include forall.fmt


\section{Shifting and Substitution}\label{sec:elab:shiftsubst}

The last semantic boilerplate lemmas that we consider in this chapter are
shifting and substitution lemmas of user-defined relations. For formal proofs we
can apply the methodology of this chapter: elaboration into a sound witness
language. The witness language in this case also observe term equalities similar
to Section \ref{sec:elab:interaction}. We do not present the final elaboration
but only present all the necessary ingredients to develop it. We first discuss
shifting lemmas in Section \ref{ssec:elab:shifting} and then substitution lemmas
in Section \ref{ssec:elab:substitution}.

\subsection{Shifting}\label{ssec:elab:shifting}
\newcommand{\shift}[3]{{\text{shift}_{#1}~{#2}~{#3}}}

As in the previous sections, we first discuss the necessary proof steps
semi-formally and subsequently sketch the formal proof elaboration for shifting
lemmas.

Shifting introduces a new binding in the environment of a relation and adapts
the relation indices by term-level shifting. In its most generic form the
insertion happens between two parts $u_1$ and $u_2$ of the environment. In this
case, term-level shifting is done using the domain of $u_2$ as cut-off. The
proof proceeds by induction on the derivation of a relation. For the inductive
step of each rule, be it a variable rule or a regular rule, we want to apply the
same rule again. This may require massaging the proof goal with commutation
lemmas of shifting and substitution, i.e. we have to push the global shifting
into local weakenings and local substitutions to recreate the symbolic structure
of the rule.

More specifically, for a rule with conclusion $R~\ov{\symbolicterm}$ and values
$\vartheta$ the goal of the induction step is to show
\[ R~\ov{\shift{\alpha}{c}{\evalsym{\epsilon}{\symbolicterm}{\vartheta}}}.
\]

To use rule $r$ again, we need to match the same symbolic structure
$\ov{\symbolicterm}$, i.e. we have to find $\vartheta'$ such that the following
holds
\begin{equation}\label{eq:shifteval}
\ov{\shift{\alpha}{c}{\evalsym{\epsilon}{\symbolicterm}{\vartheta}}} =
\ov{\evalsym{\epsilon}{\symbolicterm}{\vartheta'}}.
\end{equation}

\noindent This is just
$\vartheta' = \ov{(r \mapsto \shift{\alpha}{c}{(\vartheta~r)})},\ov{(t \mapsto
  \shift{\alpha}{(c+\evalbs{\bindspec_t}{\vartheta})}{(\vartheta~t)})}$
\noindent or in other words: shifting commutes with symbolic evaluation.

Similar to Section \ref{sec:elab:wellscopedness}, we can give a formal
syntax-directed elaboration for equation (\ref{eq:shifteval}) from symbolic
expressions into a domain-specific witness language of term equalities. This is
an extension of the language of Section \ref{sec:elab:interaction} that
additionally has primitives for the commutation lemmas. After using rule $r$ we
are still left with it's premises as proof goals. In case of a judgement, we
need to apply equality (\ref{eq:shifteval}) in the opposite direction.

%% This has a lot of similarity to equivariance proofs of functions in nominal
%% representations that commute function evaluation with permutations $\pi$ on
%% atoms:
%% $$ f(\pi(t)) =_\alpha \pi~(f(t)))$$

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% End:
