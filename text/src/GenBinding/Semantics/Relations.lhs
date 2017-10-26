%include lhs2TeX.fmt
%include polycode.fmt
%include Formatting.fmt
%include forall.fmt

%-------------------------------------------------------------------------------
\section{Relation Semantics}\label{sec:relationsemantics}

Semantics of relations are derivation trees of judgements. However, for the
purpose of deriving boilerplate lemmas the interesting structure lies primarily
in the symbolic expressions used to define the rules of the
relations. Therefore, we only introduce declaration heads as notation for use in
subsequent sections, but refer to the technical Appendix
\ref{appendix:semantics} for details.

The next ingredient of the semantics is an interpretation of lookup formulas
$\{ g \cto \ov{S} \}$ of rules with implicit environment type $E$ as containment
judgements
$$\knotbox{\lookupenv{n}{\ov{v}}{E}{\alpha}{u_E}}$$
\noindent on environment terms $u_E$. We can generically establish weakening and
well-scopedness lemmas \cite{knotneedle} for containment. Rule binding specification are evaluated
% $$\knotbox{\evalrbs{|_|}{|_|}{|_|}{|_|}: \rulebindspec \to E \to \vartheta \to u_E}$$
to an environment term of type $E$ with respect to values $\vartheta$. Finally,
relations are generically modelled by judgements of the form
$$\knotbox{\judg{u_E?}{R}{\ov{u_t}}{\ov{u_f}}}$$
where $u_E$ is an optional environment term and $\ov{u_t}$ are the
sort indices of the relations. Rather than interpreting binding functions as
computations over derivation trees, we include the results as indices
$\ov{u_f}$ of the judgements. To further simplify the presentation, we assume
that all relations have an environment $E$ and ignore outputs of functions, i.e.
we only consider judgements of the form
$$\knotbox{\judgsimpl{u_E}{R}{\ov{u_t}}}.$$


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% End:

%% (add-to-list 'TeX-command-list '("Make" "make" TeX-run-compile nil t))
