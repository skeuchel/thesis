%include lhs2TeX.fmt
%include polycode.fmt
%include Formatting.fmt
%include forall.fmt

%-------------------------------------------------------------------------------
\section{Relation Semantics}\label{sec:relationsemantics}

\subsection{Environment lookups}\label{ssec:contextlookups}

The paramount infrastructure operation on environments is the lookup of
variables and their associated data. Lookup is a partial function. For that
reason, we define it as a relation |(n:overline u) inα Γ| that witnesses that
looking up the index |n| of namespace |α| in the environment term |Γ| is valid
and that |overline u| is the associated data. Figure \ref{fig:environmentlookup}
contains the definition.

Rule \textsc{InHere} forms the base case where |n = 0|. In this case the
environment term needs to be a cons for namespace |α|. Note that well-scopedness
of the associated data is included as a premise. This reflects common practice
of annotating variable cases with with well-scopedness conditions. By moving it
into the lookup itself, we free the user from dealing with this obligation
explicitly. We need to |weaken| the result of the lookup to account for the
binding.

Rule \textsc{InThere} encodes the case that the lookup is not the last cons of
the environment. The rule handles both the homogeneous |α = β| and the
heterogeneous case |α ≠ β| by means of weakening the index |n|. The associated
data is also shifted to account for the new |β| binding.

\begin{figure}[t]
\begin{center}
\fbox{
  \begin{minipage}{0.95\columnwidth}
  \framebox{\mbox{|(n : overline u) inα Γ|}} \\
  \vspace{-7mm}
  \[ \begin{array}{c}
     \inferrule* [right=\textsc{InHere}]
                 {|domain Γ ⊢ u_i| \quad (\forall i)}
                 {|(0 : overline (weaken u Iα)) inα (Γ ► overline u)|}  \\
     \inferrule* [right=\textsc{InThere}]
                 {|(n : overline u) inα Γ|}
                 {|(weakenα n Iβ : overline (weaken u Iβ)) inα (Γ ►► overline v)|}
     \end{array}
  \]
  \end{minipage}
}
\end{center}
\caption{Environment lookup}
\label{fig:environmentlookup}
\end{figure}


\subsection{Derivations}

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
