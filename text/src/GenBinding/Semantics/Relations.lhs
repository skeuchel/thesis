%include lhs2TeX.fmt
%include polycode.fmt
%include Formatting.fmt
%include forall.fmt

%-------------------------------------------------------------------------------
\section{Relation Semantics}\label{sec:relationsemantics}

In this section we define the semantics of relations. A prerequisite is
interpretation of environment lookups. This the paramount boilerplate operation
on environments that we define generically in Section \ref{ssec:contextlookups}.
Premises of rules can contain rule binding specifications which we need to
interpret. They define the environment extensions for the corresponding premise.
In Section \ref{ssec:sem:rulebindspec} we show how to evaluate rule binding
specifications to concrete environment terms that represent the extensions.
Finally, Section \ref{ssec:sem:derivations} discusses the interpretation of
relations as derivation trees.


%-------------------------------------------------------------------------------
\subsection{Environment lookups}\label{ssec:contextlookups}

\begin{figure}[t]
  \centering
  \fbox{
    \begin{minipage}{0.95\columnwidth}
      \framebox{\mbox{|(n : overline u) inαE v|}} \\
      \[ \begin{array}{c}
         \inferrule* [right=\textsc{InHere}]
                     {\wellscopedsort{|domain|~v}{u_i}{S} \quad (\forall i) \\
                      K : E \to \alpha \to \ov{S} \to E
                     }
                     {|(0 : overline (weakenS u Iα)) inαE (K v (overline u))|}  \\ \\
         \inferrule* [right=\textsc{InThere}]
                     {|(n : overline u) inαE v| \\
                       K : E \to \alpha \to \ov{S} \to E \\
                       K' : E \to \beta \to \ov{T} \to E
                     }
                     {|(weakenα n Iβ : overline (weakenS u Iβ)) inαE (K' v (overline u'))|}
         \end{array}
      \]
    \end{minipage}
  }
  \caption{Environment lookup}
  \label{fig:environmentlookup}
\end{figure}

Lookup is a partial function. For that reason, we define it as a relation
|(n:overline u) inαE V| that witnesses that looking up the index |n| of
namespace |α| in the environment term |V| is valid and that |overline u| is the
associated data. Figure \ref{fig:environmentlookup} contains the definition.

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
data is also weakened to account for the new |β| binding.


%-------------------------------------------------------------------------------
\subsection{Rule Binding Specifications}\label{ssec:sem:rulebindspec}

\begin{figure}[t]
  \centering
  \fbox{
    \begin{minipage}{0.96\columnwidth}
      \begin{code}
      box (evalrbsE : rbs → u)

      evalrbsE ε                            =  0
      evalrbsE (rbs , b → overline sym)     =  K (evalrbsE rbs) ((overline (evalsymS bs sym ϑ)))
        where  (b : α) ∈ LENV
               K : E → α → overline T → E
               (symflatten LENV rbs bs)
      evalrbsE (rbs , f j)                  =  appendE (evalrbsE rbs) (ϑ (f,j))
      \end{code}
  \end{minipage}
  }
  \caption{Evaluation of rule binding specifications}
  \label{fig:rulebindspecevaluation}
\end{figure}

Similar to evaluation of binding specifications of sorts, we define the
semantics of rule binding specifications of relations as an evaluation. The
result in this case are environment terms instead of domains.

In case of a new single variable binding |b → overline sym| with a binding
variable |b| of namespace |α| we construct the environment term using the
constructor |K| of |E|, the result |(evalrbsE rbs)| of recursively evaluating
the prefix rule binding specification, and the evaluated associated data. The
associated data are expressions which need to be evaluated also. We get the
local scope |bs| for the evaluation of expressions by flattening the prefix of
the rule binding specification. For a function call on a judgement |j|, we look
up the corresponding environment term in the local value environment $\vartheta$
and append it to the result of recursively evaluating the prefix.

%-------------------------------------------------------------------------------
\subsection{Derivations}\label{ssec:sem:derivations}

Semantics of relations are derivation trees of judgements. However, for the
purpose of deriving boilerplate lemmas the interesting structure lies primarily
in the symbolic expressions used to define the rules of the relations. For
example, none of the elaborations for boilerplate lemmas make use of
representations of derivations. The lemmas need to induct over derivations but
we leave this aspect to the concrete implementation. Therefore, we only
introduce declaration heads as notation for use in subsequent sections.

%% but refer to the technical Appendix \ref{appendix:semantics} for details.

% The next ingredient of the semantics is an interpretation of lookup formulas
% $\{ g \cto \ov{S} \}$ of rules with implicit environment type $E$ as containment
% judgements
% $$\knotbox{\lookupenv{n}{\ov{v}}{E}{\alpha}{u_E}}$$
% \noindent on environment terms $u_E$. We can generically establish weakening and
% well-scopedness lemmas \cite{knotneedle} for containment.


% Rule binding specification are evaluated
% % $$\knotbox{\evalrbs{|_|}{|_|}{|_|}{|_|}: \rulebindspec \to E \to \vartheta \to u_E}$$
% to an environment term of type $E$ with respect to values $\vartheta$.


Relations are generically modelled by judgements of the form
$$\knotbox{\judg{u_E?}{R}{\ov{u_t}}{\ov{u_f}}}$$
where $u_E$ is an optional environment term and $\ov{u_t}$ are the sort indices
of the relations. Rather than interpreting binding functions as computations
over derivation trees, we include the results as indices $\ov{u_f}$ of the
judgements. To further simplify the presentation in the subsequent chapters, we
assume that all relations have an environment $E$ and ignore outputs of
functions, i.e. we only consider judgements of the form
$$\knotbox{\judgsimpl{u_E}{R}{\ov{u_t}}}.$$


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% End:

%% (add-to-list 'TeX-command-list '("Make" "make" TeX-run-compile nil t))
