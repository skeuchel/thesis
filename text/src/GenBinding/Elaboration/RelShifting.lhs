%include lhs2TeX.fmt
%include polycode.fmt
%include Formatting.fmt
%include forall.fmt


\section{Shifting and Substitution}\label{sec:elab:shifting}

Finally, we provide generic lemmas for shifting and substitution. 

\paragraph{Shifting}
As in the
previous section, we first present the generic form, then discuss the necessary
reasoning in the inductive steps and briefly address proof term
elaboration. Shifting introduces a new binding in the environment of a relation
and adapts the relation indices by term-level shifting. In its most generic form
the insertion happens between two parts $u_1$ and $u_2$
of the environment:
$$
\inferrule*[]
  {(K : \alpha \cto \ov{T}) \in E \\
   u_1 + u_2 \models_R \ov{u} \\
   \ov{\domain{u_1} \vdash_T v} \\
   c := \domain{u_2} \\
  }
  {K~u_1~\ov{v} + \sh{\alpha}{0}{u_2} \models_R \ov{\sh{\alpha}{c}{u}}
  }
$$

In this case, term-level shifting is done using the domain of $u_2$ as cutoff.
The proof proceeds by induction on the derivation of
$u_1 + u_2 \models_R \ov{u}$. For the inductive step of each of the rules we
want to apply the same rule again which may require massaging the proof goal
with commutation lemmas of shifting and substitution. More specifically, for a
rule with conclusion $R~\ov{\symbolicterm}$ and values $\vartheta$ the goal is
to show
$$K~u_1~\ov{v} + \sh{\alpha}{0}{u_2} \models_R \ov{\sh{\alpha}{c}{\evalsym{\epsilon}{\symbolicterm}{\vartheta}}}$$

To use rule $r$ again, we need to match the same symbolic
structure $\ov{\symbolicterm}$, i.e. we have to find $\vartheta'$ such that the
following holds
\begin{equation}\label{eq:shifteval}
\ov{sh~c~\evalsym{\epsilon}{\symbolicterm}{\vartheta}} =
\ov{\evalsym{\epsilon}{\symbolicterm}{\vartheta'}}.
\end{equation}

\noindent This is just
$\vartheta' = \ov{(r \mapsto sh~c~(\vartheta~r))},\ov{(t \mapsto
  sh~(c+\evalbs{\bindspec_t}{\vartheta})~(\vartheta~t))}$
\noindent or in other words: shifting commutes with symbolic evaluation.

Similar to Section \ref{sec:wellscopedness} we can give a syntax-directed
elaboration of symbolic expressions to equality proof terms that witness
equality (\ref{eq:shifteval}). After using rule $r$ we are still left with it's
premises as proof goals. In case of a judgement, we need to apply equality
(\ref{eq:shifteval}) in the opposite direction. The shifting lemma for environment
lookups has already been generically established in \cite{knotneedle}.


%% This has a lot of similarity to equivariance proofs of functions in nominal
%% representations that commute function evaluation with permutations $\pi$ on
%% atoms:
%% $$ f(\pi(t)) =_\alpha \pi~(f(t)))$$

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% End:
