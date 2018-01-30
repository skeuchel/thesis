%include lhs2TeX.fmt
%include polycode.fmt
%include Formatting.fmt
%include forall.fmt

\subsection{Substitution}\label{ssec:elab:substitution}

Much of the reasoning is similar to shifting: for context-parametric regular
rules we need to commute substitution with symbolic evaluation, which is done by
elaboration to term equality witnesses. In the case of a homogenous
substitution, the lookup of a variable rule is replaced by a derivation tree of
the relation and in the case of a heterogeneous substitution, the lookup is
adapted and wrapped inside the variable rule again. Hence we only discuss the
problematic case of non-context parametric regular rules. As an example consider
the algorithmic transitivity rule of of \emph{$\SystemF$ with sub-typing}:
\[
\inferrule*[]
  {(\alpha <: \sigma) \in \Gamma \\
   \Gamma \vdash \sigma <: \tau
  }
  {\Gamma \vdash \alpha <: \tau
  }.
\]

In the inductive step of the type-variable substitution lemma, e.g. when
substitution a type-variable $\beta$ for $\sigma'$, we cannot apply the same
rule again, because in the case $\alpha = \beta$ it has been substituted.
However, we can substitute the lookup by a derivation and use the induction
hypothesis of the second premise, i.e. it suffices to show

\[
\inferrule*[]
  {\Gamma' \vdash [\beta \mapsto \sigma']\alpha <: [\beta \mapsto \sigma']\sigma) \\
   \Gamma' \vdash [\beta \mapsto \sigma']\sigma <: [\beta \mapsto \sigma']\tau
  }
  {\Gamma' \vdash [\beta \mapsto \sigma']\alpha <: [\beta \mapsto \sigma']\tau
  }
\]

where $\Gamma'$ is the resulting context after substitution. In other words, we
have spliced in derivations for lookups not only in the case of a variable
constructor, but also for lookups in non-context parametric rules. We can finish
the proof of the induction step, if we can show that the declarative sub-typing
rule is admissible:

\[
\inferrule*[]
  {\Gamma \vdash \rho <: \sigma \\
   \Gamma \vdash \sigma <: \tau \\
  }
  {\Gamma \vdash \rho <: \tau
  }.
\]

Unfortunately, the admissibility of this rule is a meta-theoretic property of
the sub-typing relation that has to be proved separately and that we cannot
establish automatically. As a consequence, for this sub-typing relation and
similar languages with non-context parametric rules we cannot establish the
substitution lemma generically.

However, the above gives us a recipe to automatically derive sufficient proof
obligations to establish the inductive step. Consider the substitution lemma for
namespace $\alpha$ of a relation $R$ and let $S$ be the sort for namespace
$\alpha$. For each non-context parametric rule of $R$, we derive a proof
obligation by replacing all occurrences of global meta-variables $\ov{g}$ of
namespace $\alpha$ with fresh sort meta-variables $\ov{s_g}$ of sort $S$ and
each lookup premise $\{g \cto \ov{\symbolicterm}\}$ with a judgement premise
$([\epsilon] R~(s_g,\ov{[g \mapsto s_g]\symbolicterm}))$. Note that $[g \mapsto
  s_g]$ denotes a substitution at the meta-level and not the object level or a
symbolic substitution. This substitution needs to ensure that well-scoping of
symbolic expression is not violated: each occurrence of $g$ at local scope
$\bindspec$ is in fact replaced by $(\symbolicweaken~s_g~bs)$. Global
meta-variables of other namespaces and lookups of other clauses are left
unchanged except for the meta-substitution $[g \mapsto s_g]$ in the lookup data.

% need to ensure
%
% We can fully derive  for relations that have the structure of
% free relative monads which we discuss in Section
% \ref{ssec:substitutionfree}. However, relations that do not fit this structure
% are quite common in practice. Deriving the substitution lemma for them is in
% general impossible. We therefore characterize proof obligations for these that
% are sufficient to prove the full substitution lemma.




%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% End:
