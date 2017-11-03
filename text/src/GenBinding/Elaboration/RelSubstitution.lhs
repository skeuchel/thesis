

\paragraph{Substitution}\label{sec:substitution}

Much of the reasoning is similar to shifting: we need to commute
substitution with symbolic evaluation. Hence we only discuss the problematic
case of non-context parametric rules. As an example consider the algorithmic
transitivity rule of of \emph{$\SystemF$ with subtyping}:
\vspace{-3mm}
$$
\inferrule*[]
  {(\alpha <: \sigma) \in \Gamma \\
   \Gamma \vdash \sigma <: \tau
  }
  {\Gamma \vdash \alpha <: \tau
  }
$$

In the inductive step of the type-variable substitution lemma we cannot apply
the same rule again, because $\alpha$ may have been substituted. In this
and similar languages we cannot establish the substitution lemma
generically. However, we can make progress if we can show that declarative
subtyping holds
$$
\inferrule*[]
  {\Gamma \vdash \rho <: \sigma \\
   \Gamma \vdash \sigma <: \tau \\
  }
  {\Gamma \vdash \rho <: \tau
  }
$$

This gives us a recipe to generically state sufficient proof obligations to
establish the inductive step for non-context parametric rules. Consider substituting
an environment clause $(K_E : \alpha \to \ov{T} : R) \in E$ and sort variable
constructor $K_S : \alpha \to S$. We replace all occurrences of global
meta-variables $\ov{g}$ of namespace $\alpha$ with fresh sort meta-variables
$\ov{s_g}$ of sort $S$ and each lookup premise $\{g \cto \ov{\symbolicterm}\}$
with a judgement premise $([\epsilon] R~(s_g,\ov{[g \mapsto
s_g]\symbolicterm}))$. Note that $[g \mapsto s_g]$ denotes a substitution at the
meta-level and not the object level or a symbolic substitution. This
substitution needs to ensure that well-scoping of symbolic expression is not
violated. Each occurrence of $g$ at local scope $\bindspec$ is in fact replaced
by $(\symbolicweaken~s_g~bs)$. Global meta-variables of other namespaces and
lookups of other clauses are left unchanged except for the meta-substitution $[g
\mapsto s_g]$ in the lookup data.

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
