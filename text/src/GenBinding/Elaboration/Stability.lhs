%include lhs2TeX.fmt
%include polycode.fmt
%include Formatting.fmt
%include forall.fmt

\section{Stability of binding specifications}\label{sec:elab:stability}

A crucial property of \Knot is the stability of binding specifications under
syntactic operations. This property enforces lexical scoping: shifting and
substituting variables in |t| does not change the scoping of bound variables.

We achieve this by ruling out functions over sorts with variables: function
evaluation can never reach variable cases and thus their results only depends on
the parts of the structure that are left unchanged by syntactic operations. This
includes, in particular the stabiltity of evaluation of binding specifications
functions.

\begin{lem}\label{lem:elab:funstability}
For all terms |t| of sort |S| and all |f : S → overline α| the
following holds:
\begin{enumerate}
  \item $\hsforall |∀ β, c.     evalfun f (shiftβ c t)   = evalfun f t|$
  \item $\hsforall |∀ β, s, c.  evalfun f (substβ c s t) = evalfun f t|$
\end{enumerate}
\begin{proof}
By induction over the structure of |t| and nested induction over the
right-hand side of |f|.
\end{proof}
\end{lem}

The nested induction of the lemma above deserves essentially proves that
evaluation of binding specifications is invariant under shifting and
substitution. This is a useful result of its own.

\begin{cor}\label{lem:elab:evalstability}
Let $bs$ be a binding specification and $\vartheta = \overline{t_i \mapsto
  u_i}^i$ a local value environment. For given cut-offs $\overline{h_i}^i$ and
substitutes $\overline{v_i}^i$ define the following value environments

\[ \begin{array}{lcl}
     \vartheta'(t_i)  & := & |shiftα|~h_i~u_i     \\
     \vartheta''(t_i) & := & |substα|~h_i~v_i~u_i \\
   \end{array}
\]

\begin{enumerate}
  \item $\hsforall |∀ bs.     evalbs bs ϑ'   = evalbs bs ϑ|$
  \item $\hsforall |∀ bs.     evalbs bs ϑ''  = evalbs bs ϑ|$
\end{enumerate}
\begin{proof}By induction over $bs$ and using Lemma \ref{lem:elab:funstability}
  for function calls.
\end{proof}
\end{cor}


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../Main"
%%% End:
