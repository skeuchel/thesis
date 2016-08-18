%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include macros.fmt

\section{Expression Problem}\label{sec:mod:expressionproblem}

\begin{figure}[t]
\fbox{\hspace{-5pt}
  \begin{minipage}{0.98\columnwidth}
    \begin{code}
      data Exp
        =  Lit Int
        |  Add e e
        |  BLit Bool
        |  If e e e
    \end{code}
  \end{minipage}
}
\caption{Monolithic arithmetic and boolean expressions}
\label{fig:mod:monolitichexpressions}
\end{figure}


%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../../mod"
%%% End:
