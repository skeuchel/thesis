%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include Formatting.fmt
%include macros.fmt

%format Sigma = "\Varid{\Sigma}"
%format mu = "\sigma''"
%format sigma = "\Varid{\sigma}"

\begin{figure*}[t]
  \centering
  \fbox{\begin{minipage}[t]{0.981391\columnwidth}

  \begin{subfigure}[t]{\linewidth}
    \begin{gather*}
      \forall e, t, \Sigma, \sigma.
          \left\{\begin{array}{c}
          | typeof e == return t | \\
          \Sigma \vdash \sigma
          \end{array}\right\} \rightarrow \\
        \exists v, \Sigma', \sigma'.
         \left\{\begin{array}{c}
         |put sigma >> eval e == put mu >> return v| \\
         \Sigma' \supseteq \Sigma \\
         \Sigma' \vdash v : t \\
         \Sigma' \vdash \sigma'
         \end{array}\right\}
      %%\tag{\textsc{LSound}$_S$}
      \label{thm:LSoundS}
    \end{gather*}
  \end{subfigure}
  \hrule
  \begin{subfigure}[t]{\linewidth}
    \begin{gather*}
      \forall e, t. |typeof e == return t| \rightarrow \\
        (\exists v. |eval e == return v| \wedge \vdash v : t) \vee
        (\exists x. |eval e == throw x|)
      %%\tag{\textsc{LSound}$_E$}
      \label{thm:SoundE}
    \end{gather*}
  \end{subfigure}
  \hrule
  \begin{subfigure}[t]{\linewidth}
    \begin{gather*}
      \forall e, t, \Sigma, \sigma.
          \left\{\begin{array}{c}
          | typeof e == return t | \\
          \Sigma \vdash \sigma
          \end{array}\right\}
       \rightarrow \\
        \exists v, \Sigma', \sigma'.
         \left\{\begin{array}{c}
         |put sigma >> eval e == put mu >> return v| \\
         \Sigma' \supseteq \Sigma \\
         \Sigma' \vdash v : t \\
         \Sigma' \vdash \sigma'
         \end{array}\right\} \\
      \vee \\
        \exists x.
         |put sigma >> eval e == throw x|
      %%\tag{\textsc{LSound}$_\mathit{ES}$}
      \label{thm:SoundES}
    \end{gather*}
  \end{subfigure}

  \end{minipage}}
  \vspace{-2mm}
  \caption{Key classes, definitions and laws from \Name's monadic library.}
  \label{fig:mod:effecttheorems}
\end{figure*}
